import Crypto.Field127
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

-- ============================================================================
-- HFHE — ciphertext DAG, decryption, encryption  (Phase 3, KEYSTONE #2 setup)
-- ============================================================================
--
-- Grounded in Crypto/HFHE/SPEC.md (extracted from pvac_hfhe_cpp).  The scheme is
-- NOT a noisy LWE/LPN FHE: decryption is an EXACT identity over a field 𝔽
-- (intended 𝔽ₚ, p = 2^127−1 — see Crypto/Field127.lean).  A ciphertext is a DAG
-- of layers + edges; each edge contributes `±w·g^idx`; a per-layer secret mask
-- `R` is divided out.  The "noise" cancels identically, so there is NO
-- decryption noise budget.
--
-- The algebra below holds over ANY field; the secret mask `R` is an abstract
-- parameter (its LPN/PRF derivation is the separate, axiomatized hardness layer).

namespace Octra.HFHE

variable {S : ℕ} {F : Type*} [Field F]

/-- Carrier sign: `SGN_P ↦ +1`, `SGN_M ↦ −1` (C++ `sgn_val`). -/
def sgn : Bool → F
  | true  => 1
  | false => -1

/-- A DAG layer.  `base` is a fresh masked layer (its mask is a PRF/LPN output);
    `prod` is created by homomorphic multiply, and its mask is the product of the
    two parents' masks (`R(prod a b) = R a · R b`). -/
inductive Layer
  | base (seed : ℕ)
  | prod (pa pb : ℕ)
deriving Repr, DecidableEq

/-- A ciphertext edge: contributes `±w · g^idx`, attributed to layer `layer`.
    (The C++ `Edge` also carries a bit-selector `s`; it is a DECOY that
    decryption never reads, so it is omitted from the decryption-relevant model.) -/
structure Edge (S : ℕ) (F : Type*) where
  layer : ℕ
  idx   : ℕ
  sign  : Bool
  w     : Fin S → F

/-- A ciphertext: a DAG (`layers`) of edges plus a constant term `c0`, over `S`
    SIMD slots.  Decryption only needs the per-layer mask `R`; `layers` records
    provenance (and drives how `R` is computed). -/
structure Cipher (S : ℕ) (F : Type*) where
  layers : List Layer
  edges  : List (Edge S F)
  c0     : Fin S → F

/-- Decryption under carrier `g` and an abstract per-layer mask `R`:
      `v[j] = c0[j] + Σ_e sign(e)·w[j]·g^idx·R(layer)⁻¹`.
    `R l j` is the (nonzero) mask of layer `l` at slot `j`. -/
def decrypt (g : F) (R : ℕ → Fin S → F) (c : Cipher S F) (j : Fin S) : F :=
  c.c0 j + (c.edges.map fun e => sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹).sum

/-- Homomorphic addition (correctness proved in Homomorphism.lean): concatenate
    layers and edges, add the constant terms. -/
def cAdd (a b : Cipher S F) : Cipher S F where
  layers := a.layers ++ b.layers
  edges  := a.edges ++ b.edges
  c0     := fun j => a.c0 j + b.c0 j

/-- Minimal one-edge encryption: encode `v` in a single signal edge at carrier
    position `idx`, masked by `R 0`.  The real `synth` uses K=8 signal edges plus
    weight-2/3 noise tuples; this is the noise-free K=1 special case — enough to
    exhibit EXACT correctness end-to-end (see Correctness.lean). -/
def encrypt1 (g : F) (R : ℕ → Fin S → F) (idx : ℕ) (v : Fin S → F) : Cipher S F where
  layers := [Layer.base 0]
  edges  := [{ layer := 0, idx := idx, sign := true, w := fun j => v j * (g ^ idx)⁻¹ * R 0 j }]
  c0     := fun _ => 0

-- The intended field instance is 𝔽_p, p = 2¹²⁷−1; the development is generic.
example : Field Octra.Field127.F := inferInstance

end Octra.HFHE
