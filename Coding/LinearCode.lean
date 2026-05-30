import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Linear codes, parity-check matrices, syndromes  (Phase 1b)
-- ============================================================================
--
-- A linear code is the kernel of a parity-check matrix H.  The SYNDROME of a
-- word x is σ = H·x; codewords are exactly the words of syndrome 0.  The
-- hardness Octra relies on is SYNDROME DECODING: given H and σ, recover a
-- low-Hamming-weight error e with H·e = σ.  Here H will be the hypergraph
-- incidence matrix (see Coding/Syndrome.lean); this file is the abstract layer.

namespace Octra.Coding

open Matrix

variable {m n : Type*} [Fintype n]

/-- The syndrome of `x` under parity-check matrix `H`: `σ = H·x`. -/
def syndrome {R : Type*} [Semiring R] (H : Matrix m n R) (x : n → R) : m → R :=
  H.mulVec x

/-- The syndrome map is additive (it is `𝔽`-linear). -/
theorem syndrome_add {R : Type*} [Semiring R] (H : Matrix m n R) (x y : n → R) :
    syndrome H (x + y) = syndrome H x + syndrome H y := by
  simp only [syndrome, Matrix.mulVec_add]

/-- Hamming weight: the number of nonzero coordinates of `x`. -/
def hammingWeight {R : Type*} [Zero R] [DecidableEq R] (x : n → R) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- `e` solves the syndrome-decoding instance `(H, σ, w)` when it has the right
    syndrome and weight at most `w`.  Finding such `e` is the hard problem. -/
def IsSyndromeDecodingSolution {R : Type*} [Semiring R] [DecidableEq R]
    (H : Matrix m n R) (σ : m → R) (w : ℕ) (e : n → R) : Prop :=
  syndrome H e = σ ∧ hammingWeight e ≤ w

end Octra.Coding
