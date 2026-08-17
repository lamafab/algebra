import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

-- ============================================================================
-- McEliece: encryption from an error-correcting code
-- ============================================================================
--
-- McEliece hides a decodable linear code inside a random-looking one.
-- A binary [n, k, t] code encodes k-bit messages as n-bit codewords via a
-- generator matrix G (k×n over 𝔽₂) and corrects up to t errors. The scheme:
--
--   keygen    secret: invertible S (k×k), generator G, permutation P (n×n)
--             public: Ĝ = S·G·P, generator of a scrambled equivalent code
--   encrypt   c = m·Ĝ + e,   e random of Hamming weight ≤ t
--   decrypt   c·P⁻¹ = (m·S)·G + e·P⁻¹;  e·P⁻¹ still has weight ≤ t, so the
--             secret decoder recovers m·S, and multiplying by S⁻¹ gives m
--
-- Two facts make this work, and both are proved here:
--
--   §1  permuting coordinates preserves Hamming weight, so the error stays
--       within the decoder's budget after the P⁻¹ step
--   §3  decryption correctness is pure linear algebra once a decoder for
--       the secret code is given (the decoder enters as a hypothesis)
--
-- What is **not** proved: that Ĝ hides the structure of G. That is the McEliece
-- assumption (a scrambled Goppa code looks like a random code, and decoding
-- a random linear code is hard), not algebra.
--
-- §4 instantiates everything on the [7,4,3] Hamming code; the theory of that
-- code is developed in Algebra/Code/Hamming.lean.

namespace McEliece

open Matrix

-- ============================================================================
-- Section 1: Hamming weight and permutations
-- ============================================================================

/-- Hamming weight of a binary vector: the number of nonzero coordinates. -/
def weight {n : ℕ} (v : Fin n → ZMod 2) : ℕ := ∑ i, (if v i = 0 then 0 else 1)

-- Permuting coordinates does not change the weight.
theorem weight_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    weight (v ∘ σ) = weight v := by
  unfold weight
  exact Equiv.sum_comp σ (fun l => if v l = 0 then (0 : ℕ) else 1)

-- ============================================================================
-- Section 2: Permutation matrices
-- ============================================================================
--
-- A permutation σ of the coordinates acts on row vectors from the right:
-- `v ᵥ* permMatrix σ = v ∘ σ⁻¹`. The inverse of a permutation matrix is the
-- matrix of the inverse permutation.

/-- The permutation matrix of `σ`: entry (i, j) is 1 iff σ i = j. -/
def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  (1 : Matrix (Fin n) (Fin n) (ZMod 2)).submatrix σ id

theorem vecMul_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    v ᵥ* permMatrix σ = v ∘ σ.symm := by
  ext j
  simp only [vecMul, dotProduct, permMatrix, submatrix_apply, one_apply, id_eq]
  rw [Finset.sum_eq_single (σ.symm j) _ (fun h => (h (Finset.mem_univ _)).elim)]
  · rw [Equiv.apply_symm_apply, if_pos rfl, mul_one]
    rfl
  · intro i _ hi
    rw [if_neg (mt (Equiv.apply_eq_iff_eq_symm_apply σ).mp hi), mul_zero]

theorem permMatrix_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permMatrix σ * permMatrix τ = permMatrix (σ.trans τ) := by
  ext i j
  simp only [mul_apply, permMatrix, submatrix_apply, one_apply, id_eq]
  rw [Finset.sum_eq_single (σ i) _ (fun h => (h (Finset.mem_univ _)).elim)]
  · rw [if_pos rfl, one_mul, Equiv.trans_apply]
  · intro l _ hl
    rw [if_neg (Ne.symm hl), zero_mul]

theorem permMatrix_refl {n : ℕ} : permMatrix (Equiv.refl (Fin n)) = 1 :=
  Matrix.submatrix_id_id 1

-- The decryption factor P⁻¹ is a permutation matrix again, and P·P⁻¹ = 1.
theorem permMatrix_mul_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permMatrix σ * permMatrix σ.symm = 1 := by
  rw [permMatrix_mul, Equiv.self_trans_symm, permMatrix_refl]

-- ============================================================================
-- Section 3: The scheme and its correctness
-- ============================================================================

section Abstract

variable {k n t : ℕ}
  (S Sinv : Matrix (Fin k) (Fin k) (ZMod 2))
  (G : Matrix (Fin k) (Fin n) (ZMod 2))
  (σ : Equiv.Perm (Fin n))

/-- Encryption: encode with the public generator `S * G * P`, then add a
random error of weight at most `t`. -/
def encrypt (m : Fin k → ZMod 2) (e : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  m ᵥ* (S * G * permMatrix σ) + e

/-- Decryption: undo the permutation, decode with the secret code's decoder,
then undo the scrambling `S`. -/
def decrypt (decode : (Fin n → ZMod 2) → Fin k → ZMod 2) (c : Fin n → ZMod 2) :
    Fin k → ZMod 2 :=
  decode (c ᵥ* permMatrix σ.symm) ᵥ* Sinv

-- Correctness: given a decoder for the secret code that tolerates errors of
-- weight ≤ t, decryption recovers the message. The decoder hypothesis does
-- all the coding theory; what remains is one chain of matrix identities.
--
--   decrypt (encrypt m e)
--   = decode ((m·(S·G·P) + e) · P⁻¹) · S⁻¹        unfold decrypt, encrypt
--   = decode (m·S·G·(P·P⁻¹) + e·P⁻¹) · S⁻¹        add_vecMul, vecMul_vecMul
--   = decode (m·S·G + e·P⁻¹) · S⁻¹                permMatrix_mul_symm
--   = (m·S) · S⁻¹                                 hdecode, weight_comp
--   = m                                           hS, vecMul_one
theorem decrypt_correct
    (decode : (Fin n → ZMod 2) → Fin k → ZMod 2)
    (hS : S * Sinv = 1)
    (hdecode : ∀ x e, weight e ≤ t → decode (x ᵥ* G + e) = x)
    (m : Fin k → ZMod 2)
    (e : Fin n → ZMod 2)
    (he : weight e ≤ t)
  :
    decrypt Sinv σ decode (encrypt S G σ m e) = m := by
  -- The error after undoing P is a permutation of e, so still small.
  have hw : weight (e ∘ σ) ≤ t := by rwa [weight_comp]
  unfold decrypt encrypt
  rw [add_vecMul, vecMul_vecMul, vecMul_permMatrix, Equiv.symm_symm,
    Matrix.mul_assoc (S * G), permMatrix_mul_symm, Matrix.mul_one, ← vecMul_vecMul,
    hdecode _ _ hw, vecMul_vecMul, hS, vecMul_one]

end Abstract

end McEliece

-- ============================================================================
-- Section 4: A concrete instance on the [7,4,3] Hamming code
-- ============================================================================
--
-- The code theory is developed in Algebra/Code/Hamming.lean; here we repeat
-- just what the scheme needs (generator, parity-check matrix, syndrome
-- decoder) to wire it into the McEliece scheme. Correctness is checked
-- exhaustively by native_decide.

namespace McEliece.Example

open Matrix McEliece

/-- Generator of the [7,4,3] Hamming code in systematic form [I₄ | A]. -/
def G : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 0, 1]

/-- Parity-check matrix H = [Aᵀ | I₃]. -/
def H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0, 0;
     1, 1, 1, 0, 0, 1, 0;
     0, 1, 1, 1, 0, 0, 1]

/-- The syndrome of a received word. -/
def syndrome (w : Fin 7 → ZMod 2) : Fin 3 → ZMod 2 := w ᵥ* Hᵀ

/-- Syndrome decoding: if the syndrome matches column j of H, flip bit j;
then read off the first 4 (systematic) coordinates. -/
def decode (w : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 :=
  let w' := match (List.finRange 7).find? (fun j => (fun i => H i j) = syndrome w) with
    | none => w
    | some j => Function.update w j (w j + 1)
  fun i => w' (Fin.castLE (by decide) i)

/-- Scrambling matrix (secret), unitriangular hence invertible over 𝔽₂. -/
def S : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 1;
     0, 1, 1, 0;
     0, 0, 1, 1;
     0, 0, 0, 1]

/-- Its inverse. -/
def Sinv : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 1, 0;
     0, 1, 1, 1;
     0, 0, 1, 1;
     0, 0, 0, 1]

example : S * Sinv = 1 := by native_decide
example : Sinv * S = 1 := by native_decide

/-- Coordinate permutation (secret): the cyclic rotation of the 7 positions. -/
def σ : Equiv.Perm (Fin 7) := finRotate 7

/-- The public key: the scrambled generator Ĝ = S·G·P. -/
def pubG : Matrix (Fin 4) (Fin 7) (ZMod 2) := S * G * permMatrix σ

/-- Encrypt with the public key, as an outsider would. -/
def enc (m : Fin 4 → ZMod 2) (e : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  m ᵥ* pubG + e

/-- Decrypt with the secret S⁻¹, P⁻¹ and the syndrome decoder. -/
def dec (c : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 :=
  decrypt Sinv σ decode c

-- Round trip: the syndrome decoder corrects any single error, so the full
-- McEliece decryption recovers the original message.
theorem dec_enc (m : Fin 4 → ZMod 2) (e : Fin 7 → ZMod 2) (he : weight e ≤ 1) :
    dec (enc m e) = m := by
  have hdecode : ∀ (x : Fin 4 → ZMod 2) (e : Fin 7 → ZMod 2), weight e ≤ 1 → decode (x ᵥ* G + e) = x := by
    intro x e he
    revert x e
    native_decide
  exact decrypt_correct S Sinv G σ decode (by native_decide) hdecode m e he

end McEliece.Example
