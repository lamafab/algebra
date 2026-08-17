import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

open Polynomial
open MvPolynomial
open Finset

noncomputable section

-- ============================================================================
-- Reed-Solomon and Reed-Muller codes over binary fields
-- ============================================================================
--
-- Reed-Solomon (RS) codes evaluate univariate polynomials of bounded degree
-- on a finite subset of GF(2ᵏ). For binary FRI the evaluation domain is
-- typically an affine subspace L ⊆ GF(2ᵏ) (an 𝔽₂-coset of a linear subspace),
-- so that folding (via the trace map) halves the dimension each round.
--
-- TODO: FRI => Fast Reed-Solomon Interactive
--
-- Reed-Muller (RM) codes evaluate multivariate polynomials of bounded total
-- degree on the entire boolean hypercube 𝔽₂ᵐ. They are the natural codes
-- for multilinear extensions and sumcheck.
--
-- Prerequisites: BinaryFields.lean for GF(2ᵏ); Multilinear.lean for the
-- hypercube and MLE.
--
--   §1  Reed-Solomon codes over GF(2ᵏ)
--   §2  Reed-Muller codes over 𝔽₂
-- ============================================================================

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

-- ============================================================================
-- Section 1: Reed-Solomon codes over GF(2ᵏ)
-- ============================================================================
--
-- Let L ⊆ GF(2ᵏ) be a finite subset (typically an affine subspace over 𝔽₂).
-- The RS code RS[L, d] encodes a polynomial p ∈ GF(2ᵏ)[X] of degree < d as
-- the vector (p(α))_{α∈L} ∈ (GF(2ᵏ))^L.
--
-- Because a nonzero polynomial of degree < d has at most d−1 roots in any
-- field, two distinct such polynomials agree on at most d−1 points of L.
-- Therefore RS[L, d] has minimum distance |L| − d + 1. The injectivity
-- theorem below is the case where the number of agreeing points is |L|;
-- the min-distance bound sharpens it.
--
-- TODO: Worth referencing `Algebra/Ring/RootsInterpolation.lean`

section ReedSolomon
variable {k d : ℕ}

/-- The evaluation vector of a univariate polynomial over GF(2ᵏ) on a finite
set L. -/
def rsEncode (L : Finset (GaloisField 2 k)) (p : Polynomial (GaloisField 2 k)) :
    L → GaloisField 2 k :=
  fun α => p.eval (α : GaloisField 2 k)

/-- The RS code over GF(2ᵏ) of degree bound d evaluated on a set L. -/
def rsCode (L : Finset (GaloisField 2 k)) (d : ℕ) : Set (L → GaloisField 2 k) :=
  rsEncode L '' {p : Polynomial (GaloisField 2 k) | p.natDegree < d}

/-- The encoding is injective when the degree bound does not exceed |L|.
Two distinct polynomials of degree < d cannot agree on all |L| points. -/
theorem rsEncode_injective (L : Finset (GaloisField 2 k)) (d : ℕ) (hd : d ≤ L.card)
    (p q : Polynomial (GaloisField 2 k)) (hp : p.natDegree < d) (hq : q.natDegree < d)
    (h : rsEncode L p = rsEncode L q) : p = q := by
  have hmax : max p.natDegree q.natDegree < L.card := by
    have hmax' : max p.natDegree q.natDegree < d := max_lt hp hq
    exact lt_of_lt_of_le hmax' hd
  have heval : ∀ α ∈ L, p.eval (α : GaloisField 2 k) = q.eval (α : GaloisField 2 k) := by
    intro α hα
    have hval := congr_fun h ⟨α, hα⟩
    simpa [rsEncode] using hval
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q L heval hmax

end ReedSolomon

-- ============================================================================
-- Section 2: Reed-Muller codes over 𝔽₂
-- ============================================================================
--
-- Reed-Muller code RM(r, m) ⊆ 𝔽₂^{𝔽₂ᵐ}: evaluate multivariate polynomials of
-- total degree ≤ r on the entire boolean hypercube 𝔽₂ᵐ.
--
--   Dimension = Σ_{i=0}^{r} C(m, i)
--   Minimum distance = 2^{m-r}
--
-- For the minimum distance: a nonzero polynomial of total degree ≤ r vanishes
-- on at most 2ᵐ − 2^{m-r} hypercube points. The proof uses the standard
-- induction RM(r,m) ≅ RM(r,m-1) + xₘ · RM(r-1,m-1).

section ReedMuller
variable {m r : ℕ}

lemma one_plus_one_zmod2 : (1 : ZMod 2) + (1 : ZMod 2) = (0 : ZMod 2) := by decide

/-- The evaluation of a multivariate polynomial over 𝔽₂ on the boolean
hypercube {0,1}ᵐ. -/
def rmEncode (p : MvPolynomial (Fin m) (ZMod 2)) : (Fin m → ZMod 2) → ZMod 2 :=
  fun x => eval x p

/-- The Reed-Muller code RM(r, m): evaluations of polynomials of total
degree ≤ r on the hypercube. -/
def rmCode (r : ℕ) : Set ((Fin m → ZMod 2) → ZMod 2) :=
  rmEncode '' {p : MvPolynomial (Fin m) (ZMod 2) | totalDegree p ≤ r}

/-- The hypercube domain 𝔽₂ᵐ as a Finset. -/
def hypercubeDomain (m : ℕ) : Finset (Fin m → ZMod 2) := Finset.univ

-- RM(1, 2) example: the linear polynomial x₀ + x₁.
-- Its evaluations on the 4 points of 𝔽₂² match the truth table of XOR.

example : rmEncode (X (0 : Fin 2) + X 1) (fun _ : Fin 2 => (0 : ZMod 2)) = (0 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1)
    (fun i : Fin 2 => if i = 0 then (1 : ZMod 2) else (0 : ZMod 2)) = (1 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1)
    (fun i : Fin 2 => if i = 1 then (1 : ZMod 2) else (0 : ZMod 2)) = (1 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1) (fun _ : Fin 2 => (1 : ZMod 2)) = (0 : ZMod 2) := by
  simp [rmEncode, one_plus_one_zmod2]

end ReedMuller
