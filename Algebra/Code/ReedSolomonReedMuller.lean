import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic
import Algebra.Field.G8

open Polynomial
open MvPolynomial
open Finset

noncomputable section

-- TODO: Note that we have a section on (Lagrange) interpolation in
-- RootsInterpolation.lean, relevant here.

-- ============================================================================
-- Reed-Solomon and Reed-Muller codes
-- ============================================================================
--
-- A Reed-Solomon (RS) code evaluates univariate polynomials of bounded
-- degree on a finite subset of a field; here GF(2ᵏ). A Reed-Muller (RM)
-- code evaluates multivariate polynomials of bounded total degree on the
-- boolean hypercube {0,1}ᵐ.
--
-- Encoding is just evaluation, so the mathematical content is the distance
-- bound: how few points two distinct messages can agree on. Decoding
-- (error recovery) is implementation-specific and out of scope.
--
--   §1  Reed-Solomon codes over GF(2ᵏ)
--   §2  Reed-Muller codes over 𝔽₂
-- ============================================================================

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

-- ============================================================================
-- Section 1: Reed-Solomon codes over GF(2ᵏ)
-- ============================================================================
--
-- Let L ⊆ GF(2ᵏ) be a finite subset. The RS code RS[L, d] encodes a
-- polynomial p ∈ GF(2ᵏ)[X] of degree < d as the vector (p(α))_{α∈L}.
--
-- Because a nonzero polynomial of degree < d has at most d−1 roots in any
-- field (RootsInterpolation.lean §1), two distinct such polynomials agree
-- on at most d−1 points of L. Therefore RS[L, d] has minimum distance
-- |L| − d + 1, proved as `rs_min_distance` at the end of the section.
-- The injectivity theorem below is the uniqueness corollary: two codewords
-- at distance 0 come from the same polynomial.

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
theorem rsEncode_injective
    (L : Finset (GaloisField 2 k))
    (d : ℕ)
    (hd : d ≤ L.card)
    (p q : Polynomial (GaloisField 2 k))
    (hp : p.natDegree < d)
    (hq : q.natDegree < d)
    (h : rsEncode L p = rsEncode L q)
  :
    p = q := by
  have hmax : max p.natDegree q.natDegree < L.card := by
    have hmax' : max p.natDegree q.natDegree < d := max_lt hp hq
    exact lt_of_lt_of_le hmax' hd
  have heval : ∀ α ∈ L, p.eval (α : GaloisField 2 k) = q.eval (α : GaloisField 2 k) := by
    intro α hα
    have hval := congr_fun h ⟨α, hα⟩
    simpa [rsEncode] using hval
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q L heval hmax

/-- The set of points of L on which p and q agree. The codewords differ on
the complement, so their Hamming distance is |L| − |rsAgreement L p q|. -/
noncomputable def rsAgreement (L : Finset (GaloisField 2 k))
    (p q : Polynomial (GaloisField 2 k)) : Finset (GaloisField 2 k) := by
  classical
  exact L.filter fun α => p.eval α = q.eval α

/-- Agreement bound: distinct polynomials of degree < d agree on at most
d−1 points of L. Every agreement point is a root of the nonzero difference
p − q, whose degree is < d. -/
theorem rs_agreement_card_le
    (L : Finset (GaloisField 2 k))
    (d : ℕ)
    (p q : Polynomial (GaloisField 2 k))
    (hp : p.natDegree < d)
    (hq : q.natDegree < d)
    (hpq : p ≠ q)
  :
    (rsAgreement L p q).card ≤ d - 1 := by
  classical
  have hpq' : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsub : rsAgreement L p q ⊆ (p - q).roots.toFinset := by
    intro α hα
    rw [rsAgreement, Finset.mem_filter] at hα
    rw [Multiset.mem_toFinset, mem_roots hpq', IsRoot.def, Polynomial.eval_sub,
      sub_eq_zero]
    exact hα.2
  have hcard : (rsAgreement L p q).card ≤ (p - q).natDegree :=
    le_trans (le_trans (Finset.card_le_card hsub)
      (Multiset.toFinset_card_le (p - q).roots)) (card_roots' (p - q))
  have hdeg : (p - q).natDegree ≤ d - 1 :=
    le_trans (natDegree_sub_le p q) (max_le (by omega) (by omega))
  omega

/-- Minimum distance of RS[L, d]: two distinct codewords differ in at least
|L| − d + 1 positions. The injectivity theorem above is the special case
"distance 0 implies equal polynomials". -/
theorem rs_min_distance
    (L : Finset (GaloisField 2 k))
    (d : ℕ)
    (hd : d ≤ L.card)
    (p q : Polynomial (GaloisField 2 k))
    (hp : p.natDegree < d)
    (hq : q.natDegree < d)
    (hpq : p ≠ q)
  :
    L.card - d + 1 ≤ L.card - (rsAgreement L p q).card := by
  have h := rs_agreement_card_le L d p q hp hq hpq
  omega

end ReedSolomon

-- ----------------------------------------------------------------------------
-- Demonstration over GF(8), computed by decide
-- ----------------------------------------------------------------------------
--
-- The hand-rolled G8 (Algebra/Field/G8.lean) evaluates with decide, so the
-- codeword and the distance bound can be checked entry by entry. The
-- messages are written as functions: p is X² + 1 and q is X² + X + 1,
-- both of degree 2 < d = 3.

namespace RSDemo

open G8

/-- The message p(X) = X² + 1 over GF(8), as a function. -/
def p : G8 → G8 := fun x => x * x + 1

/-- The message q(X) = X² + X + 1 over GF(8), as a function. -/
def q : G8 → G8 := fun x => x * x + x + 1

/-- The evaluation domain: all of GF(8), ordered
0, 1, α, α+1, α², α²+1, α²+α, α²+α+1. -/
def L : List G8 := [0, 1, α, α + 1, α², α² + 1, α² + α, α² + α + 1]

-- The codeword of p is its evaluation table. Squaring is injective in
-- characteristic 2, so all eight entries are distinct.
example : L.map p = [1, 0, α² + 1, α², α² + α + 1, α² + α, α + 1, α] := by decide

-- Distinct polynomials of degree < 3 agree on at most 2 = d − 1 points
-- (rs_agreement_card_le); p and q agree only at 0, since p(x) = q(x)
-- iff x = 0.
example : (L.filter fun x => p x = q x) = [0] := by decide

-- So their codewords differ in 7 of 8 positions; rs_min_distance
-- guarantees at least 8 − 3 + 1 = 6.
example : (L.filter fun x => p x ≠ q x).length = 7 := by decide

end RSDemo

-- ============================================================================
-- Section 2: Reed-Muller codes over 𝔽₂
-- ============================================================================
--
-- The Reed-Muller code RM(r, m) ⊆ 𝔽₂^{𝔽₂ᵐ} evaluates multivariate
-- polynomials of total degree ≤ r on the entire boolean hypercube 𝔽₂ᵐ.
--
--   Dimension = Σ_{i=0}^{r} C(m, i)
--   Minimum distance = 2^{m-r}
--
-- For the minimum distance: a nonzero polynomial of total degree ≤ r
-- vanishes on at most 2ᵐ − 2^{m-r} hypercube points. The proof uses the
-- induction RM(r,m) ≅ RM(r,m-1) + xₘ · RM(r-1,m-1); it is not formalized
-- here.

section ReedMuller
variable {m r : ℕ}

/-- The evaluation of a multivariate polynomial over 𝔽₂ on the boolean
hypercube {0,1}ᵐ. -/
def rmEncode (p : MvPolynomial (Fin m) (ZMod 2)) : (Fin m → ZMod 2) → ZMod 2 :=
  fun x => eval x p

/-- The Reed-Muller code RM(r, m): evaluations of polynomials of total
degree ≤ r on the hypercube. -/
def rmCode (r : ℕ) : Set ((Fin m → ZMod 2) → ZMod 2) :=
  rmEncode '' {p : MvPolynomial (Fin m) (ZMod 2) | totalDegree p ≤ r}

-- RM(1, 2) example: the linear polynomial x₀ + x₁. Its evaluations on the
-- four points of 𝔽₂² are the truth table of XOR.

example : rmEncode (X (0 : Fin 2) + X 1) (fun _ : Fin 2 => (0 : ZMod 2)) = (0 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1)
    (fun i : Fin 2 => if i = 0 then (1 : ZMod 2) else (0 : ZMod 2)) = (1 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1)
    (fun i : Fin 2 => if i = 1 then (1 : ZMod 2) else (0 : ZMod 2)) = (1 : ZMod 2) := by
  simp [rmEncode]

example : rmEncode (X (0 : Fin 2) + X 1) (fun _ : Fin 2 => (1 : ZMod 2)) = (0 : ZMod 2) := by
  simp [rmEncode, show (1 : ZMod 2) + 1 = 0 by decide]

-- The four evaluations above form the codeword of x₀ + x₁: it has weight
-- 2 = 2^{2−1}, the minimum distance of RM(1, 2). That this codeword lies
-- in the code:
example : rmEncode (X (0 : Fin 2) + X 1) ∈ rmCode (m := 2) 1 := by
  refine ⟨X 0 + X 1, ?_, rfl⟩
  simp only [Set.mem_setOf_eq]
  exact le_trans (totalDegree_add _ _) (by simp)

end ReedMuller
