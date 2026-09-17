import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic
import Algebra.Code.ReedSolomonReedMuller
import Algebra.Field.G8

open Polynomial

noncomputable section

-- ============================================================================
-- Evaluation opening: proving p(r) = v without a table entry at r
-- ============================================================================
--
-- A committed word is the table of a polynomial p on a domain L
-- (ReedSolomonReedMuller.lean §1). The verifier's final question in a
-- polynomial commitment is "p(r) = v?" at a point r sampled after the
-- commitment, and r lies outside L with overwhelming probability: the
-- prover cannot be expected to Merkleize the whole field. The opening
-- must therefore be proved, not read.
--
-- The quotient trick: p(r) = v iff X − r divides p(X) − v, iff
--
--   q(X) = (p(X) − v) / (X − r)
--
-- is a polynomial of degree < d − 1. So the prover answers the claim by
-- tabulating q on L; the verifier proximity-tests that table against the
-- smaller degree bound (binary FRI, BinaryFRI.lean). If the claim is
-- false, q has a pole at r and its table is far from every codeword
-- (quotientWord_agreement_le, §2), which is what the proximity test
-- catches.
--
-- The full opening, as a protocol. Once the claim (r, v) exists, the
-- prover commits the quotient word as a fresh root; the quotient's fold
-- chain is then committed round by round (BinaryFRI.lean §1c) against
-- the smaller degree bound. At each query the verifier opens both
-- roots, w(x) from word 0 and q(x) from the quotient, and checks
-- q(x)·(x − r) = w(x) − v: this binds the quotient to the polynomial
-- committed before any challenges existed. A fabricated quotient fails
-- this equation at query points; a consistent-but-false one fails the
-- proximity test (§2).
--
--   §1  The quotient word and its consistency
--   §2  The distance bound for a false claim
--   §3  Computed demonstration over GF(8)
--
-- Prerequisites: ReedSolomonReedMuller.lean (the code and its distance
-- bound). Used by Binius.lean §4 (the opening at r).

namespace EvalOpening

-- ============================================================================
-- Section 1: The quotient word and its consistency
-- ============================================================================

section Quotient
variable {F : Type*} [Field F]

/-- The quotient word: the table of (w(x) − v)/(x − r), computed from the
word by field arithmetic only; no polynomial is needed on the verifier's
side. At x = r the value is junk (0); the interesting case is r outside
the domain. -/
def quotientWord (w : F → F) (r v : F) (x : F) : F := (w x - v) / (x - r)

/-- Consistency: if w is the table of p and the claim p(r) = v holds, the
quotient word is the table of the genuine polynomial quotient
(p − v)/(X − r), at every x ≠ r. -/
theorem quotientWord_eval (p : Polynomial F) (r v : F) (hvr : p.eval r = v)
    (w : F → F) (hw : ∀ x, w x = p.eval x) (x : F) (hx : x ≠ r) :
    quotientWord w r v x = ((p - C v) /ₘ (X - C r)).eval x := by
  have hdvd : X - C r ∣ p - C v := by
    rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, hvr, sub_self]
  have hq : p - C v = (X - C r) * ((p - C v) /ₘ (X - C r)) := by
    have h0 : (p - C v) %ₘ (X - C r) = 0 :=
      (modByMonic_eq_zero_iff_dvd (monic_X_sub_C r)).mpr hdvd
    have h := modByMonic_add_div (p - C v) (X - C r)
    rw [h0, zero_add] at h
    exact h.symm
  have e := congr_arg (Polynomial.eval x) hq
  rw [eval_sub, eval_C, eval_mul, eval_sub, eval_X, eval_C] at e
  unfold quotientWord
  rw [hw x, e]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hx)

/-- The quotient has degree < d − 1 when p has degree < d: the opening is
tested against the smaller code RS[L, d−1]. -/
theorem natDegree_quotient_le (p : Polynomial F) (d : ℕ) (v r : F)
    (hp : p.natDegree < d) :
    ((p - C v) /ₘ (X - C r)).natDegree ≤ d - 2 := by
  have h1 : (p - C v).natDegree ≤ p.natDegree := by
    have hc := natDegree_C v
    have h := natDegree_sub_le p (C v)
    omega
  rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
  omega

end Quotient

-- ============================================================================
-- Section 2: The distance bound for a false claim
-- ============================================================================
--
-- If the claim is false (p(r) ≠ v), the quotient is not a polynomial, and
-- the quotient word is far from every codeword of the smaller code: any
-- q̃ of degree < d − 1 whose table matched the quotient word on d points
-- would give two polynomials of degree < d (p and q̃·(X − r) + v) agreeing
-- on d points, hence equal by rs_agreement_card_le, forcing p(r) = v.

section Distance
variable {k d : ℕ}

/-- The set of points of L on which the quotient word agrees with the
table of q'. GaloisField carries no DecidableEq instance, so the filter
is formed classically, as in rsAgreement. -/
noncomputable def quotientAgreement (L : Finset (GaloisField 2 k))
    (w : GaloisField 2 k → GaloisField 2 k) (r v : GaloisField 2 k)
    (q' : Polynomial (GaloisField 2 k)) : Finset (GaloisField 2 k) := by
  classical
  exact L.filter fun x => quotientWord w r v x = q'.eval x

/-- A false claim is far from every codeword of the smaller code: if
p(r) ≠ v, any polynomial q' of degree < d − 1 agrees with the quotient
word on at most d − 1 points of L. The proximity test against RS[L, d−1]
therefore catches the false claim. -/
theorem quotientWord_agreement_le
    (L : Finset (GaloisField 2 k)) (d : ℕ)
    (p q' : Polynomial (GaloisField 2 k)) (r v : GaloisField 2 k)
    (hp : p.natDegree < d) (hq' : q'.natDegree < d - 1)
    (hvr : p.eval r ≠ v) (hrL : r ∉ L)
    (w : GaloisField 2 k → GaloisField 2 k) (hw : ∀ x, w x = p.eval x) :
    (quotientAgreement L w r v q').card ≤ d - 1 := by
  classical
  have hsub : quotientAgreement L w r v q' ⊆
      rsAgreement L p (q' * (X - C r) + C v) := by
    intro x hx
    rw [quotientAgreement, Finset.mem_filter] at hx
    rw [rsAgreement, Finset.mem_filter]
    refine ⟨hx.1, ?_⟩
    have hxr : x - r ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hrL (h ▸ hx.1)
    have e : w x - v = q'.eval x * (x - r) := by
      rw [← hx.2]
      unfold quotientWord
      rw [div_mul_cancel₀ _ hxr]
    rw [hw x] at e
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C, ← e, sub_add_cancel]
  have hne : p ≠ q' * (X - C r) + C v := by
    intro h
    apply hvr
    have e := congr_arg (Polynomial.eval r) h
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C, sub_self, mul_zero,
      zero_add] at e
    exact e
  have hdeg : (q' * (X - C r) + C v).natDegree < d := by
    have h1 : (q' * (X - C r)).natDegree ≤ q'.natDegree + 1 := by
      by_cases h0 : q' = 0
      · rw [h0, zero_mul, natDegree_zero]; omega
      · rw [natDegree_mul h0 (X_sub_C_ne_zero r), natDegree_X_sub_C]
    have h2 := le_trans (natDegree_add_le _ _)
      (max_le_max h1 (le_of_eq (natDegree_C v)))
    omega
  exact le_trans (Finset.card_le_card hsub)
    (rs_agreement_card_le L d p _ hp hdeg hne)

end Distance

-- ============================================================================
-- Section 3: Computed demonstration over GF(8)
-- ============================================================================
--
-- The hand-rolled G8 (Algebra/Field/G8.lean) evaluates with decide. The
-- message is p(X) = X² + X + 1 (degree 2, so d = 3), the domain is the
-- 2-dimensional subspace L = {0, 1, α, α+1}, and the claim point r = α²
-- lies outside L: there is no table entry to read, the opening must be
-- proved. In char 2 subtraction is addition and inv is the reciprocal.

section Demo
open G8

/-- The message p(X) = X² + X + 1 over GF(8), as a function. -/
def p : G8 → G8 := fun x => x * x + x + 1

/-- The committed domain: the subspace {0, 1, α, α+1} of GF(8). -/
def L : List G8 := [0, 1, α, α + 1]

/-- The claim point, outside the domain. -/
def r : G8 := α²

/-- The claim value: v = p(r) = α⁴ + α² + 1 = α + 1. -/
def v : G8 := α + 1

example : r ∉ L := by decide
example : p r = v := by decide

/-- The quotient word, local copy over G8: (w(x) + v)·inv(x + r). -/
def quotW (w : G8 → G8) (r v : G8) (x : G8) : G8 := (w x + v) * inv (x + r)

-- Honest claim: on L the quotient word is the line x ↦ x + (1 + α²), the
-- table of the genuine quotient X + (1 + α²) of degree 1 = d − 2, since
-- X² + X + α = (X + α²)·(X + 1 + α²). The opening verifies.
example : ∀ x ∈ L, quotW p r v x = x + (1 + α²) := by decide

-- False claim v' = α: the "quotient" table on L fits no line t ↦ a·t + b,
-- so it is not any degree-1 polynomial's table. The proximity test
-- against degree < d − 1 = 2 catches it (quotientWord_agreement_le).
example : ¬ ∃ a b : G8, ∀ x ∈ L, quotW p r α x = a * x + b := by decide

end Demo

end EvalOpening
