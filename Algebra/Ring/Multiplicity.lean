import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Separable
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Multiplicity of Roots
-- ============================================================================
--
-- RootsInterpolation.lean §1 bounds the number of roots of a polynomial by
-- its degree. That bound is sharp only when roots are counted with
-- multiplicity: (X − 1)² has the single root 1, but it counts twice, and 2
-- matches the degree. This file defines the multiplicity of a root, computes
-- with it, and gives the two results that control it.
--
--   §1  Definition: the multiplicity of a in p is the number of times
--       (X − a) can be factored out of p.
--   §2  The degree budget: multiplicities sum to at most deg p, with
--       equality exactly when p splits into linear factors.
--   §3  The derivative test: a repeated root of p is a common root of p and
--       p′, so polynomials coprime to their derivative (separable) have only
--       simple roots.
--   §4  Characteristic 2: the freshman's dream (Characteristic.lean §3)
--       gives (X − 1)^{2ʳ} = X^{2ʳ} − 1, so a single root can carry the
--       whole degree budget. This is the polynomial side of "no 2-power
--       roots of unity" (BinaryFields.lean §3; the field-theoretic
--       squaring-collapse face is Characteristic.lean §4).
--
-- Prerequisites: RootsInterpolation.lean for the roots bound and the
-- eval-on-all-points technique for proving polynomial identities over 𝔽ₚ.

notation "𝔽₅" => ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

notation "𝔽₂" => ZMod 2
instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

open Polynomial

-- ============================================================================
-- Section 1: The multiplicity of a root
-- ============================================================================
--
-- The root theorem says a is a root of p exactly when (X − a) divides p:
--
--   p(a) = 0    ⟺    (X − a) divides p
--
-- TODO: This should be stated more generalized somewhere else, like
-- Polynomials.lean
--
-- Vanishing at the point a and carrying the linear factor (X − a) are one
-- fact, stated once for a value and once for the polynomial. Once one factor
-- comes out, the same question can be asked of the quotient, and a second
-- root at a means a second factor. The multiplicity of a in p is how many
-- times this succeeds: the largest m with (X − a)^m ∣ p.
--
-- Mathlib: `Polynomial.rootMultiplicity`.

example (K : Type*) [Field K] (p : K[X]) (a : K) :
    X - C a ∣ p ↔ p.IsRoot a :=
  dvd_iff_isRoot

-- "Largest" has two directions. The m factors really divide p:
example (K : Type*) [Field K] (p : K[X]) (a : K) :
    (X - C a) ^ (rootMultiplicity a p) ∣ p :=
  pow_rootMultiplicity_dvd p a

-- After dividing them out, the quotient is nonzero at a, so no
-- (m + 1)-th factor remains:
example (K : Type*) [Field K] {p : K[X]} (hp : p ≠ 0) (a : K) :
    (p /ₘ (X - C a) ^ (rootMultiplicity a p)).eval a ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero a hp

-- Multiplicities of explicit factors are computed by two lemmas:
-- `rootMultiplicity_X_sub_C_pow` for a pure power, and `rootMultiplicity_mul`
-- for a product (multiplicities add). Over 𝔽₅:
example : rootMultiplicity 1 ((X - C 1)^2 : 𝔽₅[X]) = 2 :=
  rootMultiplicity_X_sub_C_pow 1 2

-- A non-root has multiplicity 0: (X − 1)² at 2 evaluates to (2 − 1)² = 1 ≠ 0.
example : rootMultiplicity 2 ((X - C 1)^2 : 𝔽₅[X]) = 0 := by
  apply rootMultiplicity_eq_zero
  show ¬ ((X - C 1)^2 : 𝔽₅[X]).eval 2 = 0
  simp [eval_pow, eval_sub]
  decide

-- Let p = (X − 1)²(X − 2). Its roots, from the values over 𝔽₅:
--
--   p(1) = (1−1)²·(1−2) = 0·(−1) = 0   so 1 is a root
--   p(2) = (2−1)²·(2−2) = 1·0    = 0   so 2 is a root
--   p(0) = 3, p(3) = 4, p(4) = 3       no other roots
--
-- The multiplicities come from the factorization, not the value table. The
-- multiplicity of a is the number of times (X − a) divides p in a row: divide
-- once, and keep dividing while the quotient still vanishes at a (§1). For a
-- = 1 the quotient survives one division but not two:
--
--   p / (X − 1)  = (X − 1)(X − 2),   still 0 at 1, divide again
--   p / (X − 1)² = (X − 2),          1 at 1 ≠ 0, stop
--
-- so (X − 1) factors out exactly 2 times: the multiplicity of 1 is 2. For
-- a = 2 the quotient fails immediately after one division:
--
--   p / (X − 2)  = (X − 1)²,         1 at 2 ≠ 0, stop
--
-- so the multiplicity of 2 is 1. The value table sees the zeros but cannot
-- see these counts; only the factorization carries them.
example : rootMultiplicity 1 ((X - C 1)^2 * (X - C 2) : 𝔽₅[X]) = 2 := by
  have hne : (X - C 1)^2 * (X - C 2) ≠ (0 : 𝔽₅[X]) :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) (X_sub_C_ne_zero 2)
  rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow,
    rootMultiplicity_eq_zero (by
      show ¬ (X - C 2 : 𝔽₅[X]).eval 1 = 0
      simp [eval_sub]
      decide)]

-- ============================================================================
-- Section 2: The degree budget
-- ============================================================================
--
-- `p.roots` is the multiset of roots: each root a occurs rootMultiplicity a p
-- many times. So the roots bound `card_roots'` of RootsInterpolation.lean §1
-- already says that multiplicities sum to at most natDegree p.
example (K : Type*) [Field K] [DecidableEq K] (p : K[X]) (a : K) :
    p.roots.count a = rootMultiplicity a p :=
  count_roots p

example (K : Type*) [Field K] (p : K[X]) :
    Multiset.card p.roots ≤ p.natDegree :=
  Polynomial.card_roots' p

-- The budget is met exactly, sum of multiplicities = degree, precisely when
-- p splits into linear factors over K (as always over ℂ, but not over ℝ:
-- X² + 1 spends none of its budget).
example {K : Type*} [Field K] {p : K[X]} (h : p.Splits) :
    p.natDegree = Multiset.card p.roots :=
  h.natDegree_eq_card_roots

-- Over 𝔽₅, X⁴ − 1 splits completely: every nonzero element is a 4th root of
-- unity (RootsOfUnity.lean §1), so it has four simple roots and the budget
-- is met as 4 = 1 + 1 + 1 + 1. Proved by evaluation at all 5 points, as in
-- RootsInterpolation.lean §3.
example : ((X - C 1) * (X - C 2) * (X - C 3) * (X - C 4) : 𝔽₅[X]) = X^4 - 1 := by
  have hpt : ∀ x : 𝔽₅, (x - 1) * (x - 2) * (x - 3) * (x - 4) = x^4 - 1 := by
    decide
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ Finset.univ
  · intro x _
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one]
    exact hpt x
  · rw [show (Finset.univ : Finset 𝔽₅).card = 5 from by decide]
    have hl :
        ((X - C 1) * (X - C 2) * (X - C 3) * (X - C 4) : 𝔽₅[X]).natDegree ≤ 4 := by
      compute_degree!
    have hr : (X^4 - 1 : 𝔽₅[X]).natDegree ≤ 4 := by compute_degree!
    exact lt_of_le_of_lt (max_le hl hr) (by norm_num)

-- ============================================================================
-- Section 3: The derivative test
-- ============================================================================
--
-- If (X − a)² divides p, so p = (X − a)²·q, the product rule gives
-- p′ = 2(X − a)q + (X − a)²q′, which vanishes at a. So every repeated root
-- of p is a common root of p and p′.
example {K : Type*} [Field K] {p q : K[X]} {a : K} (h : p = (X - C a)^2 * q) :
    p.derivative.eval a = 0 := by
  rw [h, derivative_mul]
  simp [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, derivative_pow]

-- Contrapositive: if p and p′ are coprime, no root is repeated. Mathlib
-- calls such a polynomial `Separable`; then the roots multiset has no
-- duplicates, meaning every root has multiplicity 1. Concretely for X⁴ − 1
-- over 𝔽₅ the coprimality witness is 4·(X⁴ − 1) − X·(4X³) = 1; the library
-- lemma `separable_X_pow_sub_C` produces it from 4 ≠ 0.
example : (X^4 - C 1 : 𝔽₅[X]).Separable :=
  separable_X_pow_sub_C 1 (by decide : (4 : 𝔽₅) ≠ 0) one_ne_zero

-- So the four factors in the §2 factorization are genuinely distinct.
example : (X^4 - C 1 : 𝔽₅[X]).roots.Nodup :=
  Polynomial.nodup_roots
    (separable_X_pow_sub_C 1 (by decide : (4 : 𝔽₅) ≠ 0) one_ne_zero)

-- ============================================================================
-- Section 4: Characteristic p: the collapse
-- ============================================================================
--
-- In characteristic p the freshman's dream iterates: the p-th power map is a
-- ring homomorphism, so its iterates are too, and (x + y)^{pʳ} =
-- x^{pʳ} + y^{pʳ}. Powers of p are exactly the exponents with this property;
-- for a multiple like 2p the interior binomial coefficients survive.
theorem add_pow_two_pow {R : Type*} [CommRing R] [CharP R 2] (x y : R) (r : ℕ) :
    (x + y) ^ (2 ^ r) = x ^ (2 ^ r) + y ^ (2 ^ r) := by
  induction r generalizing x y with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    exact add_pow_char (R := R) _ _ (p := 2)

-- Applied to X and 1 with p = 2, using 1 = −1 in characteristic 2:
--
--   (X − 1)^{2ʳ} = X^{2ʳ} − 1.
example (F : Type*) [Field F] [CharP F 2] (r : ℕ) :
    (X - 1 : F[X]) ^ (2 ^ r) = X ^ (2 ^ r) - 1 := by
  have h : (X + 1 : F[X]) ^ (2 ^ r) = X ^ (2 ^ r) + 1 := by
    simpa using add_pow_two_pow (R := F[X]) X 1 r
  have e1 : (X - 1 : F[X]) = X + 1 := by rw [sub_eq_add_neg, CharTwo.neg_eq]
  have e2 : (X ^ (2 ^ r) - 1 : F[X]) = X ^ (2 ^ r) + 1 := by
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [e1, e2]
  exact h

-- So X^{2ʳ} − 1, which over 𝔽₅ splits into distinct linear factors (§2, §3),
-- here has the single root 1 with multiplicity 2ʳ: the entire degree budget
-- spent on one point.
example (F : Type*) [Field F] [CharP F 2] (r : ℕ) :
    rootMultiplicity 1 ((X - C 1 : F[X]) ^ (2 ^ r)) = 2 ^ r :=
  rootMultiplicity_X_sub_C_pow 1 (2 ^ r)

example : rootMultiplicity 1 ((X - C 1)^2 : 𝔽₂[X]) = 2 :=
  rootMultiplicity_X_sub_C_pow 1 2

-- The derivative test sees the same collapse from the other side. The
-- derivative of X^{2ʳ} − 1 is 2ʳ·X^{2ʳ−1}, and 2ʳ = 0 in characteristic 2,
-- so p′ vanishes identically and §3's criterion becomes vacuous.
example (F : Type*) [Field F] [CharP F 2] {r : ℕ} (hr : 0 < r) :
    (X ^ (2 ^ r) - 1 : F[X]).derivative = 0 := by
  have h2 : ((2 ^ r : ℕ) : F) = 0 :=
    (CharP.cast_eq_zero_iff F 2 _).mpr (dvd_pow_self 2 hr.ne')
  simp [derivative_sub, derivative_pow, derivative_one, h2]
