import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
open scoped BigOperators

open MvPolynomial
open Finset Fintype

-- ============================================================================
-- Multivariate Polynomials and the Boolean Hypercube
-- ============================================================================
--
-- This file extends the univariate polynomial facts from
-- RootsInterpolation.lean to the multivariate setting.  The main goal is the
-- Multilinear Extension (MLE): given a function f : {0,1}ⁿ → R, there is a
-- unique multilinear polynomial matching f on the boolean hypercube.
--
-- Prerequisites: RootsInterpolation.lean for the univariate roots bound;
-- BinaryFields.lean for the connection between boolean functions and 𝔽₂
-- polynomials.
--
--   §1  MvPolynomial basics and degree bounds
--   §2  Multivariate Schwartz-Zippel lemma
--   §3  Multilinear extension (MLE) over 𝔽₂
--   §4  Subset basis and Moebius transform (ANF over 𝔽₂)
--   §5  Hypercube sum and vanishing
-- ============================================================================

noncomputable section

-- ============================================================================
-- Section 1: MvPolynomial basics and degree bounds
-- ============================================================================

section Basics
variable {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]

-- Total degree of a variable is 1.
example (i : σ) : totalDegree (X i : MvPolynomial σ R) = 1 := totalDegree_X i

-- Degree bounds: product and sum.
example (p : MvPolynomial σ R) : totalDegree (p * p) ≤ totalDegree p + totalDegree p :=
  totalDegree_mul _ _

example (p q : MvPolynomial σ R) : totalDegree (p + q) ≤ max (totalDegree p) (totalDegree q) :=
  totalDegree_add _ _

-- Constants have total degree 0.
example (a : R) : totalDegree (C a : MvPolynomial σ R) = 0 := totalDegree_C _

-- Evaluation at a point.
example : eval (fun _ : Fin 2 => (1 : ℚ)) ((X 0 : MvPolynomial (Fin 2) ℚ) + X 1) = 2 := by
  norm_num [MvPolynomial.eval]

end Basics

-- ============================================================================
-- Section 2: Multivariate Schwartz-Zippel
-- ============================================================================

-- TODO: Should we mention sumcheck here?

section SchwartzZippel
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}

/-- The boolean hypercube as a product set {0,1}ⁿ. -/
def hypercube (R : Type*) [CommRing R] [DecidableEq R] (n : ℕ) : Finset (Fin n → R) :=
  piFinset (fun _ : Fin n => ({0, 1} : Finset R))

-- The Schwartz-Zippel lemma for a nonzero polynomial p:
--
--   #{x ∈ Sⁿ | p(x) = 0} / |S|ⁿ  ≤  totalDegree(p) / |S|   (as ℚ≥0)
--
-- With S = {0,1} the bound becomes:
--
--   Pr_{x ∈ {0,1}ⁿ} [p(x) = 0]  ≤  totalDegree(p) / 2.
--
-- The Mathlib lemma `schwartz_zippel_totalDegree` applies to
-- polynomials over an integral domain R with |S|≥1. The two examples below
-- state the bound and then the special case totalDegree = 1 (a single
-- sumcheck round, where the verifier catches a cheating prover with
-- probability at least 1/2).
example (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) :
    (((hypercube R n).filter fun x => eval x p = 0).card : ℚ≥0) / ((hypercube R n).card : ℚ≥0)
    ≤ (p.totalDegree : ℚ≥0) / 2 := by
  simpa [hypercube] using schwartz_zippel_totalDegree hp ({0, 1} : Finset R)

-- If totalDegree(p) = 1 then the fraction of hypercube points where p
-- vanishes is at most 1/2.  This is the soundness guarantee of one
-- sumcheck round: when the prover pretends p is nonzero but p is in fact
-- zero at too many points, the verifier's random challenge catches it
-- with probability > 1/2.
example (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) (hdeg : p.totalDegree = 1) :
    (((hypercube R n).filter fun x => eval x p = 0).card : ℚ≥0) / ((hypercube R n).card : ℚ≥0)
    ≤ 1/2 := by
  have h := schwartz_zippel_totalDegree hp ({0, 1} : Finset R)
  simpa [hypercube, hdeg] using h

end SchwartzZippel

-- ============================================================================
-- Section 3: Multilinear extension (MLE) over 𝔽₂
-- ============================================================================
--
-- A polynomial is multilinear if every variable appears with exponent at most
-- 1 in every monomial.  On the boolean hypercube {0,1}ⁿ such a polynomial is
-- pinned down by its 2ⁿ values.  Conversely, every function f : {0,1}ⁿ → R
-- extends to a multilinear polynomial, the Multilinear Extension (MLE), built
-- here over 𝔽₂ from the indicator polynomials χᵥ that are 1 at a single
-- hypercube point and 0 elsewhere.

section MLE
variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- A polynomial is multilinear: every variable has exponent at most 1 in every
monomial. -/
def IsMultilinear (p : MvPolynomial (Fin n) R) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

theorem isMultilinear_C (a : R) : IsMultilinear (C a : MvPolynomial (Fin n) R) := by
  intro m hm i
  rw [mem_support_iff] at hm
  have hm0 : m = 0 := by
    by_contra h
    apply hm
    rw [coeff_C, if_neg (Ne.symm h)]
  subst hm0; simp

theorem isMultilinear_X (i : Fin n) : IsMultilinear (X i : MvPolynomial (Fin n) R) := by
  intro m hm j
  rw [mem_support_iff] at hm
  have hm0 : m = Finsupp.single i 1 := by
    by_contra h
    apply hm
    have hX : (X i : MvPolynomial (Fin n) R) = monomial (Finsupp.single i 1) (1 : R) := rfl
    rw [hX, coeff_monomial m (Finsupp.single i 1) (1 : R)]
    by_cases hcase : Finsupp.single i 1 = m
    · exfalso; exact h hcase.symm
    · simp [hcase]
  subst hm0
  simp [Finsupp.single_apply]
  split_ifs <;> simp

theorem isMultilinear_add {p q : MvPolynomial (Fin n) R}
    (hp : IsMultilinear p) (hq : IsMultilinear q) : IsMultilinear (p + q) := by
  intro m hm i
  rw [mem_support_iff, coeff_add] at hm
  have hm' : coeff m p ≠ 0 ∨ coeff m q ≠ 0 := by
    contrapose! hm; simp [hm]
  rcases hm' with (hm' | hm')
  · apply hp m (by rwa [mem_support_iff]) i
  · apply hq m (by rwa [mem_support_iff]) i

theorem isMultilinear_smul {p : MvPolynomial (Fin n) R} (c : R)
    (hp : IsMultilinear p) : IsMultilinear (c • p) := by
  intro m hm i
  rw [mem_support_iff, coeff_smul] at hm
  have hm' : coeff m p ≠ 0 := by
    contrapose! hm; simp [hm]
  apply hp m (by rwa [mem_support_iff]) i

lemma mem_vars_of_mem_support (p : MvPolynomial (Fin n) R) {m : Fin n →₀ ℕ} {i : Fin n}
    (hm : m ∈ p.support) (hi : m i ≠ 0) : i ∈ p.vars := by
  rw [MvPolynomial.mem_vars]
  refine ⟨m, hm, ?_⟩
  rwa [Finsupp.mem_support_iff]

theorem IsMultilinear.mul_of_disjoint {p q : MvPolynomial (Fin n) R}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (hdisj : Disjoint p.vars q.vars) :
    IsMultilinear (p * q) := by
  intro m hm i
  rw [mem_support_iff, coeff_mul] at hm
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have h1 : coeff x.1 p ≠ 0 := by
    intro h; apply hxne; simp [h]
  have h2 : coeff x.2 q ≠ 0 := by
    intro h; apply hxne; simp [h]
  have hx1 : x.1 ∈ p.support := (mem_support_iff).2 h1
  have hx2 : x.2 ∈ q.support := (mem_support_iff).2 h2
  have hsum : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
  have hle1 : x.1 i ≤ 1 := hp x.1 hx1 i
  have hle2 : x.2 i ≤ 1 := hq x.2 hx2 i
  have hzero : x.1 i = 0 ∨ x.2 i = 0 := by
    by_contra h
    push Not at h
    have hi1 : i ∈ p.vars := mem_vars_of_mem_support p hx1 h.1
    have hi2 : i ∈ q.vars := mem_vars_of_mem_support q hx2 h.2
    have hmem : i ∈ p.vars ∩ q.vars := by simp [hi1, hi2]
    have hsub : p.vars ∩ q.vars = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    simp [hsub] at hmem
  rw [← hsum, Finsupp.add_apply]
  omega

theorem isMultilinear_prod_of_pairwise_disjoint (s : Finset (Fin n))
    (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, IsMultilinear (p i))
    (hvars : ∀ i, (p i).vars ⊆ {i})
    (hdisj : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → i ≠ j → Disjoint (p i).vars (p j).vars) :
    IsMultilinear (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using isMultilinear_C (1 : R)
  | insert i s hi ih =>
      have hprod : (∏ j ∈ insert i s, p j) = p i * ∏ j ∈ s, p j := by
        simp [Finset.prod_insert hi]
      rw [hprod]
      have hdisj_for_s : ∀ ⦃i' : Fin n⦄, i' ∈ s → ∀ ⦃j' : Fin n⦄, j' ∈ s → i' ≠ j' → Disjoint (p i').vars (p j').vars :=
        fun i' hi' j' hj' hne' => hdisj (Finset.mem_insert_of_mem hi') (Finset.mem_insert_of_mem hj') hne'
      refine IsMultilinear.mul_of_disjoint (hp i) (ih hdisj_for_s) ?_
      have hivars : (p i).vars ⊆ {i} := hvars i
      have hs : (∏ j ∈ s, p j).vars ⊆ s.biUnion (fun j => (p j).vars) := by
        simpa using MvPolynomial.vars_prod (s := s) (fun j : Fin n => p j)
      have hunion : s.biUnion (fun j : Fin n => (p j).vars) ⊆ {i}ᶜ := by
        intro a ha
        rw [Finset.mem_compl]
        rw [Finset.mem_biUnion] at ha
        rcases ha with ⟨j, hj, haj⟩
        have hjn : j ≠ i := by
          intro hji; exact hi (hji ▸ hj)
        have hsub : (p j).vars ⊆ {j} := hvars j
        have haj' : a ∈ {j} := hsub haj
        have haj_eq : a = j := Finset.mem_singleton.mp haj'
        intro hai
        have hai_eq : a = i := Finset.mem_singleton.mp hai
        exact hjn (haj_eq.symm.trans hai_eq)
      apply Finset.disjoint_left.mpr
      intro a hai has
      have has' : a ∈ s.biUnion (fun j : Fin n => (p j).vars) := hs has
      have hac : a ∈ {i}ᶜ := hunion has'
      have hai' : a ∈ {i} := hivars hai
      exact (Finset.mem_compl.mp hac) hai'

def subsetMonomial (S : Finset (Fin n)) : MvPolynomial (Fin n) R :=
  ∏ i ∈ S, X i

theorem isMultilinear_subsetMonomial (S : Finset (Fin n)) [Nontrivial R] :
    IsMultilinear (subsetMonomial S : MvPolynomial (Fin n) R) := by
  refine isMultilinear_prod_of_pairwise_disjoint S (fun i => X i)
    (fun i => isMultilinear_X i)
    (fun i => by simp [MvPolynomial.vars_X])
    (fun i hi j hj hij => by
      apply Finset.disjoint_left.mpr
      intro a hai haj
      have hai' : a = i := by
        have htemp : (X i : MvPolynomial (Fin n) R).vars = {i} := by simp [MvPolynomial.vars_X]
        have : a ∈ ({i} : Finset (Fin n)) := by rwa [← htemp]
        exact Finset.mem_singleton.mp this
      have haj' : a = j := by
        have htemp : (X j : MvPolynomial (Fin n) R).vars = {j} := by simp [MvPolynomial.vars_X]
        have : a ∈ ({j} : Finset (Fin n)) := by rwa [← htemp]
        exact Finset.mem_singleton.mp this
      exact hij (hai'.symm.trans haj'))

theorem eval_subsetMonomial (S : Finset (Fin n)) (v : Fin n → R) :
    eval v (subsetMonomial S) = ∏ i ∈ S, v i := by
  simp [subsetMonomial, eval_X]

end MLE

-- ============================================================================
-- Section 3 continued: the MLE over 𝔽₂ via the indicator basis
-- ============================================================================

section MLEOverBinary
variable {n : ℕ}

/-- The indicator polynomial of a hypercube point v: 1 at v, 0 elsewhere. -/
def mleIndicator (v : Fin n → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) :=
  ∏ i : Fin n, (if v i = 1 then X i else 1 - X i)

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := x.isLt
  have hx' : x.val ≤ 1 := by omega
  have hxval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hxval with h | h
  · left; simpa [h] using (ZMod.natCast_zmod_val x).symm
  · right; simpa [h] using (ZMod.natCast_zmod_val x).symm

lemma sub_eq_add_zmod2 (x : ZMod 2) : x - (1 : ZMod 2) = x + 1 := by
  fin_cases x <;> decide

lemma vars_one_minus_X (i : Fin n) : (1 - X i : MvPolynomial (Fin n) (ZMod 2)).vars ⊆ {i} := by
  have hsub : (1 - X i : MvPolynomial (Fin n) (ZMod 2)).vars ⊆
    (1 : MvPolynomial (Fin n) (ZMod 2)).vars ∪ (X i : MvPolynomial (Fin n) (ZMod 2)).vars := by
    simpa [sub_eq_add_neg] using MvPolynomial.vars_add_subset (1 : MvPolynomial (Fin n) (ZMod 2))
      (-(X i : MvPolynomial (Fin n) (ZMod 2)))
  have h1 : (1 : MvPolynomial (Fin n) (ZMod 2)).vars = ∅ := by simp [MvPolynomial.vars_one]
  have hX : (X i : MvPolynomial (Fin n) (ZMod 2)).vars = {i} := by simp [MvPolynomial.vars_X]
  rw [h1, hX, Finset.empty_union] at hsub
  exact hsub

lemma vars_of_factor (v : Fin n → ZMod 2) (i : Fin n) :
    (if v i = 1 then X i else 1 - X i : MvPolynomial (Fin n) (ZMod 2)).vars ⊆ {i} := by
  by_cases hvi : v i = 1
  · simp [hvi, MvPolynomial.vars_X]
  · simp [hvi]

theorem isMultilinear_mleIndicator (v : Fin n → ZMod 2) :
    IsMultilinear (mleIndicator v) := by
  rw [mleIndicator]
  refine isMultilinear_prod_of_pairwise_disjoint Finset.univ
    (fun i : Fin n => (if v i = 1 then X i else 1 - X i : MvPolynomial (Fin n) (ZMod 2))) ?_ ?_ ?_
  · intro i
    by_cases hvi : v i = 1
    · simpa [hvi] using isMultilinear_X i
    · have hXi : IsMultilinear (X i : MvPolynomial (Fin n) (ZMod 2)) := isMultilinear_X i
      have hone : IsMultilinear (1 : MvPolynomial (Fin n) (ZMod 2)) := isMultilinear_C 1
      have hplus : IsMultilinear (1 + X i : MvPolynomial (Fin n) (ZMod 2)) :=
        isMultilinear_add hone hXi
      -- 1 - X i = 1 + X i over 𝔽₂
      have hsub : (1 - X i : MvPolynomial (Fin n) (ZMod 2)) = 1 + X i := by
        ext m
        have hcoef : coeff m (-(X i : MvPolynomial (Fin n) (ZMod 2))) = coeff m (X i : MvPolynomial (Fin n) (ZMod 2)) := by
          rw [coeff_neg]
          have hneg : ∀ x : ZMod 2, -x = x := by
            intro x; fin_cases x <;> decide
          exact hneg _
        simp [sub_eq_add_neg, hcoef, add_comm]
      simpa [hvi, hsub] using hplus
  · intro i
    exact vars_of_factor v i
  · intro i hi j hj hij
    have hi_vars : (if v i = 1 then X i else 1 - X i : MvPolynomial (Fin n) (ZMod 2)).vars ⊆ {i} :=
      vars_of_factor v i
    have hj_vars : (if v j = 1 then X j else 1 - X j : MvPolynomial (Fin n) (ZMod 2)).vars ⊆ {j} :=
      vars_of_factor v j
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hai' : a = i := Finset.mem_singleton.mp (hi_vars hai)
    have haj' : a = j := Finset.mem_singleton.mp (hj_vars haj)
    exact hij (hai'.symm.trans haj')

theorem eval_mleIndicator (v w : Fin n → ZMod 2) :
    eval w (mleIndicator v) = if w = v then 1 else 0 := by
  rw [mleIndicator, eval_prod]
  by_cases h : w = v
  · rw [if_pos h]
    rw [← Finset.prod_const_one]
    apply Finset.prod_congr rfl
    intro i hi
    have hwi : w i = v i := by rw [h]
    by_cases hvi : v i = 1
    · simp [hwi, hvi]
    · have hvi0 : v i = 0 := by
        rcases zmod2_eq_zero_or_one (v i) with hv | hv
        · exact hv
        · exfalso; exact hvi hv
      simp [hwi, hvi0]
  · rw [if_neg h]
    have hne : ∃ i, w i ≠ v i := by
      by_contra h2; apply h; funext i; by_contra hi; exact h2 ⟨i, hi⟩
    rcases hne with ⟨i, hwi⟩
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases hvi : v i = 1
    · have hwi1 : w i ≠ 1 := by simpa [hvi] using hwi
      have hw0 : w i = 0 := by
        rcases zmod2_eq_zero_or_one (w i) with hw | hw
        · exact hw
        · exfalso; exact hwi1 hw
      simp [hvi, hw0]
    · have hvi0 : v i = 0 := by
        rcases zmod2_eq_zero_or_one (v i) with hv | hv
        · exact hv
        · exfalso; exact hvi hv
      have hw1 : w i = 1 := by
        rcases zmod2_eq_zero_or_one (w i) with hw | hw
        · exfalso; apply hwi; simp [hvi0, hw]
        · exact hw
      simp [hvi0, hw1]

/-- The multilinear extension of f. -/
def mle (f : (Fin n → ZMod 2) → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) :=
  ∑ v : Fin n → ZMod 2, C (f v) * mleIndicator v

theorem eval_mle (f : (Fin n → ZMod 2) → ZMod 2) (w : Fin n → ZMod 2) :
    eval w (mle f) = f w := by
  rw [mle, eval_sum]
  simp [eval_mleIndicator, Finset.sum_ite_eq]

theorem isMultilinear_mle (f : (Fin n → ZMod 2) → ZMod 2) :
    IsMultilinear (mle f) := by
  rw [mle]
  refine Finset.induction_on (Finset.univ : Finset (Fin n → ZMod 2)) ?_ ?_
  · simpa using isMultilinear_C (0 : ZMod 2)
  · intro v s hv ih
    rw [Finset.sum_insert hv]
    refine isMultilinear_add ?_ ih
    simpa [MvPolynomial.smul_eq_C_mul] using isMultilinear_smul (f v) (isMultilinear_mleIndicator v)

end MLEOverBinary

-- ============================================================================
-- Section 4: Subset basis and Moebius transform (ANF over 𝔽₂)
-- ============================================================================
--
-- The subset monomials χ_S = ∏_{i∈S} x_i form a basis for the space of
-- multilinear polynomials.  Evaluating χ_S at the characteristic vector of T
-- gives 1 exactly when S ⊆ T, so the change of basis from "values on the
-- hypercube" to "ANF coefficients" is the Moebius inversion on the boolean
-- lattice.  Over 𝔽₂ the coefficient of χ_S is the sum of the values f(1_T)
-- over all T ⊆ S, and this reconstructs f.

section SubsetBasis
variable {n : ℕ}

/-- The characteristic function of a subset S. -/
def charFn (S : Finset (Fin n)) : Fin n → ZMod 2 := fun i => if i ∈ S then 1 else 0

-- Evaluating the subset monomial at a characteristic vector: 1 iff S ⊆ T.
theorem eval_charFn_subsetMonomial (S T : Finset (Fin n)) :
    eval (charFn T) (subsetMonomial S) = if S ⊆ T then 1 else 0 := by
  rw [eval_subsetMonomial]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [charFn, h hi]
  · rw [if_neg h]
    rcases Finset.not_subset.mp h with ⟨i, hiS, hiT⟩
    refine Finset.prod_eq_zero hiS ?_
    simp [charFn, hiT]

-- The ANF coefficient of the subset monomial: the Moebius transform.
def mleCoef (f : (Fin n → ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ T ∈ S.powerset, f (charFn T)

-- The support of a boolean vector: the coordinates equal to 1.
def supportOf (w : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i = 1

-- A boolean vector's evaluation of a subset monomial: 1 iff S is contained in
-- the support.
theorem eval_bool_subsetMonomial (S : Finset (Fin n)) (w : Fin n → ZMod 2) :
    eval w (subsetMonomial S) = if S ⊆ supportOf w then 1 else 0 := by
  rw [eval_subsetMonomial, supportOf]
  by_cases h : S ⊆ (Finset.univ.filter fun i => w i = 1)
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hi' : i ∈ Finset.univ.filter (fun i => w i = 1) := h hi
    have hiw : w i = 1 := (Finset.mem_filter.mp hi').2
    simp [hiw]
  · rw [if_neg h]
    rcases Finset.not_subset.mp h with ⟨i, hiS, hiT⟩
    refine Finset.prod_eq_zero hiS ?_
    have hnot : i ∉ Finset.univ.filter (fun i => w i = 1) := hiT
    have hwi : w i ≠ 1 := by
      intro hwi; apply hnot; simp [hwi]
    rcases zmod2_eq_zero_or_one (w i) with hw | hw
    · simp [hw]
    · exfalso; exact hwi hw

-- The Moebius inversion on the boolean lattice: for any function on subsets,
--   Σ_{S⊆A} Σ_{T⊆S} f(T) = f(A)   over 𝔽₂.
-- Each T contributes to exactly the S with T⊆S⊆A, and there are 2^{|A|-|T|}
-- of those, which is 1 mod 2 only for T = A.  The proof goes by induction on
-- A, splitting the powerset of `insert i A` into the subsets not containing i
-- and those containing i, which cancel over 𝔽₂.

lemma sum_powerset_insert (i : Fin n) (S : Finset (Fin n)) (hi : i ∉ S)
    (f : Finset (Fin n) → ZMod 2) :
    (∑ T ∈ (insert i S).powerset, f T) = (∑ T ∈ S.powerset, f T) + (∑ T ∈ S.powerset, f (insert i T)) := by
  have hinj : Set.InjOn (insert i) (S.powerset : Set (Finset (Fin n))) := by
    intro T hT U hU hTU
    have hTle : T ⊆ S := Finset.mem_powerset.mp hT
    have hUle : U ⊆ S := Finset.mem_powerset.mp hU
    have hTie : i ∉ T := fun h => hi (hTle h)
    have hUie : i ∉ U := fun h => hi (hUle h)
    calc
      T = (insert i T).erase i := by rw [Finset.erase_insert hTie]
      _ = (insert i U).erase i := by rw [hTU]
      _ = U := by rw [Finset.erase_insert hUie]
  have hdisj : Disjoint (S.powerset) ((S.powerset).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro T hT hT'
    rcases Finset.mem_image.mp hT' with ⟨U, hU, hTU⟩
    have hTle : T ⊆ S := Finset.mem_powerset.mp hT
    have hiT : i ∈ T := by
      rw [← hTU]; simp
    exact (fun h => hi (hTle hiT)) hiT
  rw [Finset.powerset_insert]
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image hinj]

lemma moebius_inversion (n : ℕ) (A : Finset (Fin n)) :
    ∀ f : Finset (Fin n) → ZMod 2, ∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T = f A := by
  induction A using Finset.induction_on with
  | empty =>
      intro f; simp
  | insert i A hi ih =>
      intro f
      have hinj : Set.InjOn (insert i) (A.powerset : Set (Finset (Fin n))) := by
        intro T hT U hU hTU
        have hTle : T ⊆ A := Finset.mem_powerset.mp hT
        have hUle : U ⊆ A := Finset.mem_powerset.mp hU
        have hTie : i ∉ T := fun h => hi (hTle h)
        have hUie : i ∉ U := fun h => hi (hUle h)
        calc
          T = (insert i T).erase i := by rw [Finset.erase_insert hTie]
          _ = (insert i U).erase i := by rw [hTU]
          _ = U := by rw [Finset.erase_insert hUie]
      have hdisj : Disjoint (A.powerset) ((A.powerset).image (insert i)) := by
        apply Finset.disjoint_left.mpr
        intro T hT hT'
        rcases Finset.mem_image.mp hT' with ⟨U, hU, hTU⟩
        have hTle : T ⊆ A := Finset.mem_powerset.mp hT
        have hiT : i ∈ T := by
          rw [← hTU]; simp
        exact (fun h => hi (hTle hiT)) hiT
      have hsplit : (∑ S ∈ (insert i A).powerset, ∑ T ∈ S.powerset, f T)
          = (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T)
            + (∑ S ∈ A.powerset, ∑ T ∈ (insert i S).powerset, f T) := by
        rw [Finset.powerset_insert]
        rw [Finset.sum_union hdisj]
        rw [Finset.sum_image hinj]
      have hinner : ∀ S ∈ A.powerset, (∑ T ∈ (insert i S).powerset, f T)
          = (∑ T ∈ S.powerset, f T) + (∑ T ∈ S.powerset, f (insert i T)) := by
        intro S hS
        have hSle : S ⊆ A := Finset.mem_powerset.mp hS
        exact sum_powerset_insert i S (fun h => hi (hSle h)) f
      have hsecond : (∑ S ∈ A.powerset, ∑ T ∈ (insert i S).powerset, f T)
          = (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T)
            + (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f (insert i T)) := by
        rw [Finset.sum_congr rfl (fun S hS => hinner S hS)]
        rw [Finset.sum_add_distrib]
      calc
        ∑ S ∈ (insert i A).powerset, ∑ T ∈ S.powerset, f T
            = (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T)
              + (∑ S ∈ A.powerset, ∑ T ∈ (insert i S).powerset, f T) := hsplit
        _ = (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T)
              + ((∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T)
                 + (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f (insert i T))) := by rw [hsecond]
        _ = (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f (insert i T)) := by
          have hz : (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T) +
              (∑ S ∈ A.powerset, ∑ T ∈ S.powerset, f T) = (0 : ZMod 2) := by
            rw [← two_mul]
            simp [show (2 : ZMod 2) = 0 by decide]
          rw [← add_assoc, hz, zero_add]
        _ = f (insert i A) := ih (fun T => f (insert i T))

lemma zmod2_eq_one_of_eq_ite (x : ZMod 2) : (if x = 1 then 1 else 0) = x := by
  rcases zmod2_eq_zero_or_one x with hx | hx
  · simp [hx]
  · simp [hx]

-- The ANF identity: f is recovered from its Moebius transform.
--   f(w) = Σ_{S ⊆ supp(w)} Σ_{T⊆S} f(charFn T)   over 𝔽₂.
theorem anf_reconstruct (f : (Fin n → ZMod 2) → ZMod 2) (w : Fin n → ZMod 2) :
    f w = ∑ S : Finset (Fin n), mleCoef f S * eval w (subsetMonomial S) := by
  have hchar : charFn (supportOf w) = w := by
    funext i
    simp [charFn, supportOf, zmod2_eq_one_of_eq_ite]
  have hsum : (∑ S : Finset (Fin n), mleCoef f S * eval w (subsetMonomial S))
      = ∑ S ∈ (supportOf w).powerset, mleCoef f S := by
    calc
      (∑ S : Finset (Fin n), mleCoef f S * eval w (subsetMonomial S))
          = ∑ S : Finset (Fin n), if S ⊆ supportOf w then mleCoef f S else 0 := by
            simp [eval_bool_subsetMonomial]
      _ = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S ⊆ supportOf w), mleCoef f S := by
            rw [← Finset.sum_filter]
      _ = ∑ S ∈ (supportOf w).powerset, mleCoef f S := by
            congr 1
            ext S
            simp [Finset.mem_powerset]
  calc
    f w = f (charFn (supportOf w)) := by rw [hchar]
    _ = ∑ S ∈ (supportOf w).powerset, ∑ T ∈ S.powerset, f (charFn T) := by
          exact (moebius_inversion n (supportOf w) (fun T => f (charFn T))).symm
    _ = ∑ S ∈ (supportOf w).powerset, mleCoef f S := by
          simp [mleCoef]
    _ = ∑ S : Finset (Fin n), mleCoef f S * eval w (subsetMonomial S) := hsum.symm

end SubsetBasis

-- ============================================================================
-- Section 5: Hypercube sum and vanishing
-- ============================================================================
--
-- Sumcheck reduces a sum over the hypercube to evaluations at random points.
-- The two facts needed: the MLE of f sums to the same value as f, and a
-- subset monomial sums to 1 mod 2 only when it involves all n variables.

section HypercubeSum
variable {n : ℕ}

-- The sum of the MLE over the hypercube equals the sum of f.
theorem sum_mle_eq_sum (f : (Fin n → ZMod 2) → ZMod 2) :
    ∑ x : Fin n → ZMod 2, eval x (mle f) = ∑ x : Fin n → ZMod 2, f x := by
  simp [eval_mle]

-- The sum of a subset monomial over the hypercube: 1 if S = [n], 0 otherwise.
-- This is the mod-2 consequence of the identity Σ_x χ_S(x) = 2^{n-|S|}.
theorem sum_subsetMonomial_hypercube (S : Finset (Fin n)) :
    ∑ x : Fin n → ZMod 2, eval x (subsetMonomial S) = if S = Finset.univ then 1 else 0 := by
  simp_rw [eval_subsetMonomial]
  have h1 : (∏ i : Fin n, ∑ j : ZMod 2, (if i ∈ S then j else 1))
      = ∑ x : Fin n → ZMod 2, ∏ i : Fin n, (if i ∈ S then x i else 1) := by
    calc
      (∏ i : Fin n, ∑ j : ZMod 2, (if i ∈ S then j else 1))
          = ∏ i : Fin n, ∑ j ∈ (Finset.univ : Finset (ZMod 2)), (if i ∈ S then j else 1) := by simp
      _ = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))), ∏ i : Fin n, (if i ∈ S then x i else 1) := by
          rw [Finset.prod_univ_sum]
      _ = ∑ x : Fin n → ZMod 2, ∏ i : Fin n, (if i ∈ S then x i else 1) := by simp
  have h2 : (∏ i : Fin n, ∑ j : ZMod 2, (if i ∈ S then j else 1)) = if S = Finset.univ then 1 else 0 := by
    by_cases hS : S = Finset.univ
    · subst hS
      have hfactor : ∀ i : Fin n, (∑ j : ZMod 2, (if i ∈ Finset.univ then j else 1)) = 1 := by
        intro i
        have hsum : (∑ j : ZMod 2, j) = 1 := by decide
        simp [hsum]
      rw [Finset.prod_congr rfl (fun i _ => hfactor i)]
      simp
    · rw [if_neg hS]
      have hne : ∃ i : Fin n, i ∉ S := by
        by_contra h
        apply hS
        ext i
        exact ⟨fun _ => Finset.mem_univ i, fun _ => by by_contra hi; exact h ⟨i, hi⟩⟩
      rcases hne with ⟨i, hi⟩
      have hfactor0 : (∑ j : ZMod 2, (if i ∈ S then j else 1)) = 0 := by
        simp [hi, show (2 : ZMod 2) = 0 by decide]
      have hprod : (∏ k : Fin n, ∑ j : ZMod 2, (if k ∈ S then j else 1)) =
          (∑ j : ZMod 2, (if i ∈ S then j else 1)) *
            ∏ k ∈ (Finset.univ.erase i), (∑ j : ZMod 2, (if k ∈ S then j else 1)) := by
        have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
        have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
          (fun k : Fin n => ∑ j : ZMod 2, (if k ∈ S then j else 1)) hmem
        calc
          (∏ k : Fin n, ∑ j : ZMod 2, (if k ∈ S then j else 1))
              = (∏ k ∈ Finset.univ, ∑ j : ZMod 2, (if k ∈ S then j else 1)) := by simp
          _ = ((∏ k ∈ Finset.univ.erase i, ∑ j : ZMod 2, (if k ∈ S then j else 1)) *
                (∑ j : ZMod 2, (if i ∈ S then j else 1))) := by rw [h.symm]
          _ = (∑ j : ZMod 2, (if i ∈ S then j else 1)) *
                ∏ k ∈ Finset.univ.erase i, ∑ j : ZMod 2, (if k ∈ S then j else 1) := by rw [mul_comm]
      rw [hprod, hfactor0, zero_mul]
  calc
    ∑ x : Fin n → ZMod 2, (∏ i ∈ S, x i)
        = ∑ x : Fin n → ZMod 2, ∏ i : Fin n, (if i ∈ S then x i else 1) := by simp
    _ = ∏ i : Fin n, ∑ j : ZMod 2, (if i ∈ S then j else 1) := h1.symm
    _ = if S = Finset.univ then 1 else 0 := h2

end HypercubeSum

end
