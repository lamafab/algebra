import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Roots, Interpolation, and Vanishing Polynomials
-- ============================================================================
--
-- Polynomials.lean builds the ring 𝔽₃[X]. This file proves three facts about
-- polynomials over a field, all variations on one theme: a low-degree
-- polynomial is pinned down by a small number of its values.
--
--   §1  Roots bound: a nonzero polynomial of degree d has at most d roots, so
--       d+1 values determine it uniquely.
--   §2  Interpolation: conversely, any d+1 values are realized by a unique
--       polynomial of degree ≤ d. With §1 this makes a polynomial and its
--       table of values interchangeable.
--   §3  Vanishing polynomial: over a finite multiplicative subgroup H of a
--       field, the polynomial vanishing exactly on H is Z_H(X) = ∏(X − h),
--       which collapses to X^|H| − 1.
--
-- All three are statements about 𝔽[X]; no cryptography enters here. They are
-- also the algebra behind the zero-knowledge proof systems in Crypto/, and
-- each section closes with a one-line pointer. The theorems are stated over a
-- general field; 𝔽₇ appears only to make things concrete.
--
-- Prerequisites: Polynomials.lean for the ring R[X], and RootsOfUnity.lean for §3,
-- where H is a cyclic subgroup of 𝔽ₚˣ.

notation "𝔽₇" => ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open Polynomial

-- ============================================================================
-- Section 1: The roots bound
-- ============================================================================
--
-- Evaluating p at a point r means substituting r for X, written p(r), or
-- `p.eval r` in Lean. A root of p is a point r where p vanishes, p(r) = 0.
--
-- The fact everything else leans on:
--
--   a nonzero polynomial of degree d has at most d roots.
--
-- Equivalently, a polynomial with more roots than its degree is the zero
-- polynomial. Each root r splits off a factor (X − r), and d+1 such factors do
-- not fit inside degree d.
--
-- Two consequences:
--
--   * Two polynomials of degree < n that agree at n distinct points are equal.
--     Their difference has degree < n yet vanishes at n points, so it has more
--     roots than its degree permits and must be zero.
--   * A nonzero polynomial of degree < n cannot vanish on an n-element set, so
--     the set contains a point where it is nonzero.
--
-- Both at once over 𝔽₇, with p = X² and q = X:
--
--   x         :  0    1    2    3    4    5    6
--   ────────────────────────────────────────────────
--   p(x) = x² :  0    1    4    2    2    4    1
--   q(x) = x  :  0    1    2    3    4    5    6
--   ────────────────────────────────────────────────
--   agree?    :  ✓    ✓    ✗    ✗    ✗    ✗    ✗
--   (p−q)(x)  :  0    0    2    6    5    6    2
--
-- The agreements sit exactly where the bottom row is zero: p and q agree
-- precisely at the roots of p − q = X² − X = X(X−1). A degree-2 polynomial has
-- at most 2 roots, so 2 agreements is the maximum; a third would force
-- p − q = 0, that is p = q. Read the other way, p − q is nonzero of degree 2,
-- so it cannot vanish on any 3-element subset of 𝔽₇.
--
-- The quantitative reading, that a uniformly random point of an N-element set
-- is a root of a fixed nonzero degree-d polynomial with probability at most
-- d/N, is the univariate Schwartz–Zippel lemma. We prove the combinatorial
-- core; that bound is what the proof systems in Crypto/ turn into soundness.

section RootsBound
variable {K : Type*} [Field K]

-- The bound itself: the multiset of roots, with multiplicity, is no larger
-- than `natDegree p`.
theorem card_roots_le_degree (p : K[X]) : Multiset.card p.roots ≤ p.natDegree :=
  Polynomial.card_roots' p

-- A nonzero `p` of degree below `s.card` cannot vanish on all of `s`, so some
-- point of `s` is a non-root.
theorem exists_nonroot {p : K[X]}
    (s : Finset K)
    (hp : p ≠ 0)
    (hdeg : p.natDegree < s.card)
  :
    ∃ x ∈ s, p.eval x ≠ 0 := by
  by_contra h
  apply hp
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p s ?_ hdeg
  intro x hx
  by_contra hx0
  exact h ⟨x, hx, hx0⟩

-- Identity: two polynomials of degree below `s.card` that agree on every point
-- of `s` are equal.
theorem eq_of_eval_eq_on {p q : K[X]}
    (s : Finset K)
    (hpq : ∀ x ∈ s, p.eval x = q.eval x)
    (hdeg : max p.natDegree q.natDegree < s.card)
  :
    p = q
  :=
    Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q s hpq hdeg

end RootsBound

-- A concrete instance over 𝔽₇. `X² + 1` and `4·X` are different polynomials of
-- degree ≤ 2, so they agree at no more than 2 points; their difference
-- `X² − 4X + 1` is nonzero, witnessed at 0.
example : ((X^2 + C 1) - (C 4 * X) : 𝔽₇[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval (0 : 𝔽₇)) h
  simp [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one] at this

-- ============================================================================
-- Section 2: Interpolation
-- ============================================================================
--
-- Section 1 says a low-degree polynomial is over-determined by its values: any
-- `n` points already pin down a polynomial of degree `< n`. Interpolation is
-- the matching existence statement:
--
--   given n nodes and n target values, there is a unique polynomial of
--   degree < n hitting each target at its node.
--
-- Together the two directions form a dictionary: over a fixed set of n nodes,
-- a polynomial of degree < n and its list of n values carry the same
-- information. Concretely over 𝔽₇, interpolate the three nodes {0, 1, 2} with
-- target values (1, 3, 2). The unique degree-< 3 polynomial through them works
-- out to 2X² + 1:
--
--   node x        :  0    1    2
--   target r(x)   :  1    3    2
--   ──────────────────────────────
--   2X² + 1 at x  :  1    3    2
--
-- Check each node: 2·0²+1 = 1, 2·1²+1 = 3, 2·2²+1 = 9 ≡ 2 (mod 7). Three
-- points fix a degree-< 3 polynomial (§1), so 2X² + 1 is the only candidate;
-- any other polynomial of degree < 3 agreeing at these nodes would equal it.
--
-- Mathlib builds the interpolant explicitly by the Lagrange formula; we expose
-- its two defining properties.

section Interpolation
variable {K : Type*} [Field K] [DecidableEq K]
open Lagrange

-- Existence: for any value table `r`, `interpolate s id r` is a degree `< #s`
-- polynomial taking the value `r i` at each node `i ∈ s`. So every table is
-- realizable; the map polynomial -> value table is surjective.
theorem eval_interpolate_node {i : K}
    (s : Finset K)
    (r : K → K)
    (hi : i ∈ s)
  :
    -- Lagrange interpolant: the degree-< #s polynomial with value `r i` at
    -- each node `i ∈ s`.
    (interpolate s id r).eval i = r i :=
  eval_interpolate_at_node r (Set.injOn_id _) hi

-- Uniqueness: any `f` of degree `< #s` is recovered by interpolating its own
-- values at `s`, so the value table is a faithful encoding of `f`. In one
-- direction: forget `f`, keep only its values on `s`, then interpolate; you
-- get `f` back, with nothing lost. So the map polynomial -> value table is
-- injective too, hence a bijection between degree-< #s polynomials and
-- value tables on `s`.
theorem eq_interpolate_self
    (s : Finset K)
    (f : K[X])
    (hf : f.degree < s.card)
  :
    f = interpolate s id (fun i => f.eval i) :=
  eq_interpolate (Set.injOn_id _) hf

end Interpolation

-- The round trip, concretely. Take `f = 2X² + 1` (degree < 3) over the nodes
-- {0,1,2}, forget it down to the value table {1, 3, 2}, then interpolate; the
-- table rebuilds `f`. That the table is a faithful encoding of `f` is exactly
-- `eq_interpolate_self`, applied here to f = 2X² + 1 and s = {0,1,2}.
open Lagrange in
example : (C 2 * X^2 + C 1 : 𝔽₇[X])
    = interpolate ({0, 1, 2} : Finset 𝔽₇) id
      (fun i => (C 2 * X^2 + C 1 : 𝔽₇[X]).eval i) := by
  refine eq_interpolate (Set.injOn_id _) ?_
  rw [show ({0, 1, 2} : Finset 𝔽₇).card = 3 from by decide]
  have hdeg : (C 2 * X^2 + C 1 : 𝔽₇[X]).natDegree = 2 := by compute_degree!
  have hne : (C 2 * X^2 + C 1 : 𝔽₇[X]) ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by decide)
  rw [degree_eq_natDegree hne, hdeg]; norm_num

-- ============================================================================
-- Section 3: The vanishing polynomial of a subgroup
-- ============================================================================
--
-- Fix a finite multiplicative subgroup H of a field, for instance the n-th
-- roots of unity H = ⟨ω⟩ = {1, ω, ω², …, ωⁿ⁻¹} generated by a primitive n-th
-- root of unity ω. This is a cyclic subgroup of 𝔽ₚˣ (RootsOfUnity.lean §2) sitting
-- inside a field. The polynomial vanishing exactly on H is its vanishing
-- polynomial, or zerofier:
--
--   Z_H(X) = ∏_{h ∈ H} (X − h).
--
-- Since the elements of H are precisely the n-th roots of unity, the product
-- collapses to a binomial:
--
--   Z_H(X) = Xⁿ − 1        (n = |H|).
--
-- One object with two faces: the product exhibits every h ∈ H as a root, and
-- Xⁿ − 1 is the compact form to compute with. Over the domain H, Z_H is the
-- universal zero:
--
--   p vanishes on all of H   ⟺   Z_H ∣ p.
--
-- That equivalence, checked at a random point via §1, is the constraint test
-- used by the proof systems in Crypto/.
--
-- Concretely over 𝔽₇: 𝔽₇ˣ is cyclic of order 6 (RootsOfUnity.lean §1) and 2 is a
-- primitive cube root of unity (RootsOfUnity.lean §2), since 2¹=2, 2²=4, 2³=8≡1. So
-- the order-3 subgroup is H = ⟨2⟩ = {1, 2, 4} and Z_H(X) = X³ − 1.

-- 2 generates the cube roots of unity; H = {1, 2, 4}.
example : (2 : 𝔽₇) ^ 3 = 1 := by decide
example : ({1, 2, 4} : Finset 𝔽₇) = {(2:𝔽₇)^0, 2^1, 2^2} := by decide

-- Each element of H is a root of Z_H = X³ − 1, the product face.
example : (X^3 - 1 : 𝔽₇[X]).eval 1 = 0 := by simp
example : (X^3 - 1 : 𝔽₇[X]).eval 2 = 0 := by simp [eval_sub, eval_pow, eval_one]; decide
example : (X^3 - 1 : 𝔽₇[X]).eval 4 = 0 := by simp [eval_sub, eval_pow, eval_one]; decide

-- The factorization Z_H = ∏(X − h), proved by the roots bound: both sides have
-- degree ≤ 3, so agreeing on all 7 points of 𝔽₇ forces equality. The pointwise
-- identity (x−1)(x−2)(x−4) = x³−1 is 𝔽₇ arithmetic, holding because
-- 1+2+4 ≡ 0 and 1·2·4 ≡ 1 (mod 7), so `decide` settles it.
theorem vanishing_factored :
    ((X - C 1) * (X - C 2) * (X - C 4) : 𝔽₇[X]) = X^3 - 1 := by
  have hpt : ∀ x : 𝔽₇, (x - 1) * (x - 2) * (x - 4) = x^3 - 1 := by decide
  apply eq_of_eval_eq_on (Finset.univ)
  · intro x _
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one]
    exact hpt x
  · have hl : ((X - C 1) * (X - C 2) * (X - C 4) : 𝔽₇[X]).natDegree ≤ 3 := by
      compute_degree!
    have hr : (X^3 - 1 : 𝔽₇[X]).natDegree ≤ 3 := by compute_degree!
    have hcard : (Finset.univ : Finset 𝔽₇).card = 7 := by decide
    rw [hcard]
    exact lt_of_le_of_lt (max_le hl hr) (by norm_num)
