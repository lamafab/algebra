import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

-- ============================================================================
-- Sumcheck with a nonlinear round polynomial
-- ============================================================================
--
-- TODO: Consider removing/stripping BiniusToy.lean; hence update this comment.
--
-- A companion to the sumcheck step of Examples/BiniusToy.lean. There both
-- round polynomials came out as g(t) = t: two values determine them, and
-- the challenge r ∈ 𝔽₂ always lands on an interpolation node, so the
-- "verifier evaluates the received polynomial at r" step never becomes
-- visible. This file runs the protocol where it does become visible:
--
--   p(x₀, x₁) = x₀²·x₁ + x₀ + x₁    over ℤ/7ℤ
--
-- The variable x₀ occurs with degree 2, so the round-1 message g₀ is
-- quadratic: two values do NOT determine it, the prover must send three
-- (equivalently, the polynomial's coefficients), and the challenge r₀ = 2
-- lies outside the interpolation nodes {0, 1}, so the target value
-- v₁ = g₀(2) is genuinely new information.
--
-- TODO: Compact the following comment block:
--
-- Why three: RootsInterpolation.lean §1, the first consequence of the
-- roots bound: polynomials of degree < n agreeing at n points are equal,
-- so n = 3 points pin down g₀, and §2 gives the interpolant's existence.
-- Two points leave a one-parameter family: ĝ₀ = g₀ + c·X·(X−1) for any
-- c ∈ ℤ/7ℤ is a different quadratic agreeing with g₀ at both nodes, and
-- it still passes the verifier's check ĝ₀(0) + ĝ₀(1) = 5, because X(X−1)
-- vanishes exactly there.
--
-- The run:
--
--   claim:      Σ p over the hypercube {0,1}² = 5
--   round 1:    g₀(t) = t² + 2t + 1,  check g₀(0) + g₀(1) = 5
--   r₀ = 2:     target v₁ = g₀(2) = 2,  pin x₀ := 2
--   round 2:    g₁(t) = 5t + 2,       check g₁(0) + g₁(1) = 2 = v₁
--   r₁ = 3:     target v = g₁(3) = 3,  pin x₁ := 3
--   final:      p(2, 3) = 3, checked directly
--
-- Soundness note: a cheating prover must send ĝ₀ ≠ g₀ of degree ≤ 2 with
-- ĝ₀(0) + ĝ₀(1) = 5. Two distinct degree-2 polynomials agree on at most 2
-- points (RootsInterpolation.lean), so of the 7 possible challenges at
-- most 2 let ĝ₀ survive: the verifier catches the lie with probability
-- ≥ 5/7 in round 1 alone.

namespace Examples.Sumcheck

open MvPolynomial

/-- The statement polynomial: degree 2 in x₀, degree 1 in x₁. -/
noncomputable def p : MvPolynomial (Fin 2) (ZMod 7) := X 0 ^ 2 * X 1 + X 0 + X 1

-- ============================================================================
-- Step 0: The claim
-- ============================================================================

-- The four corners, concretely.
example : eval ![0, 0] p = 0 := by
  simp only [p, eval_add, eval_mul, eval_pow, eval_X]; decide
example : eval ![0, 1] p = 1 := by
  simp only [p, eval_add, eval_mul, eval_pow, eval_X]; decide
example : eval ![1, 0] p = 1 := by
  simp only [p, eval_add, eval_mul, eval_pow, eval_X]; decide
example : eval ![1, 1] p = 3 := by
  simp only [p, eval_add, eval_mul, eval_pow, eval_X]; decide

/-- The hypercube {0,1}² embedded in (ℤ/7ℤ)². -/
def cube : Finset (Fin 2 → ZMod 7) := {![0, 0], ![0, 1], ![1, 0], ![1, 1]}

/-- The claim: the hypercube sum is C = 5. -/
example : ∑ v ∈ cube, eval v p = 5 := by
  simp [cube, p, eval_add, eval_mul, eval_pow, eval_X]
  decide

-- ============================================================================
-- Step 1: Round 1, the quadratic message
-- ============================================================================

/-- The honest round-1 polynomial: g₀(t) = p(t,0) + p(t,1) = t² + 2t + 1. -/
noncomputable def g₀ : Polynomial (ZMod 7) :=
  Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 1

-- g₀ is quadratic: two values do not determine the message.
example : g₀.natDegree = 2 := by unfold g₀; compute_degree!

-- Its values at the interpolation nodes are the honest slice sums:
-- g₀(0) = p(0,0) + p(0,1) and g₀(1) = p(1,0) + p(1,1).
example : g₀.eval 0 = eval ![0, 0] p + eval ![0, 1] p := by
  simp only [g₀, p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, eval_add, eval_mul, eval_pow, eval_X]
  decide
example : g₀.eval 1 = eval ![1, 0] p + eval ![1, 1] p := by
  simp only [g₀, p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, eval_add, eval_mul, eval_pow, eval_X]
  decide

-- Round 1 consistency: g₀(0) + g₀(1) = 5 = C.
example : g₀.eval 0 + g₀.eval 1 = 5 := by
  simp only [g₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  decide

/-- The verifier samples r₀ = 2, outside {0, 1}. The new target v₁ = g₀(2)
is not among the values the slices provided: it is computed from the
polynomial itself. -/
example : g₀.eval 2 = 2 := by
  simp only [g₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  decide

-- Off the nodes, concretely: g₀(2) is neither g₀(0) nor g₀(1).
example : g₀.eval 2 ≠ g₀.eval 0 ∧ g₀.eval 2 ≠ g₀.eval 1 := by
  simp only [g₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  decide

-- ============================================================================
-- Step 2: Round 2, the pinned slice
-- ============================================================================

/-- The honest round-2 polynomial: g₁(t) = p(2, t) = 5t + 2. -/
noncomputable def g₁ : Polynomial (ZMod 7) := Polynomial.C 5 * Polynomial.X + Polynomial.C 2

-- g₁ is the pinned slice p(2, ·) at both interpolation nodes.
example : g₁.eval 0 = eval ![2, 0] p := by
  simp only [g₁, p, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, eval_add, eval_mul, eval_pow, eval_X]
  decide
example : g₁.eval 1 = eval ![2, 1] p := by
  simp only [g₁, p, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, eval_add, eval_mul, eval_pow, eval_X]
  decide

-- Round 2 consistency: g₁(0) + g₁(1) = 2 = v₁ = g₀(r₀).
example : g₁.eval 0 + g₁.eval 1 = g₀.eval 2 := by
  simp only [g₁, g₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  decide

/-- The verifier samples r₁ = 3, again outside {0, 1}. The reduction is
complete: the sum claim has become the single evaluation claim
p(2, 3) = 3, with v = g₁(3). -/
example : g₁.eval 3 = 3 := by
  simp only [g₁, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  decide

-- ============================================================================
-- Step 3: The final check
-- ============================================================================

/-- The end of the chain: p(2, 3) = 3 = v, checked directly against the
polynomial. In the composed protocol this value comes from opening the
polynomial commitment at r = (2, 3) instead (BiniusToy.lean Step 3). -/
example : eval ![2, 3] p = 3 := by
  simp only [p, eval_add, eval_mul, eval_pow, eval_X]; decide

end Examples.Sumcheck
