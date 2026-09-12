import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Algebra.Ring.Multilinear

open Finset

noncomputable section

-- TODO: The examples/comments use coordinate values, meanwhile sumchecks
-- purpose is evaluating polynomials. So this should be updated to use
-- polynomials instead, as the current version is misleading.

-- ============================================================================
-- Sumcheck: proving a hypercube claim
-- ============================================================================
--
-- The interactive sumcheck protocol on the boolean hypercube `{0,1}ⁿ`. A
-- prover claims a statement about a multivariate polynomial p(x₀,…,x_{n-1});
-- the verifier reduces that claim to a single evaluation claim by unrolling
-- one variable per round. Each round the prover sends a univariate claim
-- gᵢ, the verifier samples a random challenge rᵢ ∈ GF(2ᵏ), and moves on to the
-- next variable. At the end the verifier asks for a single evaluation
-- p(r₁,…,rₙ) = 0.
--
-- Soundness rests on the Schwartz–Zippel lemma (Multilinear.lean):
-- a cheating prover loses with probability ≈ n·2⁻ᵏ per round, provided the
-- field is large enough. 𝔽₂ itself has too few elements to sample challenges,
-- so the protocol runs over an extension GF(2ᵏ).
--
-- Prerequisites: BinaryFields.lean (GF(2ᵏ)), Multilinear.lean (hypercube,
-- MLE, Schwartz–Zippel), RootsInterpolation.lean (univariate roots bound).
--
--   §1  Sumcheck on the boolean hypercube
--   §2  Soundness bound via Schwartz–Zippel
--   §3  Packed sumcheck sketch
-- ============================================================================

-- ============================================================================
-- Section 1: Sumcheck on the boolean hypercube
-- ============================================================================
--
-- For a polynomial p ∈ R[x₀,…,x_{n-1}], the hypercube sum is:
--
--   Σ_{x₀∈{0,1}} ⋯ Σ_{x_{n-1}∈{0,1}} p(x₀,…,x_{n-1}).
--
-- The prover claims this sum equals a target C. Each round reduces C by one
-- variable until the claim is about p at a single point. The example below
-- uses the AND gate MLE of x₀·x₁ over two variables, from Multilinear.lean.
--
-- Concretely for n = 2 and p = x₀·x₁ (AND circuit), the hypercube has four
-- corners:
--
--   (x₀,x₁) │ p(x₀,x₁)
--   ────────┼──────────
--   (0, 0)  │    0
--   (0, 1)  │    0
--   (1, 0)  │    0
--   (1, 1)  │    1
--
-- The initial claim is C = 0+0+0+1 = 1. Round 1 groups the corners by their x₀
-- coordinate:
--
--   0 slice:  p(0,0) + p(0,1) = 0 + 0 = 0  →  g₀(0) = 0
--   1 slice:  p(1,0) + p(1,1) = 0 + 1 = 1  →  g₀(1) = 1
--
-- The verifier checks g₀(0) + g₀(1) = 0 + 1 = 1 = C. After sampling r₀ = 0,
-- round 2 reduces to the single evaluation p(0,1) = 0.
--
-- The verifier receives the full gᵢ polynomial each round, not just its
-- values: the next claim's target is the evaluation gᵢ(rᵢ) at the fresh
-- challenge. Examples/BiniusToy.lean Step 2 shows this concretely (there
-- g₀ = g₁ = X over 𝔽₂).
--
-- TODO: Fold that point into this section's prose above.
--
-- TODO: Note that sumchecks verifies knowledge of the truth tables (ie. program
-- behavior), not actual execution/state-transition.

section TwoRounds

/-- The running example: the two-input AND as a function on {0,1}². -/
def andCircuit (v : Fin 2 → ZMod 2) : ZMod 2 := v 0 * v 1

-- Initial claim: the hypercube sum of the AND MLE is 1; the single point
-- (1,1) is the only nonzero evaluation (Multilinear.lean, `def mle`).
example : ∑ v : Fin 2 → ZMod 2, MvPolynomial.eval v (mle andCircuit) = 1 := by
  simp only [eval_mle]
  decide

-- Round 1. The prover sends the univariate claim
--   g₀(t) = Σ_{(t, x₁) ∈ {0,1}²} p(t, x₁).
--
-- The verifier checks g₀(0) + g₀(1) equals the initial claim. In the form of
-- partial sums over first-coordinate slices, that is exactly this equality.
example :
    (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 0}, MvPolynomial.eval v.1 (mle andCircuit)) +
    (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 1}, MvPolynomial.eval v.1 (mle andCircuit))
    =
    ∑ v : Fin 2 → ZMod 2, MvPolynomial.eval v (mle andCircuit) := by
  simp only [eval_mle]
  decide

-- Round 2. The verifier sampled r₀ = 0 at the end of round 1, fixing the
-- first coordinate (x₀ = 0). The remaining claim is about p(0, x₁) with one
-- variable free. The honest prover now sends
--
--   g₁(t) = p(0, t)
--
-- which for p = x₀·x₁ is the zero polynomial. The verifier checks
-- g₁(0) + g₁(1) = g₀(0):
--
--   g₁(0) = p(0,0) = 0
--   g₁(1) = p(0,1) = 0        ← the final single-point evaluation
--   ─────────────
--   g₁(0) + g₁(1) = 0 + 0 = 0 = g₀(0) from round 1  ✓
--
-- The verifier samples r₁ = 1 and asks for the value p(0, 1) directly (via
-- the polynomial commitment, BinaryFRI.lean). It equals 0, matching g₁(1),
-- so the verifier accepts.
--
-- TODO: Consider adding a tree for visual clarity.
example : MvPolynomial.eval ![0, 1] (mle andCircuit) = 0 := by
  rw [eval_mle]
  decide

end TwoRounds

-- ============================================================================
-- Section 2: Soundness bound via Schwartz–Zippel
-- ============================================================================
-- TODO: Improve and simplify this section
--
-- A nonzero multivariate polynomial vanishes on at most totalDegree / |S|
-- fraction of points from a product set Sⁿ (Multilinear.lean §2). Here S =
-- {0,1} and the fraction is ≤ totalDegree / 2. For a total-degree-1 claim, the
-- verifier catches a cheating prover with probability > 1/2 in each round.

-- The Schwartz–Zippel bound with S = {0,1} applied to a nonzero polynomial.
example {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) :
    (((hypercube R n).filter fun x => MvPolynomial.eval x p = 0).card : ℚ≥0)
      / ((hypercube R n).card : ℚ≥0)
    ≤ (p.totalDegree : ℚ≥0) / 2 := by
  simpa [hypercube] using MvPolynomial.schwartz_zippel_totalDegree hp ({0, 1} : Finset R)

-- With totalDegree = 1, the bound is exactly 1/2.
example {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) (hp : p ≠ 0) (hdeg : p.totalDegree = 1) :
    (((hypercube R n).filter fun x => MvPolynomial.eval x p = 0).card : ℚ≥0)
      / ((hypercube R n).card : ℚ≥0)
    ≤ 1/2 := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hp ({0, 1} : Finset R)
  simpa [hypercube, hdeg] using h

-- ============================================================================
-- Section 3: Packed sumcheck sketch
-- ============================================================================
--
-- Over 𝔽₂ a round only yields the 1/2 bound from §2: the challenge space is
-- two points, so a cheater survives a round with probability 1/2. Packing
-- fixes this: several 𝔽₂-bit values of the statement are embedded into one
-- GF(2ᵏ) element via an 𝔽₂-basis of the tower (BinaryFields.lean §5), and
-- challenges are sampled over GF(2ᵏ). Per round the soundness is then
-- totalDegree · 2⁻ᵏ instead of 1/2.
--
-- TODO: formalize the packed statement construction (alongside Binius.lean?).

end
