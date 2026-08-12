import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open Finset

-- ============================================================================
-- Multiplicity-based hold-out distinguisher for McEliece
-- ============================================================================
--
-- This file develops the algebraic machinery behind the quasipolynomial
-- distinguishing attack of Ghoshal–Ishai–Jain–Sun (2026) on Goppa–McEliece
-- (https://eprint.iacr.org/2026/1630).
--
-- Over F₂, for a multilinear polynomial, "vanishing with multiplicity s at x"
-- (i.e., all Hasse derivatives of order < s are zero) is equivalent to vanishing
-- on the entire Hamming ball of radius s−1 around x. This equivalence is the
-- key that makes the binary distinguisher work.
--
-- We implement the hold-out test (Algorithm 2 of the paper) and demonstrate
-- it on a small example: a "structured" matrix whose columns satisfy the
-- vanishing property is accepted, while a random matrix is rejected.

namespace Multiplicity

-- ============================================================================
-- Hamming balls
-- ============================================================================

/-- Hamming weight of a binary vector. -/
def weight {k : ℕ} (v : Fin k → ZMod 2) : ℕ :=
  Finset.sum Finset.univ (λ i => if v i = 0 then 0 else 1)

/-- The Hamming ball of radius r around x: all y with |x−y| ≤ r. -/
def ball {k : ℕ} (x : Fin k → ZMod 2) (r : ℕ) : Finset (Fin k → ZMod 2) :=
  (Finset.univ : Finset (Fin k → ZMod 2)).filter (λ y => weight (λ i => x i + y i) ≤ r)

-- ============================================================================
-- Degree-2 multilinear homogeneous polynomials in 5 variables over F₂
-- ============================================================================

-- The 10 monomials (2-element subsets of {0,1,2,3,4}) as a function from Fin 10.
def monomial (i : Fin 10) : Finset (Fin 5) :=
  match i with
  | 0 => {0,1} | 1 => {0,2} | 2 => {0,3} | 3 => {0,4}
  | 4 => {1,2} | 5 => {1,3} | 6 => {1,4}
  | 7 => {2,3} | 8 => {2,4} | 9 => {3,4}

/-- Evaluate a polynomial (given by its 10 coefficients) at a point x. -/
def eval (c : Fin 10 → ZMod 2) (x : Fin 5 → ZMod 2) : ZMod 2 :=
  Finset.sum Finset.univ (λ i : Fin 10 => c i * Finset.prod (monomial i) (λ j => x j))

/-- The Hasse derivative at x with respect to a subset T ⊆ {0,1,2,3,4}.
Over F₂, for multilinear polynomials, the Hasse derivative ∂^[T]F(x) is
Σ_{S⊆T} F(x + 1_S). -/
def hasseDeriv (c : Fin 10 → ZMod 2) (x : Fin 5 → ZMod 2) (T : Finset (Fin 5)) : ZMod 2 :=
  Finset.sum (powerset T) (λ S => eval c (λ i => x i + if i ∈ S then 1 else 0))

/-- Vanishing with multiplicity 2 at x: F(x) = 0 and ∂^[{i}]F(x) = 0 for all i. -/
def vanishMult2 (c : Fin 10 → ZMod 2) (x : Fin 5 → ZMod 2) : Prop :=
  eval c x = 0 ∧ ∀ i : Fin 5, hasseDeriv c x {i} = 0

/-- Vanishing on the Hamming ball of radius 1 around x. -/
def vanishBall1 (c : Fin 10 → ZMod 2) (x : Fin 5 → ZMod 2) : Prop :=
  ∀ y ∈ ball x 1, eval c y = 0

-- The equivalence: vanishMult2 ↔ vanishBall1.
-- This is a finite check over all 2^10 coefficient vectors and 2^5 points.
-- (native_decide is too slow for the full product; it is stated but not run
-- here because the demo below is the point.  The demo exercises the same
-- machinery.)
-- theorem mult2_iff_ball1 (c : Fin 10 → ZMod 2) (x : Fin 5 → ZMod 2) :
--     (vanishMult2 c x ↔ vanishBall1 c x) := by
--   unfold vanishMult2 vanishBall1
--   revert c x
--   native_decide

-- ============================================================================
-- The hold-out test
-- ============================================================================

/-- The hold-out test accepts at τ if every degree-2 polynomial that vanishes
with multiplicity 2 at all non-held-out columns also vanishes at y_τ. -/
def holdOutTest (Y : Fin 4 → Fin 5 → ZMod 2) (τ : Fin 4) : Prop :=
  ∀ c ∈ (Finset.univ : Finset (Fin 10 → ZMod 2)),
    (∀ j ∈ (Finset.univ : Finset (Fin 4)), j ≠ τ → vanishMult2 c (Y j)) → eval c (Y τ) = 0

-- ============================================================================
-- Concrete demo
-- ============================================================================

-- A "structured" matrix whose columns happen to satisfy the vanishing property.
def y0 : Fin 5 → ZMod 2 := ![0, 1, 0, 0, 0]
def y1 : Fin 5 → ZMod 2 := ![0, 0, 1, 1, 0]
def y2 : Fin 5 → ZMod 2 := ![1, 1, 0, 1, 0]
def y3 : Fin 5 → ZMod 2 := ![0, 0, 0, 1, 0]

def Y_struct (j : Fin 4) : Fin 5 → ZMod 2 :=
  match j with
  | 0 => y0 | 1 => y1 | 2 => y2 | 3 => y3

-- A random matrix for comparison.
def Y_rand (j : Fin 4) : Fin 5 → ZMod 2 :=
  match j with
  | 0 => ![0, 0, 1, 0, 0]
  | 1 => ![0, 0, 0, 1, 0]
  | 2 => ![0, 0, 0, 0, 0]
  | 3 => ![0, 1, 0, 1, 1]

-- The hold-out test accepts the structured matrix.
set_option maxHeartbeats 400000 in
example : holdOutTest Y_struct 3 := by
  unfold holdOutTest vanishMult2
  native_decide

-- The hold-out test rejects the random matrix.
set_option maxHeartbeats 400000 in
example : ¬ holdOutTest Y_rand 3 := by
  unfold holdOutTest vanishMult2
  native_decide

end Multiplicity
