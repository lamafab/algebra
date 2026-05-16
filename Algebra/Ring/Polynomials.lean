import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

-- ============================================================================
-- Polynomial Rings over 𝔽₃
-- ============================================================================
--
-- A polynomial ring R[X] is the ring of polynomials with coefficients in R.
-- An element p ∈ R[X] has the form:
--
--   p = a₀ + a₁·X + a₂·X² + … + aₙ·Xⁿ (aᵢ ∈ R)
--
-- and is fully determined by its coefficient sequence (a₀, a₁, …, aₙ),
-- with only finitely many aᵢ nonzero.
--
-- We work over 𝔽₃ = ZMod 3, so coefficients live in {0, 1, 2}.
-- Examples in 𝔽₃[X]:  0, 1, 2, X, X + 1, 2X + 1, X² + X + 2, …

notation "𝔽₃" => ZMod 3
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

open Polynomial

-- ============================================================================
-- Section 1: Building polynomials
-- ============================================================================
--
-- Polynomials are built from `X` (the indeterminate) and `C r` (a constant
-- coefficient lifted from R). f = X² + 2X + 1 has coefficients (1, 2, 1).

noncomputable def f : 𝔽₃[X] := X^2 + C 2 * X + C 1
noncomputable def g : 𝔽₃[X] := X + C 1

-- Coefficients wrap mod 3, like in 𝔽₃ itself:  X⁵ · 8 = X⁵ · 2.
example : (X^5 * 8 : 𝔽₃[X]) = (X^5 * 2 : 𝔽₃[X]) := by congr

-- ============================================================================
-- Section 2: Coefficients
-- ============================================================================
--
-- A polynomial Σ aᵢXⁱ is determined by its coefficients (aᵢ).
-- `.coeff i` extracts the i-th. Higher coefficients are 0 (finite support).

example : f.coeff 0 = 1 := by unfold f; simp [coeff_add, coeff_C, coeff_X_pow, coeff_one]
example : f.coeff 1 = 2 := by unfold f; simp [coeff_add, coeff_C, coeff_mul_X, coeff_X_pow, coeff_one]
example : f.coeff 2 = 1 := by unfold f; simp [coeff_add, coeff_mul_X, coeff_X_pow, coeff_one]
example : f.coeff 3 = 0 := by unfold f; simp [coeff_add, coeff_mul_X, coeff_X_pow, coeff_one]

-- ============================================================================
-- Section 3: Arithmetic (mod 3 coefficients)
-- ============================================================================

-- Multiplication: (X + 1)² = X² + 2X + 1
example : g^2 = f := by unfold f g; ring_nf; simp [map_ofNat]

-- 2X + 2X = X   because 2 + 2 = 1 in 𝔽₃
example : C (2 : 𝔽₃) * X + C (2 : 𝔽₃) * X = (X : 𝔽₃[X]) := by
  have : (2 + 2 : 𝔽₃) = 1 := by decide
  rw [← add_mul, ← map_add, this, map_one, one_mul]

-- The characteristic propagates: 3 = 0 in 𝔽₃[X]
example : (3 : 𝔽₃[X]) = 0 := by
  show C (3 : 𝔽₃) = 0
  simp [show (3 : 𝔽₃) = 0 from by decide]

-- ============================================================================
-- Section 4: Ring structure
-- ============================================================================
--
-- 𝔽₃[X] is a commutative integral domain — infinite, characteristic 3 —
-- but NOT a field (X has no inverse, just like ℤ in ℚ).

noncomputable instance : CommRing 𝔽₃[X] := inferInstance
instance : IsDomain 𝔽₃[X]   := inferInstance
instance : Infinite 𝔽₃[X]   := inferInstance
instance : CharP 𝔽₃[X] 3    := inferInstance

-- ============================================================================
-- Section 5: Degree
-- ============================================================================

example : (X^2 + C 2 * X + C 1 : 𝔽₃[X]).natDegree = 2 := by compute_degree!
example : (X + C 1 : 𝔽₃[X]).natDegree = 1 := by compute_degree!

-- ============================================================================
-- Section 6: From here to finite fields
-- ============================================================================
--
-- 𝔽₃[X] isn't a field, but quotienting by an irreducible polynomial gives
-- one. X² + 1 is irreducible over 𝔽₃ (no roots: 0²+1=1, 1²+1=2, 2²+1=2),
-- so 𝔽₃[X] / (X² + 1) is the 9-element field GF(9).
--
-- WHY ROOTS = ZEROS: the evaluation map  ev_r : k[X] → k,  p ↦ p(r)  is a
-- ring hom; its kernel is { p | p(r) = 0 } = (X - r). So "r is a root of p"
-- is a kernel-membership statement (Ideals.lean §5). Zero matters because
-- kernels are, by definition, the preimage of zero. The factor theorem
-- (r is a root ⟺ (X - r) divides p) is the principal-ideal description
-- of this kernel; the First Iso Theorem then gives k[X] / (X - r) ≅ k.
--
-- The full GF(9) construction lives in QuotientRings.lean §4.
