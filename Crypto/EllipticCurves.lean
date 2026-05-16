import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

-- ============================================================================
-- Elliptic Curves over Finite Fields
-- ============================================================================
--
-- An elliptic curve over a field K is defined by the Weierstrass equation:
--   Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆
--
-- The short form (when char ≠ 2, 3) simplifies to:
--   y² = x³ + ax + b
-- by setting a₁ = a₂ = a₃ = 0, a₄ = a, a₆ = b.
--
-- The curve must have nonzero discriminant (Δ ≠ 0) to ensure no singular
-- points (cusps or self-intersections).

notation "𝔽₅" => ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

open WeierstrassCurve Affine

-- ============================================================================
-- Section 1: Defining a curve
-- ============================================================================

-- Define y² = x³ + x + 1 over 𝔽₅
-- In general Weierstrass form: a₁=0, a₂=0, a₃=0, a₄=1, a₆=1
abbrev E : WeierstrassCurve 𝔽₅ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 1, a₆ := 1 }

-- The discriminant must be a unit (nonzero) for an elliptic curve.
-- For short Weierstrass: Δ = -16(4a³ + 27b²)
example : IsUnit E.Δ := by decide

-- So E is an elliptic curve
instance : E.IsElliptic := ⟨by decide⟩

-- ============================================================================
-- Section 2: Points on the curve
-- ============================================================================

-- A point (x, y) is on the curve if y² = x³ + x + 1 in 𝔽₅.
-- We verify this directly with arithmetic in 𝔽₅:

-- (0, 1): 1² = 0³ + 0 + 1 = 1 ✓
example : (1 : 𝔽₅) ^ 2 = (0 : 𝔽₅) ^ 3 + 0 + 1 := by decide

-- (2, 1): 1² = 2³ + 2 + 1 = 11 ≡ 1 mod 5 ✓
example : (1 : 𝔽₅) ^ 2 = (2 : 𝔽₅) ^ 3 + 2 + 1 := by decide

-- (4, 2): 2² = 4³ + 4 + 1 = 69 ≡ 4 mod 5 ✓
example : (2 : 𝔽₅) ^ 2 = (4 : 𝔽₅) ^ 3 + 4 + 1 := by decide

-- (3, 0) is NOT on the curve: 0² = 3³ + 3 + 1 = 31 ≡ 1 ≠ 0
example : (0 : 𝔽₅) ^ 2 ≠ (3 : 𝔽₅) ^ 3 + 3 + 1 := by decide

-- ============================================================================
-- Section 3: Group structure
-- ============================================================================

-- The point at infinity is the identity element of the group
#check (Point.zero : Point E.toAffine)

-- The points on E (including the point at infinity) form an abelian group
-- under the chord-and-tangent addition law.
-- Mathlib proves this satisfies all group axioms:
--   - Closure: P + Q is on the curve
--   - Associativity: (P + Q) + R = P + (Q + R)
--   - Identity: P + O = P
--   - Inverses: P + (-P) = O  where -(x,y) = (x,-y)
--   - Commutativity: P + Q = Q + P
noncomputable instance : AddCommGroup (Point E.toAffine) := inferInstance
