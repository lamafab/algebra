import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic
import Algebra.Field.G8

-- ============================================================================
-- Vector Spaces: GF(p)ⁿ versus GF(pⁿ)
-- ============================================================================
--
-- Two constructions hide behind similar notation:
--
--   GF(p)ⁿ   the product of n copies of the prime field, componentwise ops
--   GF(pⁿ)   the finite field with pⁿ elements
--
-- They have the same cardinality pⁿ and, as shown below, isomorphic
-- additive groups: both are n-dimensional vector spaces over GF(p). But
-- GF(p)ⁿ as a ring has zero divisors, while GF(pⁿ) is a field, where every
-- nonzero element has an inverse. The difference is the multiplication.
-- The field's is polynomial multiplication modulo an irreducible of
-- degree n, which mixes the coordinates; the product's is componentwise
-- and never does.
--
-- Why it matters downstream: Reed-Solomon evaluation domains, polynomial
-- interpolation, and folding all need the field (inverses of nonzero
-- differences of domain points). The vector-space view is what gives a
-- basis, hence coordinates: an element of GF(pⁿ) as an n-tuple of GF(p)
-- coefficients.
--
-- Prerequisites: Galois.lean for GF(p) and the existence of GF(pⁿ).
--
--   §1  GF(p)ⁿ as a vector space over GF(p)
--   §2  The product ring: zero divisors, few units
--   §3  GF(pⁿ): a field of the same size
--   §4  Same vector space, different ring
--   §5  Where the field multiplication comes from

variable (p n : ℕ) [Fact p.Prime]

-- ============================================================================
-- Section 1: GF(p)ⁿ as a vector space over GF(p)
-- ============================================================================
--
-- The product of n copies of GF(p), as functions Fin n → ZMod p.
-- Addition and scalar multiplication are componentwise.

example : Module (ZMod p) (Fin n → ZMod p) := inferInstance

example (c : ZMod p) (v : Fin n → ZMod p) (i : Fin n) : (c • v) i = c * v i := rfl
example (v w : Fin n → ZMod p) (i : Fin n) : (v + w) i = v i + w i := rfl

-- The standard basis: eᵢ is 1 at position i and 0 elsewhere.
#check Pi.basisFun (ZMod p) (Fin n)
-- Pi.basisFun (ZMod p) (Fin n) : Basis (Fin n) (ZMod p) (Fin n → ZMod p)

-- The dimension is n.
example : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by
  rw [Module.finrank_pi, Fintype.card_fin]

-- The cardinality is pⁿ.
example : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide

-- Every element has additive order p (the additive group is elementary
-- abelian). Here p = 2: every vector is its own negative.
example (v : Fin 3 → ZMod 2) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

-- ============================================================================
-- Section 2: The product ring: zero divisors, few units
-- ============================================================================
--
-- GF(p)ⁿ is also a ring, with componentwise multiplication.

example : CommRing (Fin n → ZMod p) := inferInstance
example (v w : Fin n → ZMod p) (i : Fin n) : (v * w) i = v i * w i := rfl

-- But for n ≥ 2 it is never a field: two nonzero vectors with disjoint
-- supports multiply to zero.
example : (![1, 0, 0] : Fin 3 → ZMod 2) ≠ 0 ∧ (![0, 1, 0] : Fin 3 → ZMod 2) ≠ 0 ∧
    (![1, 0, 0] : Fin 3 → ZMod 2) * ![0, 1, 0] = 0 := by decide

-- A vector with a zero coordinate has no inverse: the product in that
-- coordinate is always 0, never 1.
example : ¬ ∃ b : Fin 3 → ZMod 2, ![1, 0, 0] * b = 1 := by decide

-- The units are exactly the vectors with no zero coordinate, so (p−1)ⁿ of
-- pⁿ elements. In GF(2)³ that is a single unit out of 8 vectors.
example : ∀ a : Fin 3 → ZMod 2, (∃ b, a * b = 1) ↔ ∀ i, a i ≠ 0 := by decide

-- ============================================================================
-- Section 3: GF(pⁿ), a field of the same size
-- ============================================================================
--
-- Mathlib models GF(pⁿ) as GaloisField p n, the splitting field of
-- X^(pⁿ) − X over GF(p). Its Field instance is noncomputable, so the
-- structural facts here are #synth checks rather than examples.

#synth Field (GaloisField 2 3)           -- every nonzero element invertible
#synth NoZeroDivisors (GaloisField 2 3)  -- no zero divisors
#synth IsCyclic (GaloisField 2 3)ˣ       -- multiplicative group is cyclic

example : CharP (GaloisField 2 3) 2 := inferInstance

-- Same cardinality as GF(2)³.
example : Nat.card (GaloisField 2 3) = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]; norm_num

-- Concretely: inverses exist for a ≠ 0.
example (a : GaloisField 2 3) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ ha

-- A zero product forces a zero factor (compare §2).
example (a b : GaloisField 2 3) (h : a * b = 0) : a = 0 ∨ b = 0 := mul_eq_zero.mp h

-- The unit group has order pⁿ − 1 = 7: all 7 nonzero elements, versus a
-- single unit out of 8 in the product (§2).
example : Nat.card (GaloisField 2 3)ˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]; norm_num

-- ============================================================================
-- Section 4: Same vector space, different ring
-- ============================================================================
--
-- GF(pⁿ) is a vector space over GF(p): elements are polynomials of
-- degree < n (§5), added coefficientwise. Its dimension is n, exactly the
-- product's dimension, and its additive group is elementary abelian too.

#synth Module (ZMod 2) (GaloisField 2 3)
#synth FiniteDimensional (ZMod 2) (GaloisField 2 3)

example : Module.finrank (ZMod 2) (GaloisField 2 3) = 3 :=
  GaloisField.finrank 2 (by norm_num)

example (a : GaloisField 2 3) : a + a = 0 := CharTwo.add_self_eq_zero a

-- So as vector spaces, and hence as additive groups, the two are
-- isomorphic. The equivalence is noncomputable (it amounts to choosing a
-- basis), so we assert its existence rather than exhibiting it.
example : Nonempty ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] GaloisField 2 3) :=
  ⟨LinearEquiv.ofFinrankEq _ _
    (by rw [Module.finrank_pi, Fintype.card_fin, GaloisField.finrank 2 (by norm_num)])⟩

-- But they are not isomorphic as rings: a ring equivalence would preserve
-- zero divisors, and the field has none. No relabelling of the 8 triples
-- turns componentwise multiplication into field multiplication.
example : IsEmpty ((Fin 3 → ZMod 2) ≃+* GaloisField 2 3) :=
  ⟨fun e => by
    have hab : (![1, 0, 0] : Fin 3 → ZMod 2) * ![0, 1, 0] = 0 := by decide
    have h0 : e ![1, 0, 0] * e ![0, 1, 0] = 0 := by
      rw [← map_mul, hab, map_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · have he : e ![1, 0, 0] = e 0 := by rw [h, map_zero]
      exact absurd (e.injective he) (by decide)
    · have he : e ![0, 1, 0] = e 0 := by rw [h, map_zero]
      exact absurd (e.injective he) (by decide)⟩

-- ============================================================================
-- Section 5: Where the field multiplication comes from
-- ============================================================================
--
-- Concretely, GF(pⁿ) = GF(p)[α] with α a root of an irreducible m of
-- degree n. Every element is a polynomial in α of degree < n, so its
-- coefficient tuple is a vector in GF(p)ⁿ, with basis 1, α, ..., αⁿ⁻¹.
-- Addition is coefficientwise: exactly the product's addition.
-- Multiplication is polynomial multiplication followed by reduction
-- mod m, and the reduction is what mixes the coordinates.
--
-- G8.lean builds GF(8) = GF(2)[α]/(α³ + α + 1) on exactly these triples,
-- so the mechanism is visible with decide.

open G8

-- Addition is componentwise, the same as in the product GF(2)³: here the
-- two α² summands cancel in characteristic 2.
example : (1 + α² : G8) + (α + α²) = 1 + α := by decide

-- Multiplication by α shifts coefficients up one position: 1 + α ↦ α + α².
example : α * (1 + α) = α + α² := by decide

-- ...until degree n is reached, when the reduction α³ = α + 1 folds the
-- overflow back into the low coordinates. This folding is what the
-- product ring lacks.
example : α * α² = α + 1 := by decide  -- α · α² = α³ = α + 1

-- The payoff: every nonzero element acquires an inverse (all 7 of them,
-- matching §3), instead of the product's single unit.
example : ∀ x : G8, x ≠ 0 → ∃ y : G8, x * y = 1 := by decide

-- Summary: GF(p)ⁿ and GF(pⁿ) share the set of tuples, the addition, and
-- the GF(p)-scalar multiplication. They differ in the ring
-- multiplication: componentwise versus polynomial-mod-irreducible. The
-- first is never a field for n ≥ 2; the second always is.
