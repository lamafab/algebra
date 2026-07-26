import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

-- ============================================================================
-- Roots of Unity in Finite Fields
-- ============================================================================
--
-- Cyclic.lean develops cyclic groups in the abstract: generators, the order
-- of an element, subgroup counting, and Lagrange's theorem (g^|G| = 1 for
-- any finite group G). This file applies that machinery to the multiplicative
-- group of a finite field, where the cyclic structure is richest.
--
--   §1  Cyclicity: the units 𝔽ₚˣ of a finite field form a cyclic group of
--       order p − 1 (Galois.lean §1). By Lagrange, every nonzero element is a
--       (p−1)-st root of unity, and a subgroup of order n exists exactly when
--       n ∣ (p−1).
--   §2  Roots of unity: an n-th root of unity is x with xⁿ = 1; a primitive
--       one has order exactly n (Cyclic.lean §2). The n-th roots form the
--       cyclic subgroup ⟨ω⟩ = {1, ω, …, ωⁿ⁻¹}, which RootsInterpolation.lean §3
--       turns into the vanishing polynomial Xⁿ − 1.

notation "𝔽₅" => ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

notation "𝔽₇" => ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- ============================================================================
-- Section 1: Cyclicity of 𝔽ₚˣ
-- ============================================================================
--
-- The multiplicative group of any finite field is cyclic (Galois.lean).
-- The consequence:
--
--   𝔽ₚˣ ≅ ℤ/(p−1)ℤ.
--
-- For 𝔽₅: 𝔽₅ˣ ≅ ℤ/4ℤ (cyclic of order 4, Cyclic.lean §2).
-- For 𝔽₃: 𝔽₃ˣ ≅ ℤ/2ℤ (cyclic of order 2, Cyclic.lean §2).
-- For GF(9): GF(9)ˣ ≅ ℤ/8ℤ (cyclic of order 8).
-- In general: GF(q)ˣ ≅ ℤ/(q−1)ℤ.

instance : IsCyclic 𝔽₅ˣ := inferInstance
instance : IsCyclic 𝔽₇ˣ := inferInstance

-- By Lagrange (Cyclic.lean §3), every unit of 𝔽₅ raised to the group order
-- (4) gives 1. Equivalently every nonzero element of 𝔽₅ is a 4th root of
-- unity.
example (g : 𝔽₅ˣ) : g ^ Fintype.card 𝔽₅ˣ = 1 := pow_card_eq_one
example : (2 : 𝔽₅) ^ 4 = 1 := by decide
example : (3 : 𝔽₅) ^ 4 = 1 := by decide
example : (4 : 𝔽₅) ^ 4 = 1 := by decide

-- Likewise over 𝔽₇: 𝔽₇ˣ has order 6, so every nonzero element raised to 6
-- gives 1.
example (g : 𝔽₇ˣ) : g ^ Fintype.card 𝔽₇ˣ = 1 := pow_card_eq_one

-- ============================================================================
-- Section 2: Roots of unity
-- ============================================================================
--
-- In a field K, an n-th root of unity is an element x satisfying xⁿ = 1.
-- These elements form a subgroup of the multiplicative group Kˣ (if xⁿ = 1
-- and yⁿ = 1 then (xy)ⁿ = xⁿ·yⁿ = 1). When this subgroup is cyclic of order
-- n, a generator of it is a primitive n-th root of unity; equivalently, ω
-- is primitive if ωⁿ = 1 and ωᵏ ≠ 1 for every 0 < k < n, i.e. the order of
-- ω is exactly n (Cyclic.lean §2). The n-th roots themselves are then
--
--   {ω⁰, ω¹, …, ωⁿ⁻¹},
--
-- a cyclic subgroup of order n. Lagrange's theorem (Galois.lean §3) now
-- pays off: in a subgroup of order n every element g satisfies gⁿ = 1, so
-- the defining equation xⁿ = 1 is automatic once you know you are inside
-- an order-n cyclic subgroup.
--
-- Where do such subgroups live? The multiplicative group of a finite field
-- is cyclic (§1); a subgroup of order n exists inside 𝔽ₚˣ exactly when n
-- divides p − 1, because a cyclic group has one subgroup for each divisor
-- of its order (Cyclic.lean §3).
--
-- Examples over 𝔽₅: 𝔽₅ˣ is cyclic of order 4, so subgroups exist for
-- orders 1, 2, and 4.
--
--   * 2 and 3 are primitive 4th roots of unity: each has order 4 and
--     generates the full group 𝔽₅ˣ (Cyclic.lean §2).
--   * 4 is a non-primitive 4th root of unity: 4² = 1, so its order is 2
--     (it is a square root of unity, not a primitive 4th root).
--   * 1 is a trivial root (order 1).

-- 4 has order 2, not 4: 4¹ ≠ 1 but 4² = 1, so it generates only {1, 4}.
example : (4 : 𝔽₅) ^ 1 ≠ 1 := by decide
example : (4 : 𝔽₅) ^ 2 = 1 := by decide

-- Over 𝔽₇: 𝔽₇ˣ is cyclic of order 6, so subgroups exist for orders 1, 2,
-- 3, and 6. In particular 2 has order 3 (2¹ ≠ 1, 2² ≠ 1, 2³ = 1), so it
-- generates the cube roots of unity H = ⟨2⟩ = {1, 2, 4}. Each x ∈ H
-- satisfies x³ = 1 by Lagrange, and H is the subgroup used by the
-- vanishing-polynomial construction in RootsInterpolation.lean §3.

-- 2 is a primitive cube root of unity in 𝔽₇: order 3, not 6.
example : (2 : 𝔽₇) ^ 1 ≠ 1 := by decide
example : (2 : 𝔽₇) ^ 2 ≠ 1 := by decide
example : (2 : 𝔽₇) ^ 3 = 1 := by decide

-- The cube roots of unity: {1, 2, 4}, a cyclic subgroup of order 3.
example : ({1, 2, 4} : Finset 𝔽₇) = {2^0, 2^1, 2^2} := by decide
example : ∀ x ∈ ({1, 2, 4} : Finset 𝔽₇), x^3 = 1 := by decide

-- 4 = 2² is also a primitive cube root (the second generator of H).
example : (4 : 𝔽₇) ^ 1 ≠ 1 := by decide
example : (4 : 𝔽₇) ^ 2 ≠ 1 := by decide
example : (4 : 𝔽₇) ^ 3 = 1 := by decide
