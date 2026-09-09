import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

-- ============================================================================
-- Characteristic of a Field
-- ============================================================================
--
-- The characteristic of a field F is the smallest positive integer p with
-- p·1 = 0 in F, or 0 if no such p exists (ℚ, ℝ). This single number controls
-- a surprising amount of downstream structure: whether the field has zero
-- divisors, how the Frobenius map behaves, and whether the squaring map is
-- 2-to-1 or 1-to-1. Those consequences are currently spread across
-- Galois.lean, BinaryFields.lean, and QuadraticResidues.lean; this file is
-- their common home.
--
--   §1  Definition and why the characteristic must be prime
--   §2  Characteristic 2: x + x = 0, x = −x, and translation orbits
--   §3  The freshman's dream and Frobenius
--   §4  The squaring dichotomy: 2-to-1 in odd characteristic, 1-to-1 in
--       characteristic 2
--
-- Cross-references: QuadraticResidues.lean for the odd-characteristic
-- squaring map (kernel {±1}, (p−1)/2 squares), BinaryFields.lean §4b for the
-- characteristic-2 squaring map (a bijection), and Multiplicity.lean §4 for
-- the polynomial shadow (X² − y splits into two roots vs one double root).

-- ============================================================================
-- Section 1: Definition, and why the characteristic must be prime
-- ============================================================================
--
-- Mathlib records the characteristic as the typeclass `CharP F p`, and
-- `CharP.cast_eq_zero_iff` says (n : F) = 0 ↔ p ∣ n: the numerals that
-- vanish are exactly the multiples of p.
example : CharP (ZMod 5) 5 := ZMod.charP 5

-- For 𝔽₃ the characteristic is 3: 1 + 1 + 1 = 0, and no smaller sum works.
example : ((3 : ℕ) : ZMod 3) = 0 := by decide
example : ((2 : ℕ) : ZMod 3) ≠ 0 := by decide

-- The characteristic counts additions of 1, not the size of the field. GF(4)
-- has four elements, yet 1 + 1 = 0 already, so its characteristic is 2, not
-- 4. In general GF(pⁿ) has characteristic p, not pⁿ.
example : CharP (GaloisField 2 2) 2 := inferInstance

-- TODO: This is too noisy; simplify
--
-- Why p must be prime. Suppose a composite n = a·b killed 1. Then
-- (a·1)·(b·1) = (a·b)·1 = n·1 = 0, with both a·1 and b·1 nonzero (since
-- a, b < n and n is minimal). That is a zero divisor, and a field has none
-- (Ideals.lean §8: a field has only the ideals {0} and itself). So no
-- composite n can be the characteristic; the smallest annihilator of 1 is
-- prime, or 0 when 1 never dies (characteristic 0, as in ℚ).
--
-- The contrapositive is the useful reading: a prime p cannot factor as
-- a·b with both a, b > 1, so no two nonzero numerals can multiply to 0.
-- This is exactly why ℤ/(p) is a field but ℤ/(6) is not (Ideals.lean §9).

-- ============================================================================
-- Section 2: Characteristic 2: x = −x and translation orbits
-- ============================================================================
--
-- In characteristic 2 the relation 2·1 = 0 scales to every element:
-- 2·x = (2·1)·x = 0, i.e. x + x = 0. So every element is its own additive
-- inverse, subtraction coincides with addition, and the numeral 2 names the
-- zero element (Galois.lean §2).
example (F : Type*) [Field F] [CharP F 2] (x : F) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

-- Hence x = −x: additive inverses are trivial.
example (F : Type*) [Field F] [CharP F 2] (x : F) : -x = x :=
  CharTwo.neg_eq x

-- Consequence for translation maps: x ↦ x + c is an involution in
-- characteristic 2 (its own inverse), because c + c = 0 absorbs the shift.
-- On GF(4) = {0, 1, ω, ω+1} the map x ↦ x + 1 pairs the elements up:
-- 0 ↔ 1 and ω ↔ ω+1.
example (x : GaloisField 2 2) : (x + 1) + 1 = x := by
  rw [add_assoc]
  have h : (1 : GaloisField 2 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [h, add_zero]

-- The general statement: in characteristic p the translation x ↦ x + c has
-- order p for c ≠ 0 (iterating gives x + k·c, and k·c = 0 iff p ∣ k), so in
-- characteristic 2 translations are exactly the involutions.
example (F : Type*) [Field F] [CharP F 2] (c : F) (x : F) :
    (x + c) + c = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero c, add_zero]

-- ============================================================================
-- Section 3: The freshman's dream and Frobenius
-- ============================================================================
--
-- In characteristic p the binomial coefficients C(p, i) for 0 < i < p are
-- all divisible by p, so the middle terms of (a + b)ᵖ vanish:
--
--   (a + b)ᵖ = aᵖ + bᵖ.
--
-- NOTE: "Binomial theorem" is the deeper theory for this.
--
-- The consequence is that the p-th power map x ↦ xᵖ *respects addition* (the
-- identity above) and multiplication ((a·b)ᵖ = aᵖ·bᵖ in any commutative ring),
-- so it is a ring homomorphism. On a finite field it is even an automorphism,
-- the Frobenius map (BinaryFields.lean §4, Galois.lean §5). The freshman's
-- dream is exactly the additivity of that homomorphism.
--
-- What "respects addition" looks like, with the squaring map sq(x) = x² as
-- the machine. Feeding it a sum means squaring the whole sum as one input,
-- and additivity says that equals squaring the parts separately and adding:
--
--   sq(a + b)   =?   sq(a) + sq(b)
--   (a + b)²    =?    a²   +   b²
--
-- Over 𝔽₂ (char 2) the machine is 0 ↦ 0, 1 ↦ 1, and it commutes with + on
-- every pair; the key case is 1 + 1 = 0:
--
--   sq(1 + 1)     =  sq(0)  =  0
--   sq(1) + sq(1) =  1 + 1  =  0    ✓ equal
--
-- Over ℤ (char 0) the same map fails, because the cross-term 2ab survives:
--
--   sq(1 + 1)     =  sq(2)  =  4
--   sq(1) + sq(1) =  1 + 1  =  2    ✗ not equal
--
-- The difference is the numeral 2: it is nonzero in ℤ (so 2ab blocks the
-- identity) but [2] = [0] in char 2 (so 2ab = 0 and the identity holds).
example (F : Type*) [Field F] (p : ℕ) [CharP F p] [Fact (Nat.Prime p)]
    (a b : F) : (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p

-- Iterating the homomorphism: the p-power maps compose, so in characteristic
-- 2 the iterate is (x + y)^{2ʳ} = x^{2ʳ} + y^{2ʳ}. Powers of p are exactly
-- the exponents with this property (Multiplicity.lean §4).
theorem add_pow_two_pow {F : Type*} [Field F] [CharP F 2] (x y : F) (r : ℕ) :
    (x + y) ^ (2 ^ r) = x ^ (2 ^ r) + y ^ (2 ^ r) := by
  induction r generalizing x y with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    exact add_pow_char (R := F) _ _ (p := 2)

-- ============================================================================
-- Section 4: The squaring dichotomy
-- ============================================================================
--
-- Whether the squaring map x ↦ x² is 2-to-1 or 1-to-1 is decided entirely by
-- the characteristic.
--
--   * Odd characteristic: x ≠ −x for x ≠ 0, and x² = y² ⟺ (x−y)(x+y) = 0 ⟺
--     x = ±y. So each square has exactly two roots, the squaring map on the
--     multiplicative group has kernel {1, −1}, and exactly half the nonzero
--     elements are squares (QuadraticResidues.lean §§1–3; §3 is where the
--     kernel-as-subgroup picture is developed). This is what prime-field FRI
--     folds along (BinaryFRI.lean).
--
--   * Characteristic 2: x = −x (§2), so the pair {x, −x} collapses to one
--     point and squaring is injective (proved below). It is a bijection on
--     the finite field, the Frobenius automorphism (§3), and there is no
--     2-to-1 halving to fold along (BinaryFields.lean §4b, BinaryFRI.lean).

-- Odd characteristic: distinct elements 2 ≠ 3 in 𝔽₅ share the square 4, and
-- 2 ≠ −2 (the kernel {1, −1} has two elements).
example : (2 : ZMod 5) ^ 2 = (3 : ZMod 5) ^ 2 := by decide
example : (1 : ZMod 5) ≠ -1 := by decide

-- TODO: Rewrite this to be less noisy
--
-- Characteristic 2: squaring is injective, x² = y² forces x = y. The proof
-- uses the freshman's dream (§3): (x − y)² = x² − y², so x² = y² gives
-- (x − y)² = 0, and a field has no nonzero nilpotents. (A nilpotent is a
-- nonzero a with aⁿ = 0 for some n; it would be a zero-divisor, which a
-- field forbids, Ideals.lean §8.) This is the same lemma as BinaryFields.lean
-- §4b, stated here for the general story.
example (F : Type*) [Field F] [CharP F 2] {x y : F} (h : x^2 = y^2) : x = y := by
  have hfresh : (x + -y)^2 = x^2 + (-y)^2 :=
    add_pow_char (R := F) (x := x) (y := -y) (p := 2)
  rw [neg_pow_two] at hfresh
  have hsub : (x - y)^2 = x^2 - y^2 := by
    rw [sub_eq_add_neg, hfresh, sub_eq_add_neg, CharTwo.neg_eq (y^2)]
  have h0 : (x - y)^2 = 0 := by rw [hsub, h, sub_self]
  have hxy : x - y = 0 := sq_eq_zero_iff.mp h0
  exact sub_eq_zero.mp hxy

-- The polynomial shadow (Multiplicity.lean §4): over an odd field X² − y has
-- two distinct roots ±x, but in characteristic 2 it factors as (X − x)², one
-- root with multiplicity 2. The dichotomy above is the field-theoretic face
-- of that factorization.
