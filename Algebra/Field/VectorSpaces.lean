import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic
import Algebra.Field.G8

-- ============================================================================
-- Vector Spaces: GF(p)ⁿ versus GF(pⁿ)
-- ============================================================================
--
-- Companion: Examples/G8Bits.lean retells §5 in raw bit triples, with
-- the basis as 100, 010, 001 and multiplication as shift-and-fold.
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
-- Why it matters downstream: Reed-Solomon evaluation domains and
-- interpolation need the field, specifically inverses of nonzero
-- differences of domain points (ReedSolomonReedMuller.lean §1,
-- RootsInterpolation.lean §2). The vector-space view is what gives a
-- basis, hence coordinates: an element of GF(pⁿ) as an n-tuple of GF(p)
-- coefficients.
--
-- The finite-field facts used here only as premises live elsewhere:
-- the structure theorems in Galois.lean §5, the GaloisField API in
-- BinaryFields.lean §3, characteristic-2 addition in Characteristic.lean
-- §2, and the reason reduction mod an irreducible gives a field in
-- Euclidean.lean §4. §5 runs on the hand-rolled GF(8) of G8.lean.
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

-- A basis of a vector space is a collection of vectors from which every
-- element is built as a linear combination in exactly one way:
-- existence of the combination is spanning, uniqueness is independence.
-- Mathlib records a basis as `Basis ι R M`, a linear equivalence
-- between formal combinations `ι →₀ R` and the space. The standard
-- basis has eᵢ = 1 at position i and 0 elsewhere.
#check Pi.basisFun (ZMod p) (Fin n)
-- Pi.basisFun (ZMod p) (Fin n) : Basis (Fin n) (ZMod p) (Fin n → ZMod p)

-- Over GF(2) a combination is a subset sum, so "exactly one way" can be
-- enumerated: the eight subsets of {100, 010, 001} sum to eight
-- distinct triples. The cardinality check below shows that is all of
-- GF(2)³: every triple is built, and built once.
example : [(0 : Fin 3 → ZMod 2), ![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![1, 0, 0] + ![0, 1, 0], ![1, 0, 0] + ![0, 0, 1], ![0, 1, 0] + ![0, 0, 1],
    ![1, 0, 0] + ![0, 1, 0] + ![0, 0, 1]].Nodup := by decide

-- The number of blocks is an invariant: every basis of GF(p)ⁿ has
-- exactly n vectors, the dimension of the space.
example : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by
  rw [Module.finrank_pi, Fintype.card_fin]

-- For contrast, three ways a collection fails to be a basis.
--
-- A relation among the vectors destroys uniqueness: any two of these
-- three are independent, but the three together sum to zero.
example : ![1, 1, 0] + ![0, 1, 1] + ![1, 0, 1] = (0 : Fin 3 → ZMod 2) := by decide

-- Too few vectors cannot span: two vectors reach at most p² of the p³
-- elements.
example : ¬ ∃ a b : ZMod 2, a • (![1, 0, 0] : Fin 3 → ZMod 2) + b • ![0, 1, 0] = ![0, 0, 1] := by decide

-- Too many vectors are always dependent: four vectors in a
-- 3-dimensional space, here summing to zero.
example : ![1, 0, 0] + ![0, 1, 0] + ![0, 0, 1] + ![1, 1, 1] = (0 : Fin 3 → ZMod 2) := by decide

-- A zero vector is a relation by itself: 1 · 0 = 0.
example : (1 : ZMod 2) • (0 : Fin 3 → ZMod 2) = 0 := smul_zero _

-- Equivalently, n vectors form a basis iff the matrix with them as rows
-- has nonzero determinant. The standard basis has determinant 1...
example : Matrix.det !![1, 0, 0; 0, 1, 0; 0, 0, 1] ≠ (0 : ZMod 2) := by decide

-- ...while the dependent collection above has determinant 0.
example : Matrix.det !![1, 1, 0; 0, 1, 1; 1, 0, 1] = (0 : ZMod 2) := by decide

-- The cardinality is pⁿ.
example : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide

-- Every element has additive order p: the additive group is elementary
-- abelian (Characteristic.lean §2). Here p = 2, so every vector is its own
-- negative.
example (v : Fin 3 → ZMod 2) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero _

-- ============================================================================
-- Section 2: The product ring: zero divisors, few units
-- ============================================================================
--
-- GF(p)ⁿ is also a ring, with componentwise multiplication. A field has
-- no zero divisors, and every nonzero element is a unit (Galois.lean §1);
-- the product fails both for n ≥ 2.

example : CommRing (Fin n → ZMod p) := inferInstance
example (v w : Fin n → ZMod p) (i : Fin n) : (v * w) i = v i * w i := rfl

-- Two nonzero vectors with disjoint supports multiply to zero.
example : (![1, 0, 0] : Fin 3 → ZMod 2) ≠ 0 ∧
          (![0, 1, 0] : Fin 3 → ZMod 2) ≠ 0 ∧
          (![1, 0, 0] : Fin 3 → ZMod 2) * ![0, 1, 0] = 0 := by decide

-- A vector with a zero coordinate has no inverse: the product in that
-- coordinate is always 0, never 1.
example : ¬ ∃ b : Fin 3 → ZMod 2, ![1, 0, 0] * b = 1 := by decide

-- The units are exactly the vectors with no zero coordinate, so (p−1)ⁿ of
-- pⁿ elements.
example : ∀ a : Fin 3 → ZMod 2, (∃ b, a * b = 1) ↔ ∀ i, a i ≠ 0 := by decide

-- In GF(2)³ that is a single unit out of 8 vectors: the unit set is
-- exactly {111}, and that unit is its own inverse.
example : (Finset.univ.filter fun a : Fin 3 → ZMod 2 => ∃ b, a * b = 1) = {![1, 1, 1]} := by decide
example : (![1, 1, 1] : Fin 3 → ZMod 2) * ![1, 1, 1] = 1 := by decide

-- ============================================================================
-- Section 3: GF(pⁿ), a field of the same size
-- ============================================================================
--
-- Mathlib's GF(pⁿ) is GaloisField p n, whose Field instance is
-- noncomputable (BinaryFields.lean §3), so the size facts below are
-- rewritten from GaloisField.card rather than decided.
--
-- Same cardinality as GF(2)³.
example : Nat.card (GaloisField 2 3) = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]; norm_num

-- But the unit counts differ: all 7 nonzero elements of the field are
-- units, versus a single unit out of 8 in the product (§2).
example : Nat.card (GaloisField 2 3)ˣ = 7 := by
  rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]; norm_num

-- ============================================================================
-- Section 4: Same vector space, different ring
-- ============================================================================
--
-- GF(pⁿ) is a vector space over GF(p): elements are polynomials of
-- degree < n (§5), added coefficientwise. Its dimension is n, exactly the
-- product's dimension, and its additive group is elementary abelian too
-- (Characteristic.lean §2).

#synth Module (ZMod 2) (GaloisField 2 3)
#synth FiniteDimensional (ZMod 2) (GaloisField 2 3)

example : Module.finrank (ZMod 2) (GaloisField 2 3) = 3 :=
  GaloisField.finrank 2 (by norm_num)

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
-- GF(pⁿ) consists of the same tuples as GF(p)ⁿ, with a different
-- multiplication. Read the tuple (c₀, ..., cₙ₋₁) as the polynomial
-- c₀ + c₁α + ... + cₙ₋₁αⁿ⁻¹, where α is a root of an irreducible
-- polynomial m of degree n. Addition is componentwise, exactly as in
-- the product ring. Multiplication is polynomial multiplication
-- followed by reduction mod m; the reduction mixes the coordinates,
-- which is what the product ring lacks.
--
-- The powers 1, α, ..., αⁿ⁻¹ are a basis: a relation among them would
-- be a nonzero polynomial of degree < n with α as a root, but every
-- polynomial with α as a root is a multiple of m, hence zero or of
-- degree at least n. That the quotient is a field, with inverses
-- computed by Bézout, is Euclidean.lean §4, on the same modulus
-- X³ + X + 1.
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

-- The same reduction is a relation among the powers: 1 + α + α³ = 0, so
-- {1, α, α³} is dependent and not a basis (§1). The basis powers are
-- exactly those below the degree of the minimal polynomial.
example : (1 : G8) + α + α * α * α = 0 := by decide

-- The payoff: every nonzero element acquires an inverse (all 7 of them,
-- matching §3), instead of the product's single unit.
example : ∀ x : G8, x ≠ 0 → ∃ y : G8, x * y = 1 := by decide

-- Summary: GF(p)ⁿ and GF(pⁿ) share the set of tuples, the addition, and
-- the GF(p)-scalar multiplication. They differ in the ring
-- multiplication: componentwise versus polynomial-mod-irreducible. The
-- first is never a field for n ≥ 2; the second always is.
