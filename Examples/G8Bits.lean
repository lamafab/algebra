import Mathlib.Tactic
import Algebra.Field.G8

-- ============================================================================
-- GF(8) in raw bits: basis, XOR addition, shift-and-fold multiplication
-- ============================================================================
--
-- Companion to Field/VectorSpaces.lean §5, with every α-name replaced by
-- the bit triple it stands for. Elements are triples (b₀, b₁, b₂) of
-- bits, read as b₀ + b₁α + b₂α² (G8.lean); this file never writes α,
-- only triples, and checks everything with decide. In the comments a
-- triple (b₀, b₁, b₂) is written as the string b₀b₁b₂.
--
--   §1  The basis: 100, 010, 001
--   §2  Addition: componentwise XOR
--   §3  Multiplication by 010: shift and fold
--   §4  General multiplication and the inverse pairs
--   §5  A failing collection: 100, 010, 110
--
-- The arithmetic is G8.lean's; this file is only a presentation layer.

namespace Examples.G8Bits

/-- Field multiplication on triples. Pinning the arguments to G8 forces
the G8 instance; a bare ascribed tuple would elaborate against the
product type's pointwise Mul instead (see the note on `alpha` in
G8.lean). -/
def fmul (x y : G8) : G8 := x * y

-- ============================================================================
-- Section 1: The basis: 100, 010, 001
-- ============================================================================
--
-- The building blocks are the triples 100, 010, 001: the α-names 1, α,
-- α² of G8.lean, and also the standard basis of GF(2)³. The coincidence
-- is the definition of coordinates: any basis, written in its own
-- coordinates, looks like the standard basis.

/-- The basis blocks, as bit triples 100, 010, 001. -/
def e₀ : G8 := (1, 0, 0)
def e₁ : G8 := (0, 1, 0)
def e₂ : G8 := (0, 0, 1)

-- Over GF(2) a combination of blocks is just a subset sum.
example : e₀ + e₁ = ((1, 1, 0) : G8) := by decide
example : e₀ + e₂ = ((1, 0, 1) : G8) := by decide
example : e₁ + e₂ = ((0, 1, 1) : G8) := by decide
example : e₀ + e₁ + e₂ = ((1, 1, 1) : G8) := by decide

/-- The eight subset sums of {e₀, e₁, e₂}. -/
def basisSums : List G8 := [0, e₀, e₁, e₂, e₀ + e₁, e₀ + e₂, e₁ + e₂, e₀ + e₁ + e₂]

-- Eight subsets sum to eight different triples, and GF(8) has only eight
-- elements: every element is built exactly once. The blocks span, and no
-- element is built twice; the subset that builds an element is its
-- coordinate triple.
example : basisSums.Nodup := by decide
example : Fintype.card G8 = 8 := by decide

-- ============================================================================
-- Section 2: Addition: componentwise XOR
-- ============================================================================
--
-- Addition is XOR on each coordinate: exactly the addition of the
-- product GF(2)³ (VectorSpaces.lean §1). The field changes only the
-- multiplication.

example : ((1, 1, 0) : G8) + (0, 1, 1) = (1, 0, 1) := by decide

-- Every element is its own negative (Characteristic.lean §2).
example : ∀ x : G8, x + x = 0 := by decide

-- ============================================================================
-- Section 3: Multiplication by 010: shift and fold
-- ============================================================================
--
-- All of the field multiplication reduces to one bit rule for
-- multiplication by 010, and the rule comes from reading 010 as α:
--
--   010 · (b₀, b₁, b₂) = b₀α + b₁α² + b₂α³
--
-- so each bit moves up one slot: the shift. The bit b₂ has no slot to
-- move into; it is the coefficient of α³, and the defining equation
-- α³ + α + 1 = 0 (G8.lean) rewrites it as α³ = α + 1 = 110. A bit
-- shifted out of the top therefore re-enters as an XOR with 110 in the
-- two low slots. The pattern 110 is the modulus X³ + X + 1 with its
-- leading bit dropped.
--
-- Hardware GF(2ⁿ) multipliers are wired in exactly this way: a shift
-- register with feedback taps at the set bits of the modulus
-- (BinaryFields.lean §6).

-- The rule, checked on all eight elements.
example : ∀ b₀ b₁ b₂ : Fin 2,
    fmul (b₀, b₁, b₂) (0, 1, 0)
      = (0, b₀, b₁) + (if b₂ = 1 then ((1, 1, 0) : G8) else 0) := by decide

-- TODO: Clarify how multiplication is actually defined for GF(2)³
-- (theory in VectorSpaces.lean §5, and defined in G8.lean).
--
-- No overflow: 010 · 010 = 001 (α · α = α²).
example : fmul (0, 1, 0) (0, 1, 0) = (0, 0, 1) := by decide

-- Overflow: the shift pushes the only bit of 001 off the top, and it
-- re-enters as 110: 010 · 001 = 110 (α · α² = α³ = α + 1).
example : fmul (0, 1, 0) (0, 0, 1) = (1, 1, 0) := by decide

-- The fold is what mixes the coordinates; the product ring has nothing
-- like it. Componentwise, 100 · 010 = 000 (VectorSpaces.lean §2).
example : (![1, 0, 0] : Fin 3 → ZMod 2) * ![0, 1, 0] = 0 := by decide

-- ============================================================================
-- Section 4: General multiplication and the inverse pairs
-- ============================================================================
--
-- Distributivity forces the rest: to multiply by y, shift-fold once per
-- set bit of y and XOR the partial products. For 010 · 101, split
-- 101 = 100 ⊕ 001:
--
--   010 · 100 = 010      010 · 001 = 110      010 ⊕ 110 = 100.

example : fmul (0, 1, 0) (1, 0, 1) = (1, 0, 0) := by decide

-- The result above is 100 = 1, so 010 and 101 are inverses. Repeating
-- for all seven nonzero triples, the inverse pairs are
--
--   100↔100   010↔101   001↔111   110↔011
--
-- every nonzero triple has an inverse (VectorSpaces.lean §5), versus
-- the product ring's single unit 111.
example : fmul (0, 0, 1) (1, 1, 1) = 1 ∧ fmul (1, 1, 0) (0, 1, 1) = 1 := by decide

-- ============================================================================
-- Section 5: A failing collection: 100, 010, 110
-- ============================================================================
--
-- Not every collection of three triples is a basis (VectorSpaces.lean
-- §1). The collection {100, 010, 110} is the α-named {1, α, α³}, and it
-- fails twice over. The three blocks sum to zero, so every element is
-- built twice:
example : ((1, 0, 0) : G8) + (0, 1, 0) + (1, 1, 0) = 0 := by decide

/-- The eight subset sums of the failing collection {100, 010, 110}. -/
def failingSums : List G8 :=
  [0, (1, 0, 0), (0, 1, 0), (1, 1, 0),
   (1, 0, 0) + (0, 1, 0), (1, 0, 0) + (1, 1, 0), (0, 1, 0) + (1, 1, 0),
   (1, 0, 0) + (0, 1, 0) + (1, 1, 0)]

example : ¬ failingSums.Nodup := by decide

-- And all three blocks have a zero last bit, so every subset-sum does:
-- 001 is unreachable, the collection does not span.
example : ∀ x ∈ failingSums, x.2.2 = 0 := by decide

-- In numbers: 8 subsets, only 4 distinct sums.
example : failingSums.length = 8 ∧ failingSums.eraseDups.length = 4 := by decide

end Examples.G8Bits
