import Mathlib.Tactic

-- ============================================================================
-- GF(8), hand-rolled for decidability
-- ============================================================================
--
-- GF(8) = GF(2)[α]/(α³ + α + 1) built as triples of bits with schoolbook
-- multiplication, so that worked examples can evaluate everything with
-- decide. Mathlib's GaloisField and AdjoinRoot do not evaluate with decide
-- (their DecidableEq instances are classical).
--
-- Used by Examples/BinaryFRI.lean.

/-- GF(8) = GF(2)[α]/(α³ + α + 1). Elements are triples (b₀, b₁, b₂),
read as b₀ + b₁α + b₂α². -/
def G8 := Fin 2 × Fin 2 × Fin 2

namespace G8

instance : Zero G8 := ⟨(0, 0, 0)⟩

/-- The multiplicative identity is (1, 0, 0); the product type's own One
instance would be (1, 1, 1), so it is defined explicitly. -/
instance : One G8 := ⟨(1, 0, 0)⟩

/-- Addition is componentwise: XOR on the three 𝔽₂-coordinates. -/
instance : Add G8 := ⟨fun x y => (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)⟩

/-- Multiplication: schoolbook in α, then reduce by α³ = α + 1 (hence
α⁴ = α² + α). cᵢ is the pre-reduction coefficient of αⁱ; α³ folds into
positions 0 and 1, α⁴ into positions 1 and 2. -/
def mul (x y : G8) : G8 :=
  let c₁ := x.1 * y.2.1 + x.2.1 * y.1
  let c₂ := x.1 * y.2.2 + x.2.1 * y.2.1 + x.2.2 * y.1
  let c₃ := x.2.1 * y.2.2 + x.2.2 * y.2.1
  let c₄ := x.2.2 * y.2.2
  (x.1 * y.1 + c₃, c₁ + c₃ + c₄, c₂ + c₄)

instance : Mul G8 := ⟨mul⟩

-- TODO: Justify this odd comment(?)
/-- Multiplicative inverse: x⁶, since x⁷ = 1 for every x ≠ 0 (the unit
group has order 7), and 0⁶ = 0 is the usual junk value. -/
def inv (x : G8) : G8 := x * x * x * x * x * x

/-- The primitive element α = (0, 1, 0), a root of X³ + X + 1. Kept as a
def (not an ascribed tuple) so that terms built from it elaborate with
type G8 and pick up the G8 instances above, not the product type's
pointwise ones. -/
def alpha : G8 := (0, 1, 0)

instance : DecidableEq G8 := inferInstanceAs (DecidableEq (Fin 2 × Fin 2 × Fin 2))
instance : Fintype G8 := inferInstanceAs (Fintype (Fin 2 × Fin 2 × Fin 2))

/-- The primitive element. Scoped so importers opt in with `open G8`;
plain notation would forbid α as a binder name downstream. -/
scoped notation "α" => G8.alpha

/-- α² = (0, 0, 1). -/
scoped notation "α²" => α * α

end G8

open G8

-- Sanity: the defining relation, the unit-group order used by `inv`,
-- characteristic 2, and the inverse law.
example : α * α * α = α + 1 := by decide
example : ∀ x : G8, x ≠ 0 → x * x * x * x * x * x * x = 1 := by decide
example : ∀ x : G8, x + x = 0 := by decide
example : ∀ x : G8, inv x * x = if x = 0 then 0 else 1 := by decide
