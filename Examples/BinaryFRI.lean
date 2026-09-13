import Mathlib.Tactic
import Crypto.ZK.BinaryFRI

-- ============================================================================
-- Binary FRI, end to end on a real codeword
-- ============================================================================
--
-- Companion to Examples/Sumcheck.lean: a self-contained micro-run of binary
-- FRI (Crypto/ZK/BinaryFRI.lean) over a hand-rolled GF(4), outside the
-- Binius context. Unlike BiniusToy.lean, the committed word is a genuine
-- Reed-Solomon codeword encoding a message polynomial, and the Merkle hash
-- is nonlinear, so the binding property is demonstrated rather than
-- assumed away.
--
--   §1  GF(4), hand-rolled for decidability
--   §2  The message and its RS codeword
--   §3  One fold round on the codeword
--   §4  Merkle commitment with a nonlinear hash
--
-- Design notes. Mathlib's GaloisField and AdjoinRoot do not evaluate with
-- decide (their DecidableEq instances are classical), so GF(4) is built
-- here as an inductive type with table arithmetic. The fold map and folded
-- word are redefined locally (two lines each) because instantiating
-- BinaryFRI's Field-polymorphic definitions would need a Field instance on
-- the hand-rolled type; the Merkle machinery (Tree, verify, Tree.path,
-- verify_path) needs no instances and is reused verbatim.

namespace Examples.BinaryFRI

-- ============================================================================
-- Section 1: GF(4), hand-rolled
-- ============================================================================

/-- GF(4) = {0, 1, ω, ω+1} with ω² = ω + 1. `u` is ω+1. -/
inductive G4 where
  | o | e | w | u
  deriving DecidableEq

namespace G4

/-- Addition is bitwise XOR on the 𝔽₂-coordinates. -/
def add : G4 → G4 → G4
  | .o, x => x
  | x, .o => x
  | .e, .e => .o
  | .w, .w => .o
  | .u, .u => .o
  | .e, .w => .u
  | .w, .e => .u
  | .e, .u => .w
  | .u, .e => .w
  | .w, .u => .e
  | .u, .w => .e

/-- Multiplication; the only nontrivial cells are ω² = ω+1, ω(ω+1) = 1,
(ω+1)² = ω. -/
def mul : G4 → G4 → G4
  | .o, _ => .o
  | _, .o => .o
  | .e, x => x
  | x, .e => x
  | .w, .w => .u
  | .w, .u => .e
  | .u, .w => .e
  | .u, .u => .w

/-- Multiplicative inverse; 0 ↦ 0 is a junk value, as usual. -/
def inv : G4 → G4
  | .o => .o
  | .e => .e
  | .w => .u
  | .u => .w

instance : Zero G4 := ⟨.o⟩
instance : One G4 := ⟨.e⟩
instance : Add G4 := ⟨add⟩
instance : Mul G4 := ⟨mul⟩

instance : Fintype G4 where
  elems := {.o, .e, .w, .u}
  complete := fun x => by cases x <;> decide

end G4

/-- Read the constructors as field elements: 0, 1, ω, ω+1. -/
notation "ω" => G4.w

open G4

-- Sanity: the defining relation, its consequences, and characteristic 2.
example : ω * ω = ω + 1 := by decide      -- ω² = ω+1
example : ω * (ω + 1) = 1 := by decide    -- ω(ω+1) = ω² + ω = 1; read backwards, ω⁻¹ = ω+1 (the `inv` table)
example : ∀ x : G4, x + x = 0 := by decide
example : ∀ x : G4, inv x * x = if x = 0 then 0 else 1 := by decide

-- ============================================================================
-- Section 2: The message and its RS codeword
-- ============================================================================
--
-- The message is the degree-1 polynomial m(X) = X + 1 over GF(4). Its
-- Reed-Solomon codeword is the evaluation table on the domain
-- L = {0, 1, ω, ω+1} (ReedSolomonReedMuller.lean §1, written here as a
-- function rather than a Polynomial so everything stays decidable).

/-- The message polynomial m(X) = X + 1. -/
def m : G4 → G4 := fun x => x + 1

/-- The evaluation domain, ordered. -/
def L : List G4 := [0, 1, ω, ω + 1]

/-- The codeword: evaluations of m on L. -/
def cw : G4 → G4 := m

-- The codeword really is the evaluation table of the message.
example : L.map cw = [1, 0, ω + 1, ω] := by decide

-- Distance, concretely. A second message n(X) = ωX has codeword
-- [0, ω, ω+1, 1]; it agrees with cw in exactly 1 = d − 1 positions
-- (d = 2), the maximum the roots bound allows for distinct degree < 2
-- polynomials (rs_agreement_card_le in ReedSolomonReedMuller.lean).
def n : G4 → G4 := fun x => ω * x

example : (L.filter fun x => cw x = n x).length = 1 := by decide
example : (L.filter fun x => cw x = n x) = [ω] := by decide

-- ============================================================================
-- Section 3: One fold round on the codeword
-- ============================================================================
--
-- TODO: Note that this is Binius specific, ie. enabling a 2-to-1 Frobenius
-- map for characteristic 2 fields.
--
-- The fold map q(x) = x² + ω·x with β = ω (foldMap in BinaryFRI.lean §1,
-- redefined locally). Its kernel is {0, ω}, so it pairs each x with x + ω
-- and halves the domain {0, 1, ω, ω+1} to the image {0, ω+1}.

/-- The additive fold map, local copy. -/
def qmap (β x : G4) : G4 := x * x + β * x

-- The kernel is exactly {0, ω}: q vanishes only at 0 and β.
example : ∀ x : G4, qmap ω x = 0 ↔ x = 0 ∨ x = ω := by decide

-- TODO: We have a visual demonstration for this in Crypto/ZK/BinaryFRI.lean,
-- theorem foldMap_pair
--
-- The 2-to-1 collapse: q(x + ω) = q(x) for every x (foldMap_pair).
example : ∀ x : G4, qmap ω (x + ω) = qmap ω x := by decide

-- The fibers, concretely:
--   {0, ω} ↦ 0    (q(0) = 0, q(ω) = ω² + ω² = 0)
--   {1, ω+1} ↦ ω+1 (q(1) = 1 + ω, q(ω+1) = (ω+1)² + ω(ω+1) = ω + 1)
example : qmap ω 0 = 0 ∧ qmap ω ω = 0 ∧ qmap ω 1 = ω + 1 ∧ qmap ω (ω + 1) = ω + 1 := by
  decide

/-- The folded word's value at q(x), computed from the fiber {x, x + β}:
p₀(y) + r·p₁(y) with p₁(y) = (w(x) + w(x+β)) / β (foldWord in
BinaryFRI.lean §1b, redefined locally; inv β is 1/β). -/
def foldW (β r : G4) (w : G4 → G4) (x : G4) : G4 :=
  w x + (x + r) * (w x + w (x + β)) * inv β

-- The verifier's fold-consistency check: both representatives of a fiber
-- give the same folded value (foldWord_pair, checked on all fibers).
example : foldW ω 1 cw 0 = foldW ω 1 cw ω := by decide
example : foldW ω 1 cw 1 = foldW ω 1 cw (ω + 1) := by decide

-- And the folded word is the constant 0 on the image {0, ω+1}: the message
-- is m(X) = X + 1 = 1 + X·1, so the components are the constants p₀ = 1
-- and p₁ = 1, and the fold with challenge r = 1 gives p₀ + r·p₁ = 0
-- everywhere. One round folded a degree-1 word to a constant.
example : foldW ω 1 cw 0 = 0 ∧ foldW ω 1 cw 1 = 0 := by decide

-- ============================================================================
-- Section 4: Merkle commitment with a nonlinear hash
-- ============================================================================
--
-- The codeword is committed as a 4-leaf tree over GF(4). The compression
-- function h(a, b) = a² + b³ is nonlinear, unlike the toy a + b of
-- BiniusToy.lean, and the difference is demonstrated below: with a + b any
-- single-leaf change can be compensated by editing the sibling, while with
-- h there are uncompensatable edits. Binding is a real property of the
-- hash, not a free one.

/-- The compression function: h(a, b) = a² + b³. -/
def hash1 (a b : G4) : G4 := a * a + b * b * b

/-- The committed codeword tree, leaf order 0, 1, ω, ω+1. -/
def codewordTree : BinaryFRI.Tree G4 :=
  .node (.node (.leaf 1) (.leaf 0)) (.node (.leaf (ω + 1)) (.leaf ω))

-- The root is 0: level 1 gives h(1, 0) = 1 and h(ω+1, ω) = ω+1, and the
-- root is h(1, ω+1) = 1 + 1 = 0.
example : codewordTree.root hash1 = 0 := by decide

-- The honest path to the ω-leaf (directions [false, false]), computed by
-- Tree.path rather than written out by hand, verifies against the root.
example : BinaryFRI.Tree.path hash1 codewordTree [false, false] =
    some [(false, ω + 1), (false, 1)] := by decide

example : codewordTree.lookup [false, false] = some ω ∧
    BinaryFRI.verify hash1 ω [(false, ω + 1), (false, 1)] = codewordTree.root hash1 :=
  ⟨by decide, by decide⟩

-- The same opening, discharged by the general honest-path theorem
-- (verify_path, BinaryFRI.lean §3): the machinery is used as proved, not
-- just as computed.
example : BinaryFRI.verify hash1 ω [(false, ω + 1), (false, 1)] = codewordTree.root hash1 :=
  BinaryFRI.verify_path hash1 codewordTree [false, false] ω
    [(false, ω + 1), (false, 1)] (by decide) (by decide)

-- Tampering is detected: flipping the first leaf 1 ↦ 0 changes the root.
def tamperedTree : BinaryFRI.Tree G4 :=
  .node (.node (.leaf 0) (.leaf 0)) (.node (.leaf (ω + 1)) (.leaf ω))

example : tamperedTree.root hash1 ≠ codewordTree.root hash1 := by decide

-- Why the hash matters. With h₀(a, b) = a + b (the BiniusToy toy), EVERY
-- single-leaf edit x ↦ x' can be hidden by editing the sibling to
-- y' = y + x + x': the parent hash is unchanged, so the root survives and
-- the tree is not binding at all.
example (x x' y : G4) : ∃ y' : G4, x' + y' = x + y :=
  ⟨y + x + x', by cases x <;> cases x' <;> cases y <;> decide⟩

-- With hash1, compensation can fail: after the edit 0 ↦ ω at the leaf
-- whose sibling value is 0, no sibling value y' restores the parent hash,
-- because hash1(ω, ·) only ever outputs ω+1 or ω, never 0.
example : ∃ x x' y : G4, ∀ y' : G4, hash1 x' y' ≠ hash1 x y :=
  ⟨0, ω, 0, fun y' => by cases y' <;> decide⟩

end Examples.BinaryFRI
