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
-- The message is the degree-3 polynomial f(X) = X³ + X + 1 over GF(4),
-- the same f whose base-q division is worked in §3. Its Reed-Solomon
-- codeword is the evaluation table on the domain L = {0, 1, ω, ω+1}
-- (ReedSolomonReedMuller.lean §1, written here as a function rather than
-- a Polynomial so everything stays decidable).

/-- The message polynomial f(X) = X³ + X + 1. -/
def f : G4 → G4 := fun x => x * x * x + x + 1

/-- The evaluation domain, ordered. -/
def L : List G4 := [0, 1, ω, ω + 1]

/-- The codeword: evaluations of f on L. -/
def cw : G4 → G4 := f

-- The codeword really is the evaluation table of the message.
example : L.map cw = [1, 1, ω, ω + 1] := by decide

-- Distance, concretely. With deg f = 3 = |L| − 1 the code has d = 1:
-- every word on L is the table of some degree ≤ 3 polynomial, so there
-- is no redundancy to detect errors with (real FRI takes |L| ≫ deg f;
-- GF(4) has nothing larger to offer). What survives is the roots bound:
-- distinct degree ≤ 3 polynomials agree in at most 3 positions
-- (rs_agreement_card_le in ReedSolomonReedMuller.lean). The second
-- message n(X) = (ω+1)X² + (ω+1)X + 1 agrees with f in exactly 3.
def n : G4 → G4 := fun x => (ω + 1) * x * x + (ω + 1) * x + 1

example : (L.filter fun x => cw x = n x).length = 3 := by decide
example : (L.filter fun x => cw x = n x) = [0, 1, ω] := by decide

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

-- ----------------------------------------------------------------------------
-- Aside: the long division behind the fold, worked end to end
-- ----------------------------------------------------------------------------
--
-- The components p₀, p₁ folded below come from writing the committed
-- polynomial f in base q. Division theorem: given f and q ≠ 0 there are a
-- unique quotient s and remainder aX + b with deg(aX + b) < deg q such
-- that
--
--   f = s·q + (aX + b)
--
-- With deg q = 2 the remainder is always a digit aX + b. The loop below
-- produces the digits one at a time; collecting their constant parts gives
-- p₀, their X-coefficients give p₁.
--
-- Worked with f(X) = X³ + X + 1 and q(X) = X² + ωX. Minus is plus
-- throughout (char 2). Each loop cancels the leading term of the current
-- remainder; the multiplier that does so is the next term of the quotient.
--
-- Loop 1: cancel X³. Multiplier X, since X·X² = X³.
--
--   X·q = X·(X² + ωX) = X³ + ωX²
--   remainder = f − X·q = (X³ + X + 1) + (X³ + ωX²) = ωX² + X + 1
--
--   f = X·q + (ωX² + X + 1)
--        ╰─╯   ╰────┬────╯
--     quotient   remainder has degree 2: not a digit yet, loop again
--
-- Loop 2: cancel ωX². Multiplier ω, since ω·X² = ωX².
--
--   ω·q = ω·(X² + ωX) = ωX² + ω²X = ωX² + (ω+1)X     (recall: ω² = ω+1)
--   remainder = (ωX² + X + 1) + (ωX² + (ω+1)X)
--             = (ωX² + ωX²) + (1 + ω+1)X + 1         (recall: x + x = 0)
--             = ωX + 1
--
-- Degree 1 < 2, so the loop stops:
--
--   f = (X + ω)·q + (ωX + 1)
--        ╰──┬──╯     ╰───┬───╯
--      quotient      digit: a = ω, b = 1
--
-- The quotient X + ω is itself degree < 2, so it is the second digit.
-- Collecting both digits: p₀(t) = 1 + ωt from the constant parts,
-- p₁(t) = ω + t from the X-coefficients, and indeed f = p₀(q) + X·p₁(q).

/-- The folded word's value at q(x), computed from the fiber {x, x + β}:
  p₀(y) + r·p₁(y) with p₁(y) = (w(x) + w(x+β)) / β

(foldWord in BinaryFRI.lean §1b, redefined locally; inv β is 1/β). -/
def foldW (β r : G4) (w : G4 → G4) (x : G4) : G4 :=
  w x + (x + r) * (w x + w (x + β)) * inv β

-- The verifier's fold-consistency check: both representatives of a fiber
-- give the same folded value (foldWord_pair, checked on all fibers).
example : foldW ω 1 cw 0 = foldW ω 1 cw ω := by decide
example : foldW ω 1 cw 1 = foldW ω 1 cw (ω + 1) := by decide

-- The folded word on the image {0, ω+1}: with the Aside's digits
-- p₀(t) = 1 + ωt and p₁(t) = ω + t, the fold with challenge r = 1 is
-- p₀(t) + r·p₁(t) = (1 + ω) + (1 + ω)t, the values 1 + ω at t = 0 and
-- 1 at t = ω+1. One round halved the degree from 3 to 1.
example : foldW ω 1 cw 0 = 1 + ω ∧ foldW ω 1 cw 1 = 1 := by decide

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
  .node (.node (.leaf 1) (.leaf 1)) (.node (.leaf ω) (.leaf (ω + 1)))

-- The root is 1: level 1 gives h(1, 1) = 1 + 1 = 0 and
-- h(ω, ω+1) = ω² + (ω+1)³ = ω, and the root is h(0, ω) = 0 + ω³ = 1.
example : codewordTree.root hash1 = 1 := by decide

-- The honest path to the ω-leaf (directions [false, true]), computed by
-- Tree.path rather than written out by hand, verifies against the root.
example : BinaryFRI.Tree.path hash1 codewordTree [false, true] =
    some [(true, ω + 1), (false, 0)] := by decide

example : codewordTree.lookup [false, true] = some ω ∧
    BinaryFRI.verify hash1 ω [(true, ω + 1), (false, 0)] = codewordTree.root hash1 :=
  ⟨by decide, by decide⟩

-- The same opening, discharged by the general honest-path theorem
-- (verify_path, BinaryFRI.lean §3): the machinery is used as proved, not
-- just as computed.
example : BinaryFRI.verify hash1 ω [(true, ω + 1), (false, 0)] = codewordTree.root hash1 :=
  BinaryFRI.verify_path hash1 codewordTree [false, true] ω
    [(true, ω + 1), (false, 0)] (by decide) (by decide)

-- Tampering is detected: flipping the first leaf 1 ↦ 0 changes the root.
def tamperedTree : BinaryFRI.Tree G4 :=
  .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf ω) (.leaf (ω + 1)))

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
