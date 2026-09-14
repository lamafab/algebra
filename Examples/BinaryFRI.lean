import Mathlib.Tactic
import Crypto.ZK.BinaryFRI

-- ============================================================================
-- Binary FRI, end to end on a real codeword
-- ============================================================================
--
-- Companion to Examples/Sumcheck.lean: a self-contained micro-run of binary
-- FRI (Crypto/ZK/BinaryFRI.lean) over a hand-rolled GF(8), outside the
-- Binius context. Unlike BiniusToy.lean, the committed word is a genuine
-- Reed-Solomon codeword encoding a message polynomial, and the Merkle hash
-- is nonlinear, so the binding property is demonstrated rather than
-- assumed away.
--
--   §1  GF(8), hand-rolled for decidability
--   §2  The message and its RS codeword
--   §3  One fold round on the codeword
--   §4  Merkle commitment with a nonlinear hash
--
-- Design notes. Mathlib's GaloisField and AdjoinRoot do not evaluate with
-- decide (their DecidableEq instances are classical), so GF(8) is built
-- here as triples of bits with schoolbook multiplication. The fold map and
-- folded word are redefined locally (two lines each) because instantiating
-- BinaryFRI's Field-polymorphic definitions would need a Field instance on
-- the hand-rolled type; the Merkle machinery (Tree, verify, Tree.path,
-- verify_path) needs no instances and is reused verbatim.

namespace Examples.BinaryFRI

-- ============================================================================
-- Section 1: GF(8), hand-rolled
-- ============================================================================

-- TODO: Move GF(8) into an individual helper module; this file should be
-- compact and about binary FRI.

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

end G8

/-- The primitive element. -/
notation "α" => G8.alpha

/-- α² = (0, 0, 1). -/
notation "α²" => α * α

open G8

-- Sanity: the defining relation, the unit-group order used by `inv`,
-- characteristic 2, and the inverse law.
example : α * α * α = α + 1 := by decide
example : ∀ x : G8, x ≠ 0 → x * x * x * x * x * x * x = 1 := by decide
example : ∀ x : G8, x + x = 0 := by decide
example : ∀ x : G8, inv x * x = if x = 0 then 0 else 1 := by decide

-- ============================================================================
-- Section 2: The message and its RS codeword
-- ============================================================================
--
-- The message is the degree-3 polynomial m(X) = X³ + X + 1 over GF(8),
-- the same m whose base-q division is worked in §3. Its Reed-Solomon
-- codeword is the evaluation table on the full domain L = GF(8)
-- (ReedSolomonReedMuller.lean §1, written here as a function rather than
-- a Polynomial so everything stays decidable).

/-- The message polynomial m(X) = X³ + X + 1. -/
def m : G8 → G8 := fun x => x * x * x + x + 1

/-- The evaluation domain: all of GF(8), ordered
0, 1, α, α+1, α², α²+1, α²+α, α²+α+1. -/
def L : List G8 := [0, 1, α, α + 1, α², α² + 1, α² + α, α² + α + 1]

/-- The codeword: evaluations of m on L. -/
def cw : G8 → G8 := m

-- The codeword really is the evaluation table of the message. The three
-- zeros sit at α, α², α²+α = α⁴: exactly the roots of m, since m is the
-- minimal polynomial of α over GF(2).
example : L.map cw = [1, 1, 0, α² + α, 0, α, 0, α²] := by decide

-- TODO: Briefly clarify the notation of RS [..]
--
-- Distance, concretely. With deg m = 3 and |L| = 8 the code is
-- RS [8, 4, 5]: rate 1/2 (2-to-1), and two distinct codewords agree in at
-- most n − d = 3 positions.
--
-- The bound is tight: z(X) = (α+1)X² + (α+1)X + 1 agrees with m in exactly 3
-- positions, since the difference m − z = X(X+1)(X+α) vanishes exactly at
-- {0, 1, α} (rs_agreement_card_le in ReedSolomonReedMuller.lean).
def z : G8 → G8 := fun x => (α + 1) * x * x + (α + 1) * x + 1

example : (L.filter fun x => cw x = z x) = [0, 1, α] := by decide
example : (L.filter fun x => cw x ≠ z x).length = 5 := by decide

-- ============================================================================
-- Section 3: One fold round on the codeword
-- ============================================================================
--
-- NOTE: this is Binius specific, ie. enabling a 2-to-1 Frobenius map for
-- characteristic 2 fields.
--
-- The fold map q(x) = x² + α·x. Its kernel is {0, α}, so it pairs each x
-- with x + α and halves the 8-element domain to the 4-element image
-- {0, α+1, α²+1, α²+α}.

/-- The additive fold map with β = α, local copy. -/
def qmap (x : G8) : G8 := x * x + α * x

-- The kernel is exactly {0, α}: q vanishes only at 0 and α.
example : ∀ x : G8, qmap x = 0 ↔ x = 0 ∨ x = α := by decide

-- TODO: We have a visual demonstration for this in Crypto/ZK/BinaryFRI.lean,
-- theorem foldMap_pair
--
-- The 2-to-1 collapse: q(x + α) = q(x) for every x (foldMap_pair).
example : ∀ x : G8, qmap (x + α) = qmap x := by decide

-- The fibers, concretely:
--   {0, α} ↦ 0          {1, α+1} ↦ α+1
--   {α², α²+α} ↦ α²+1   {α²+1, α²+α+1} ↦ α²+α
example : qmap 0 = 0 := by decide
example : qmap α = 0 := by decide
--
example : qmap 1 = α + 1 := by decide
example : qmap (α+1) = α + 1 := by decide
--
example : qmap α² = α² + 1 := by decide
example : qmap (α²+α) = α² + 1 := by decide
--
example : qmap (α² + 1) = α² + α := by decide
example : qmap (α² + α + 1) = α² + α := by decide

-- ----------------------------------------------------------------------------
-- Aside: the long division behind the fold, worked end to end
-- ----------------------------------------------------------------------------
--
-- The components p₀, p₁ folded below come from writing the committed
-- polynomial m in base q. Division theorem: given f and q ≠ 0 there are a
-- unique quotient s and remainder aX + b with deg(aX + b) < deg q such
-- that
--
--   f = s·q + (aX + b)
--
-- With deg q = 2 the remainder is always a digit aX + b. The loop below
-- produces the digits one at a time; collecting their constant parts gives
-- p₀, their X-coefficients give p₁.
--
-- TODO: Note that the m(X) polynomial is unrelated to the GF(8) quotient;
-- they just happen to be the same. Considing changing this for clarity.
--
-- Worked with the message m(X) = X³ + X + 1 and q(X) = X² + αX. Minus is
-- plus throughout (char 2). Each loop cancels the leading term of the
-- current remainder; the multiplier that does so is the next term of the
-- quotient.
--
-- Loop 1: cancel X³ of m(X). Multiplier X, since X·X² = X³.
--
--   X·q = X·(X² + αX) = X³ + αX²
--   remainder = m − X·q = (X³ + X + 1) + (X³ + αX²) = αX² + X + 1
--
--   m = X·q + (αX² + X + 1)
--        ╰─╯   ╰────┬────╯
--     quotient   remainder has degree 2: not a digit yet, loop again
--
-- Loop 2: cancel αX². Multiplier α, since α·X² = αX².
--
--   α·q = α·(X² + αX) = αX² + α²X
--   remainder = (αX² + X + 1) + (αX² + α²X)
--             = (αX² + αX²) + (1 + α²)X + 1       (recall: x + x = 0)
--             = (α² + 1)X + 1
--
-- Degree 1 < 2, so the loop stops:
--
--   m = (X + α)·q + ((α² + 1)X + 1)
--        ╰──┬──╯      ╰─────┬─────╯
--      quotient        digit: a = (α² + 1), b = 1
--
-- NOTE: (α² + 1) is an element/scalar inside GF(8) and has degree 1.
--
-- From the division to the fold. On the fiber {x, x + α} over
-- y = q(x), the factor q evaluates to the scalar y and X stays as the
-- fiber coordinate. Marking the remainder as digit 0 and the quotient
-- as digit 1, with aᵢ the X-coefficient and bᵢ the constant:
--
--   m = (X + α)·q + ((α² + 1)X + 1)
--        │   │    │   │          │
--        a₁  b₁   y   a₀         b₀
--
--   m(x) = (b₀ + b₁·y) + x·(a₀ + a₁·y) = p₀(y) + x·p₁(y)
--          ╰────┬────╯     ╰────┬────╯
--          p₀(t) = 1 + αt    p₁(t) = (α² + 1) + t
--
-- foldW evaluates this fiber line at the challenge r instead of at x:
--
--   p₀(y) + r·p₁(y)    with slope    p₁(y) = (w(x) + w(x+α)) / α
--
-- The slope is recovered from the two fiber values alone: w(x) and
-- w(x+α) differ by exactly α·p₁(y).
--
-- The quotient X + α is itself degree < 2, so it is the second digit.
-- Collecting digits: p₀(t) = 1 + αt from the constant parts,
-- p₁(t) = (α² + 1) + t from the X-coefficients. Both forms are checked
-- below: the division (X + α)·q + ((α² + 1)X + 1) and the fiber-line
-- evaluation p₀(y) + x·p₁(y) at y = q(x), each equal to m(x).
--
-- foldW below is this division read fiber by fiber. On {x, x + α}
-- over y = q(x), the decomposition is the line p₀(y) + X·p₁(y); its
-- slope p₁(y) = (w(x) + w(x+α)) / α comes from the two fiber values.
-- foldW evaluates that line at X = r, in point-slope form anchored at
-- (x, w(x)): w x + (x + r)·slope = p₀(y) + r·p₁(y). The challenge r
-- is the verifier's random choice, revealed after commitment, so the
-- prover cannot pre-arrange a bad fiber whose error line passes
-- through r.

-- Demonstration, the two forms of m:
--
--   m = (X + α)·q + ((α² + 1)X + 1)     the division
--     = (1 + α·q) + X·((α² + 1) + q)    the digits collected
--         ╰──┬──╯     ╰─────┬──────╯
--           p₀(q)          p₁(q)
--
-- Both expand to X·q + α·q + (α² + 1)X + 1.
def m₁ : G8 → G8 := fun x => (x + α) * qmap x + ((α² + 1) * x + 1)

/-- The digit form (1 + α·q) + X·((α²+1) + q) with the two roles of X
separated: x is the fiber point (it determines q), t the fiber
coordinate. m₂ x x is the digit form of m; m₂ r x is its fold at
challenge r. -/
def m₂ (t x : G8) : G8 := (1 + α * qmap x) + t * ((α² + 1) + qmap x)

example : ∀ x : G8, m x = m₁ x := by decide
example : ∀ x : G8, m₁ x = m₂ x x := by decide

/-- The folded word's value at q(x), computed from the fiber {x, x + α}:
  p₀(y) + r·p₁(y) with p₁(y) = (w(x) + w(x+α)) / α

(foldWord in BinaryFRI.lean §1b with β = α, redefined locally; inv α is 1/α). -/
def foldW (r : G8) (w : G8 → G8) (x : G8) : G8 :=
  w x + (x + r) * (w x + w (x + α)) * inv α

-- foldW on the honest word is the digit form m₂ with the fiber
-- coordinate X replaced by the challenge r: at y = q(x) it returns
-- m₂ r x = p₀(y) + r·p₁(y), computed from the fiber pair alone. The
-- slope recovery (w(x) + w(x+α)) / α = p₁(y) is what makes the sides agree.

example : ∀ r x : G8, foldW r cw x = m₂ r x := by decide

-- The verifier's fold-consistency check: both representatives of each
-- fiber give the same folded value (foldWord_pair, checked on all fibers).
example : foldW 1 cw 0 = foldW 1 cw α := by decide
example : foldW 1 cw 1 = foldW 1 cw (α + 1) := by decide
example : foldW 1 cw α² = foldW 1 cw (α² + α) := by decide
example : foldW 1 cw (α² + 1) = foldW 1 cw (α² + α + 1) := by decide

-- The folded word on the image {0, α+1, α²+1, α²+α}: with the Aside's
-- digits p₀(t) = 1 + αt and p₁(t) = (α²+1) + t, the fold with challenge
-- r = 1 is p₀(t) + r·p₁(t) = α² + (α+1)t, taking the values α², 1, 0,
-- α²+1 at the four image points (in the order listed). One round halved
-- the degree from 3 to 1.
example : foldW 1 cw 0 = α² ∧ foldW 1 cw 1 = 1 ∧
    foldW 1 cw α² = 0 ∧ foldW 1 cw (α² + 1) = α² + 1 := by decide

-- ============================================================================
-- Section 4: Merkle commitment with a nonlinear hash
-- ============================================================================
--
-- The codeword is committed as an 8-leaf tree over GF(8). The compression
-- function is h(a, b) = a² + b² + b; the GF(4) choice a² + b³ would be
-- vacuous here, because cubing is a bijection on GF(8) (gcd(3, 7) = 1),
-- which makes every b-fiber surjective and every edit compensatable,
-- exactly like the toy a + b of BiniusToy.lean. With b² + b the b-fiber
-- lands in a coset of the 4-element subspace {t² + t}, so half the values
-- are unreachable: binding is a real property of this hash, demonstrated
-- below.

/-- The compression function: h(a, b) = a² + b² + b. -/
def hash1 (a b : G8) : G8 := a * a + b * b + b

/-- The committed codeword tree, leaves in the order of L. -/
def codewordTree : BinaryFRI.Tree G8 :=
  .node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf (α² + α))))
        (.node (.node (.leaf 0) (.leaf α)) (.node (.leaf 0) (.leaf α²)))

-- The root is α⁵ = α²+α+1: level 1 gives h(1,1) = 1, h(0,α⁴) = α²,
-- h(0,α) = α⁴, h(0,α²) = α; level 2 gives h(1,α²) = α³, h(α⁴,α) = α²;
-- the root is h(α³, α²) = α⁶ + α⁴ + α² = α⁵.
example : codewordTree.root hash1 = α² + α + 1 := by decide

-- The honest path to the α-leaf (directions [false, true, false]),
-- computed by Tree.path rather than written out by hand, verifies against
-- the root.
example : BinaryFRI.Tree.path hash1 codewordTree [false, true, false] =
    some [(false, 0), (true, α), (false, α + 1)] := by decide

example : codewordTree.lookup [false, true, false] = some α ∧
    BinaryFRI.verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
      codewordTree.root hash1 :=
  ⟨by decide, by decide⟩

-- The same opening, discharged by the general honest-path theorem
-- (verify_path, BinaryFRI.lean §3): the machinery is used as proved, not
-- just as computed.
example : BinaryFRI.verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
    codewordTree.root hash1 :=
  BinaryFRI.verify_path hash1 codewordTree [false, true, false] α
    [(false, 0), (true, α), (false, α + 1)] (by decide) (by decide)

-- Tampering is detected: flipping the first leaf 1 ↦ 0 changes the root.
def tamperedTree : BinaryFRI.Tree G8 :=
  .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf (α² + α))))
        (.node (.node (.leaf 0) (.leaf α)) (.node (.leaf 0) (.leaf α²)))

example : tamperedTree.root hash1 ≠ codewordTree.root hash1 := by decide

-- Why the hash matters. With h₀(a, b) = a + b (the BiniusToy toy), EVERY
-- single-leaf edit x ↦ x' can be hidden by editing the sibling to
-- y' = y + x + x': the parent hash is unchanged, so the root survives and
-- the tree is not binding at all.
example : ∀ x x' y : G8, ∃ y' : G8, x' + y' = x + y :=
  fun x x' y => ⟨y + x + x', by revert x x' y; decide⟩

-- With hash1, compensation can fail: after the edit 0 ↦ 1 at the leaf
-- whose sibling value is 0, no sibling value y' restores the parent hash,
-- because hash1(1, ·) only ever outputs 1, α³, α⁵ or α⁶, never 0.
example : ∃ x x' y : G8, ∀ y' : G8, hash1 x' y' ≠ hash1 x y :=
  ⟨0, 1, 0, by decide⟩

end Examples.BinaryFRI
