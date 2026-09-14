import Mathlib.Tactic
import Algebra.Field.G8
import Crypto.Merkle

-- ============================================================================
-- Binary FRI, end to end on a real codeword
-- ============================================================================
--
-- Companion to Examples/Sumcheck.lean: a self-contained micro-run of binary
-- FRI (Crypto/ZK/BinaryFRI.lean) over GF(8), outside the Binius context.
-- Unlike BiniusToy.lean, the committed word is a genuine Reed-Solomon
-- codeword encoding a message polynomial, and the Merkle hash is nonlinear,
-- so the binding property is demonstrated rather than assumed away.
--
--   §1  The message and its RS codeword
--   §2  One fold round on the codeword
--   §3  Merkle commitment with a nonlinear hash
--
-- Design notes. GF(8) comes from Algebra/Field/G8.lean (hand-rolled for
-- decidability). The fold map and folded word are redefined locally (two
-- lines each) because instantiating BinaryFRI's Field-polymorphic
-- definitions would need a Field instance on the hand-rolled type; the
-- Merkle machinery (Tree, verify, Tree.path, verify_path) is reused
-- verbatim from Crypto/Merkle.lean.

namespace Examples.BinaryFRI

open G8

-- ============================================================================
-- Section 1: The message and its RS codeword
-- ============================================================================
--
-- The message is the degree-3 polynomial m(X) = X³ + X + 1 over GF(8),
-- the same m whose base-q division is worked in §2. Its Reed-Solomon
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
-- Section 2: One fold round on the codeword
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
-- Division theorem: given f and q ≠ 0 there are a unique quotient s
-- and remainder aX + b with deg(aX + b) < deg q such that
--
--   f = s·q + (aX + b)
--
-- With deg q = 2 a digit has the shape aX + b, degree < 2. The loop
-- below cancels leading terms until the remainder is a digit; if the
-- quotient is not itself a digit, it is divided in turn.
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
-- The quotient X + α is itself degree < 2, so it is the second digit.
-- The loop has packaged m into its base-q digits; how they become the
-- fold is the business of foldW below.

-- ----------------------------------------------------------------------------
-- From the digits to the fold: assembling foldW
-- ----------------------------------------------------------------------------
--
-- The Aside packaged m into digits; here is what they are for. Read
-- the two digits' parts as coefficients of two polynomials p₀, p₁ in
-- a fresh variable t marking the digit position: the constant parts
-- go into p₀, the X-coefficients into p₁. On the fiber {x, x + α}
-- over y = q(x), the factor q evaluates to the scalar y and X stays
-- as the fiber coordinate; aᵢ and bᵢ mark the X-coefficient and the
-- constant of digit i:
--
--   m = (X + α)·q + ((α² + 1)X + 1)
--        │   │    │   │          │
--        a₁  b₁   y   a₀         b₀
--
--   m(x) = (b₀ + b₁·y) + x·(a₀ + a₁·y) = p₀(y) + x·p₁(y)
--          ╰────┬────╯     ╰────┬────╯
--          p₀(t) = 1 + αt    p₁(t) = (α² + 1) + t
--
-- foldW below reads this fiber line fiber by fiber: it recovers the
-- slope from the two fiber values alone, which differ by exactly
-- α·p₁(y), and evaluates the line at the challenge r instead of at x:
--
--   p₀(y) + r·p₁(y)    with slope    p₁(y) = (w(x) + w(x+α)) / α
--
-- The challenge r is the verifier's random choice, revealed after
-- commitment, so the prover cannot pre-arrange a bad fiber whose error
-- line passes through r.

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
-- Section 3: Merkle commitment with a nonlinear hash
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
def codewordTree : Merkle.Tree G8 :=
  .node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf (α² + α))))
        (.node (.node (.leaf 0) (.leaf α)) (.node (.leaf 0) (.leaf α²)))

-- The root is α⁵ = α²+α+1: level 1 gives h(1,1) = 1, h(0,α⁴) = α²,
-- h(0,α) = α⁴, h(0,α²) = α; level 2 gives h(1,α²) = α³, h(α⁴,α) = α²;
-- the root is h(α³, α²) = α⁶ + α⁴ + α² = α⁵.
example : codewordTree.root hash1 = α² + α + 1 := by decide

-- The honest path to the α-leaf (directions [false, true, false]),
-- computed by Tree.path rather than written out by hand, verifies against
-- the root.
example : Merkle.Tree.path hash1 codewordTree [false, true, false] =
    some [(false, 0), (true, α), (false, α + 1)] := by decide

example : codewordTree.lookup [false, true, false] = some α ∧
    Merkle.verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
      codewordTree.root hash1 :=
  ⟨by decide, by decide⟩

-- The same opening, discharged by the general honest-path theorem
-- (verify_path, Merkle.lean): the machinery is used as proved, not just
-- as computed.
example : Merkle.verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
    codewordTree.root hash1 :=
  Merkle.verify_path hash1 codewordTree [false, true, false] α
    [(false, 0), (true, α), (false, α + 1)] (by decide) (by decide)

-- Tampering is detected: flipping the first leaf 1 ↦ 0 changes the root.
def tamperedTree : Merkle.Tree G8 :=
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
