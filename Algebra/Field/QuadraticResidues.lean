import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Quadratic Residues — which elements of 𝔽_p are squares?
-- ============================================================================
--
-- In 𝔽ₚ the squaring map x ↦ x² is two-to-one (since x² = (-x)²), so only
-- HALF of the nonzero elements are hit. Those that are hit are called
-- QUADRATIC RESIDUES (QRs); the others are NON-RESIDUES (NRs).
--
-- This file answers three questions:
--   §2 — HOW MANY:   exactly (p+1)/2 squares in 𝔽ₚ (counting 0).
--                    §3 unpacks the kernel-and-quotient picture behind the
--                    count, reconciling it with Ideals.lean's "kernels =
--                    ideals" slogan.
--   §4 — WHICH ONES: Euler's criterion, a^((p-1)/2) ∈ {±1}.
--   §5 — WHICH ONES, NICELY: the Legendre symbol packages the criterion.
--
-- Application — §6 — counts points on elliptic curves. Cyclic.lean and
-- Galois.lean are the prerequisites.

notation "𝔽₅" => ZMod 5
notation "𝔽₇" => ZMod 7

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- ============================================================================
-- Section 1: The squaring map — what does it hit?
-- ============================================================================
--
-- Take every element of 𝔽ₚ and square it. The image set is, by definition,
-- the set of QUADRATIC RESIDUES (including 0).
--
-- In 𝔽₅:
--   0² = 0  ┐
--   1² = 1  │
--   2² = 4  │  image = {0, 1, 4}  (3 elements)
--   3² = 4  │  missed = {2, 3}    (the non-residues)
--   4² = 1  ┘
--
-- In 𝔽₇:
--   0² = 0,  1² = 1,  2² = 4,  3² = 2,  4² = 2,  5² = 4,  6² = 1
--   image  = {0, 1, 2, 4}  (4 elements)
--   missed = {3, 5, 6}     (non-residues)
--
-- Notice the COLLISIONS: in 𝔽₅, both 2 and 3 square to 4; both 1 and 4
-- square to 1. The map is two-to-one on nonzero inputs, because
--   x² = y² ⟺ (x - y)(x + y) = 0 ⟺ x = y or x = -y (we're in a field).

example : IsSquare (1 : 𝔽₅) := by decide
example : IsSquare (4 : 𝔽₅) := by decide
example : ¬ IsSquare (2 : 𝔽₅) := by decide
example : ¬ IsSquare (3 : 𝔽₅) := by decide

-- 0 is always a "square" — vacuously, since 0² = 0:
example : IsSquare (0 : 𝔽₅) := by decide

-- ============================================================================
-- Section 2: Counting — exactly (p+1)/2 squares
-- ============================================================================
--
-- The squaring map 𝔽ₚˣ → 𝔽ₚˣ is a group homomorphism (for p odd) with
-- kernel {1, -1}. By the First Iso Theorem (Ideals.lean §10) its image has
-- size |𝔽_pˣ| / |kernel| = (p-1)/2. Add 1 for 0 (handled separately):
--
--   #(squares in 𝔽_p) = (p-1)/2 + 1 = (p+1)/2
--
-- For p = 5: (5+1)/2 = 3 ⟹ {0, 1, 4}.  ✓
-- For p = 7: (7+1)/2 = 4 ⟹ {0, 1, 2, 4}.  ✓
--
-- Equivalently: exactly HALF of 𝔽ₚˣ is a square. This is why "non-residue"
-- is a natural concept — they exist in equal numbers to the residues.
--
-- (p = 2 is degenerate: every element is a square, since 0² = 0 and 1² = 1.)

-- The counts match for 𝔽₅ and 𝔽₇ by direct enumeration:
example : (Finset.univ.filter (fun x : 𝔽₅ => IsSquare x)).card = 3 := by decide
example : (Finset.univ.filter (fun x : 𝔽₇ => IsSquare x)).card = 4 := by decide

-- ============================================================================
-- Section 3: The kernel as a subgroup, and the quotient picture
-- ============================================================================
--
-- §2 ran the slogan "image size = domain size / kernel size" with kernel
-- {1, -1}. But Ideals.lean §5 said "kernels = ideals" — and {1, -1} is NOT
-- an ideal. Resolving this apparent conflict clarifies both pictures.
--
-- ----------------------------------------------------------------------------
-- "Kernel" is parametrized by what the hom preserves
-- ----------------------------------------------------------------------------
--
-- A kernel is the preimage of an identity. WHICH identity (and what shape
-- the kernel takes) depends on the hom's category:
--
--   Hom preserves...        "identity" is...   Kernel is a...
--   ──────────────────      ────────────────   ─────────────────────────
--   + and · (ring hom)      0                  ideal
--   ·       (mult group)    1                  subgroup of 𝔽ₚˣ
--   +       (add group)     0                  subgroup of (𝔽ₚ, +)
--   linear  (vec sp)        0                  subspace
--
-- Ideals.lean §5's slogan is implicitly about RING homs. The squaring map
-- sq : 𝔽ₚˣ → 𝔽ₚˣ is a GROUP hom, meaning it respects · but NOT +, so its
-- kernel is a multiplicative subgroup of 𝔽ₚˣ, not an ideal.

-- Sanity: sq does not preserve addition.  sq(1+1) = 4 ≠ 2 = sq(1) + sq(1).
example : ((1 : 𝔽₅) + 1) ^ 2 ≠ (1 : 𝔽₅) ^ 2 + (1 : 𝔽₅) ^ 2 := by decide

-- And {1, -1} fails every ideal axiom of 𝔽₅: it doesn't contain 0, isn't
-- closed under + (1 + (-1) = 0 escapes), and doesn't absorb · (2·1 = 2
-- escapes too). It's purely a multiplicative subgroup of 𝔽₅ˣ.

-- ----------------------------------------------------------------------------
-- The "new identity" picture, multiplicative version
-- ----------------------------------------------------------------------------
--
-- Ideals.lean §6: pick an ideal I, declare it 0, build the quotient ring R/I.
-- Same construction multiplicatively: pick a (normal) subgroup K of G,
-- declare it 1, build the quotient group G/K.
--
-- For our kernel inside 𝔽₅ˣ = {1, 2, 3, 4}, with -1 = 4:
--
--   1 · {1, 4} = {1, 4}                       ← the kernel itself
--   2 · {1, 4} = {2, 8 mod 5}  = {2, 3}
--   3 · {1, 4} = {3, 12 mod 5} = {3, 2}      same coset as 2's
--   4 · {1, 4} = {4, 16 mod 5} = {4, 1}      same as kernel
--
-- Only two distinct cosets:
--
--   [1] = {1, 4}     the squares
--   [2] = {2, 3}     the non-squares
--
-- Cayley table:
--
--     · |   [1]   [2]
--    ----------------
--    [1]|   [1]   [2]
--    [2]|   [2]   [1]      ← because 2·2 = 4 ∈ [1]
--
-- That's ℤ/2ℤ. So  𝔽₅ˣ / {±1}  ≅  ℤ/2ℤ  ≅  {+1, -1}  as groups.

-- The image of the squaring map has the same size as the quotient — the
-- First Iso Theorem cashed out as a counting check:
example : ((Finset.univ : Finset (ZMod 5)ˣ).image (· ^ 2)).card = 2 := by decide

-- ----------------------------------------------------------------------------
-- The Legendre symbol IS the quotient map
-- ----------------------------------------------------------------------------
--
-- Composing the natural projection with the iso to {±1}:
--
--      𝔽ₚˣ ──π──→ 𝔽ₚˣ / {±1} ──≅──→ {+1, -1}
--
-- sends each x to +1 if x is a square, -1 otherwise. That's exactly
-- `legendreSym p` (extended by 0 on the zero element of 𝔽ₚ — see §5).
--
-- ----------------------------------------------------------------------------
-- The pattern in one sentence
-- ----------------------------------------------------------------------------
--
-- Every quotient map collapses its kernel to the identity; what remains
-- visible afterwards is exactly the quotient.
--
--   ℤ  ──→ ℤ/5  collapses 5ℤ   to 0  ⟹ remains: 5 residue classes
--   𝔽ₚˣ ──→ ±1  collapses {±1} to 1  ⟹ remains: "are you a square?"
--
-- Same construction, different categories (ring vs multiplicative group);
-- ideals and {±1} play structurally identical roles in their worlds.

-- ============================================================================
-- Section 4: Euler's criterion — telling residues apart
-- ============================================================================
--
-- §2 told us HOW MANY squares there are. Euler tells us WHICH:
--
--   For odd prime p and a ∈ 𝔽_p with a ≠ 0:
--     a is a quadratic residue ⟺ a^((p-1)/2) = 1   in 𝔽ₚ
--
-- Why it works:
--   By Fermat (Galois.lean §3): a^(p-1) = 1.
--   So a^((p-1)/2) is a SQUARE ROOT of 1 ⟹ equals ±1.
--   The squares form a subgroup of index 2, exactly the kernel of the
--   map x ↦ x^((p-1)/2). So:
--     a is a square  ⟺  a^((p-1)/2) = +1
--     a is a non-sq  ⟺  a^((p-1)/2) = -1
--
-- For p = 5, the exponent is (5-1)/2 = 2:
--   1^2 = 1  ⟹ QR    ✓
--   2^2 = 4 = -1  ⟹ NR    ✓
--   3^2 = 4 = -1  ⟹ NR    ✓
--   4^2 = 1  ⟹ QR    ✓
--
-- Mathlib's `ZMod.euler_criterion` makes this an `Iff`. Note the exponent
-- is written `p / 2` (integer division), which equals `(p-1)/2` for odd p.

example (a : 𝔽₅) (ha : a ≠ 0) : IsSquare a ↔ a ^ (5 / 2) = 1 :=
  ZMod.euler_criterion 5 ha

-- Check the four cases in 𝔽₅:
example : (1 : 𝔽₅) ^ 2 = 1  := by decide   -- QR
example : (2 : 𝔽₅) ^ 2 = -1 := by decide   -- NR
example : (3 : 𝔽₅) ^ 2 = -1 := by decide   -- NR
example : (4 : 𝔽₅) ^ 2 = 1  := by decide   -- QR

-- Special case: when is -1 a square?  (-1)^((p-1)/2) = 1 iff (p-1)/2 even,
-- i.e. p ≡ 1 (mod 4). So -1 is a square in 𝔽₅ (5 ≡ 1) but NOT in 𝔽₇:
example : IsSquare (-1 : 𝔽₅) := by decide      -- (-1) = 4 = 2²
example : ¬ IsSquare (-1 : 𝔽₇) := by decide

-- ============================================================================
-- Section 5: The Legendre symbol
-- ============================================================================
--
-- Euler's criterion is a NUMBER (±1). Packaging it as a function ℤ → ℤ gives
-- the LEGENDRE SYMBOL:
--
--                    ⎧  0  if p ∣ a
--          ⎛ a ⎞     ⎪
--          ⎜ ─ ⎟  =  ⎨ +1  if a is a nonzero QR mod p
--          ⎝ p ⎠     ⎪
--                    ⎩ -1  if a is a NR mod p
--
-- Two properties make it useful:
--   1. MULTIPLICATIVITY:  (a·b / p) = (a/p) · (b/p).
--      Consequence: QR · QR = QR, QR · NR = NR, NR · NR = QR.
--      (The map a ↦ (a/p) is a group hom 𝔽_pˣ → {±1}, kernel = squares.)
--   2. QUADRATIC RECIPROCITY (Gauss, the celebrated theorem) relates (p/q)
--      and (q/p) — letting you compute Legendre symbols WITHOUT computing
--      p^((q-1)/2). Out of scope here; see Mathlib's
--      `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`.

-- Mathlib's `legendreSym p a` is a ℤ-valued function. Order of args matters:
-- the prime is FIRST so that `legendreSym p` is a homomorphism in `a`.
example : legendreSym 5 1 = 1  := by decide   -- 1 is a QR
example : legendreSym 5 2 = -1 := by decide   -- 2 is a NR
example : legendreSym 5 3 = -1 := by decide   -- 3 is a NR
example : legendreSym 5 4 = 1  := by decide   -- 4 is a QR
example : legendreSym 5 5 = 0  := by decide   -- 5 ≡ 0

-- Multiplicativity in action:  2 · 3 = 6 ≡ 1 (mod 5), and (1/5) = 1 = (-1)·(-1):
example : legendreSym 5 (2 * 3) = legendreSym 5 2 * legendreSym 5 3 :=
  legendreSym.mul 5 2 3

-- ============================================================================
-- Section 6: Application — counting points on elliptic curves
-- ============================================================================
--
-- For an elliptic curve y² = x³ + a·x + b over 𝔽_p, a point (x, y) exists
-- above each x iff the RHS x³ + a·x + b is a square in 𝔽_p. Counting:
--
--   * RHS = 0           ⟹ 1 point (x, 0)
--   * RHS is a nonzero QR ⟹ 2 points (x, ±y)
--   * RHS is a NR       ⟹ 0 points
--
-- Encode this with the Legendre symbol: each x contributes 1 + (RHS/p).
-- Summing over x ∈ 𝔽_p and adding 1 for the point at infinity:
--
--      #E(𝔽_p) = (p + 1) + ∑_{x ∈ 𝔽_p} ((x³ + a·x + b) / p)
--                ───────  ─────────────────────────────────────
--                 main         "error term"
--
-- HASSE'S THEOREM (1933) bounds the error term by 2·√p — i.e. the Legendre
-- sum has magnitude ≤ 2√p, despite running over p terms. That single bound
-- is what makes ECC's group sizes predictable.
--
-- Sanity for our running example E : y² = x³ + x + 1 over 𝔽₅ (which has
-- 9 points, EllipticCurves.lean §3):
--   x = 0: rhs = 1   ⟹ (1/5) = +1  ⟹ 2 points
--   x = 1: rhs = 3   ⟹ (3/5) = -1  ⟹ 0 points
--   x = 2: rhs = 11 ≡ 1 ⟹ +1     ⟹ 2 points
--   x = 3: rhs = 31 ≡ 1 ⟹ +1     ⟹ 2 points
--   x = 4: rhs = 69 ≡ 4 ⟹ +1     ⟹ 2 points
-- Sum: 5 + (+1 -1 +1 +1 +1) = 5 + 3 = 8 affine points, + O = 9.  ✓

-- TODO: prove the point-counting formula above as a theorem about
-- Σ (over x) (1 + legendreSym p (f x)) for f : 𝔽_p → 𝔽_p.
-- TODO: state Hasse's theorem from Mathlib (if/when available).
