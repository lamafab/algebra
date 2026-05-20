import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

-- ============================================================================
-- Elliptic Curves over Finite Fields
-- ============================================================================
--
-- An elliptic curve over a field K is the set of solutions (x, y) ∈ K × K of
-- the general Weierstrass equation
--   y² + a₁·x·y + a₃ · y = x³ + a₂·x² + a₄·x + a₆
--
-- together with one extra "point at infinity" O. Over a field of char ≠ 2, 3
-- the cross terms a₁, a₂, a₃ can be eliminated, collapsing to the SHORT form:
--   y² = x³ + a·x + b
-- TODO: Demonstrate this collapse

-- 𝔽₅ has char 5, so we may use the short form here. (Char of ZMod p is p —
-- see Galois.lean §3.)
--
-- Two extras turn this set into the object cryptography cares about:
--   * a NONDEGENERACY condition (discriminant Δ ≠ 0) ruling out cusps and
--     self-intersections — §2;
--   * a GROUP LAW (chord-and-tangent) making the points into an abelian
--     group — §4.
--
-- That group is the workhorse of ECDH (§7), the elliptic-curve analog of
-- DiffieHellman.lean. Same protocol, harder discrete log, smaller keys.

notation "𝔽₅" => ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

open WeierstrassCurve Affine

-- ============================================================================
-- Section 1: Defining a curve
-- ============================================================================
--
-- We pick E : y² = x³ + x + 1 over 𝔽₅. In general Weierstrass form this is
-- a₁ = a₂ = a₃ = 0, a₄ = 1, a₆ = 1.

abbrev E : WeierstrassCurve 𝔽₅ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 1, a₆ := 1 }

-- ============================================================================
-- Section 2: The discriminant — keeping the curve smooth
-- ============================================================================
--
-- For the short form y² = x³ + a·x + b the discriminant is
--   Δ = -16 · (4a³ + 27b²).
-- TODO: Clarify where this values comes from.
--
-- An elliptic curve REQUIRES Δ ≠ 0 (equivalently, Δ is a unit). When Δ = 0
-- the cubic x³ + a·x + b has a repeated root and the curve develops a
-- singular point — a cusp or a self-intersection — where the "tangent line"
-- in §4 is no longer well-defined:
--
-- smooth                cusp (Δ=0)            node (Δ=0)
--        y²=x³+x+1               y²=x³                y²=x³+x²
--
--           __/                    /                   \  /
--          /                      /                     \/
--         |                      <                      /\
--          \__                    \                    /  \
--             \                    \                  /    \
--
-- Geometrically Δ ≠ 0 says "the curve never crosses itself or pinches" —
-- algebraically it's exactly what we need for the group law to be defined
-- at every point. Without it, addition can land on a singular point with
-- no tangent and the construction collapses.
--
-- For our curve: Δ = -16·(4·1³ + 27·1²) = -16·31 = -496 ≡ 4 (mod 5) ≠ 0.

example : IsUnit E.Δ := by decide

instance : E.IsElliptic := ⟨by decide⟩

-- ============================================================================
-- Section 3: Points on the curve
-- ============================================================================
--
-- A point (x, y) ∈ 𝔽₅ × 𝔽₅ is ON E iff y² = x³ + x + 1 holds in 𝔽₅. Squares
-- in 𝔽₅ are {0, 1, 4}, so we sweep x = 0, 1, 2, 3, 4 and check whether the
-- right-hand side lands in {0, 1, 4}. Each hit gives two y-values (±√rhs).
-- (QuadraticResidues.lean gives the general theory of which elements of
-- 𝔽ₚ are squares — Euler's criterion and the Legendre symbol.)

-- x = 0: rhs = 0³ + 0 + 1 = 1. Squares: ±1 = {1, 4}. ⟹ (0,1), (0,4)
example : (1 : 𝔽₅) ^ 2 = (0 : 𝔽₅) ^ 3 + 0 + 1 := by decide
example : (4 : 𝔽₅) ^ 2 = (0 : 𝔽₅) ^ 3 + 0 + 1 := by decide

-- x = 1: rhs = 1 + 1 + 1 = 3. Not a square — no points (no solution).
example : ¬ ∃ y : 𝔽₅, y ^ 2 = (1 : 𝔽₅) ^ 3 + 1 + 1 := by decide

-- x = 2: rhs = 8 + 2 + 1 = 11 ≡ 1. ⟹ (2,1), (2,4)
example : (1 : 𝔽₅) ^ 2 = (2 : 𝔽₅) ^ 3 + 2 + 1 := by decide
example : (4 : 𝔽₅) ^ 2 = (2 : 𝔽₅) ^ 3 + 2 + 1 := by decide

-- x = 3: rhs = 27 + 3 + 1 = 31 ≡ 1. ⟹ (3,1), (3,4)
example : (1 : 𝔽₅) ^ 2 = (3 : 𝔽₅) ^ 3 + 3 + 1 := by decide
example : (4 : 𝔽₅) ^ 2 = (3 : 𝔽₅) ^ 3 + 3 + 1 := by decide

-- x = 4: rhs = 64 + 4 + 1 = 69 ≡ 4. ⟹ (4,2), (4,3)
example : (2 : 𝔽₅) ^ 2 = (4 : 𝔽₅) ^ 3 + 4 + 1 := by decide
example : (3 : 𝔽₅) ^ 2 = (4 : 𝔽₅) ^ 3 + 4 + 1 := by decide

-- Total: 8 affine points, plus the point at infinity O (introduced in §4):
--
--   E(𝔽₅) = { O, (0,1), (0,4), (2,1), (2,4), (3,1), (3,4), (4,2), (4,3) }
--
-- ⟹ #E(𝔽₅) = 9. We will see in §6 why this number is no surprise.
--
-- Notice the SYMMETRY: every affine point appears with its mirror image
-- (x, y) and (x, -y). That mirror image is exactly the group inverse (§4).

-- ============================================================================
-- Section 4: The chord-and-tangent group law
-- ============================================================================
--
-- The points of E form an abelian group with the following rules. Geometric
-- intuition (over ℝ): to add P and Q, draw the line through them, intersect
-- with the curve at a third point R', then REFLECT across the x-axis to get
-- P + Q := R = -R'.
--
--              P *
--                 ╲
--                  ╲
--                   ╲     * R = P + Q   (below x-axis if R' above)
--                    * Q  ⋮
--                     ╲   ⋮
--    ──────────────────╲──⋮───────────────────── x-axis
--                       ╲ ⋮(reflect)
--                        \⋮
--                         * -R' = third intersection (on curve)
--
-- Three special cases:
--   (a) Q = P: the "chord" degenerates to the TANGENT at P. Same recipe,
--       same picture — used to compute 2P (DOUBLING, §5).
--   (b) Q = -P: the line through P and -P is vertical, hits no third affine
--       point, so we declare R = O, the POINT AT INFINITY. This makes O the
--       group identity by fiat.
--   (b') if y₁ = 0 then P = -P, so 2P = O. (Tangent formula would divide
--       by zero; geometrically the tangent is vertical.)
--       TODO: Remove this point?
--   (c) Negation: -(x, y) = (x, -y) — reflection across the x-axis.
--
-- ----------------------------------------------------------------------------
-- The formulas
-- ----------------------------------------------------------------------------
--
-- For short Weierstrass y² = x³ + a·x + b, given P = (x₁,y₁), Q = (x₂,y₂):
--
--   SLOPE  λ = ⎧ (y₂ - y₁) / (x₂ - x₁)  if x₁ ≠ x₂   (chord)
--              ⎩ (3·x₁² + a) / (2·y₁)   if P = Q     (tangent)
--
--   x₃ = λ² - x₁ - x₂
--   y₃ = λ·(x₁ - x₃) - y₁
--
-- Then P + Q = (x₃, y₃). Both branches DIVIDE — which is why we need a
-- field. (Ideals.lean §9: 𝔽ₚ is a field exactly because (p) is maximal.)
--
-- TODO: mention Edwards and Montgomery curves as alternatives.

-- ============================================================================
-- Section 5: A worked addition in E(𝔽₅)
-- ============================================================================
--
-- Take P = (0, 1) and Q = (4, 2). Since x₁ ≠ x₂ we use the chord branch.
-- Recall in 𝔽₅: 4⁻¹ = 4 (because 4·4 = 16 ≡ 1).
--
--   λ  = (2 - 1) / (4 - 0) = 1 / 4 = 4         in 𝔽₅
--   x₃ = 4² - 0 - 4 = 16 - 4 = 12 ≡ 2
--   y₃ = 4·(0 - 2) - 1 = -9 ≡ 1
--
-- So P + Q = (2, 1). Sanity check that (2, 1) is on E (we already did this
-- in §3, but here it is from the addition formula):

example : ((4 : 𝔽₅) * (0 - 2) - 1) ^ 2 =
          ((4 : 𝔽₅) ^ 2 - 0 - 4) ^ 3 + ((4 : 𝔽₅) ^ 2 - 0 - 4) + 1 := by decide

-- ----------------------------------------------------------------------------
-- Doubling: compute 2P with P = (0, 1)
-- ----------------------------------------------------------------------------
--
-- Now the tangent branch (Q = P): in 𝔽₅, 2⁻¹ = 3 (because 2·3 = 6 ≡ 1).
--
--   λ  = (3·0² + 1) / (2·1) = 1 / 2 = 3         in 𝔽₅
--   x₃ = 3² - 0 - 0 = 9 ≡ 4
--   y₃ = 3·(0 - 4) - 1 = -13 ≡ 2
--
-- So 2P = (4, 2). Verify (4, 2) is on E from the doubling formula directly:

example : ((3 : 𝔽₅) * (0 - 4) - 1) ^ 2 =
          ((3 : 𝔽₅) ^ 2 - 0 - 0) ^ 3 + ((3 : 𝔽₅) ^ 2 - 0 - 0) + 1 := by decide

-- ============================================================================
-- Section 6: The group structure and Hasse's bound
-- ============================================================================
--
-- Mathlib packages all of §4–§5 into an `AddCommGroup` instance on the type
-- of points. We get +, -, 0 (= O), associativity, commutativity, inverses
-- for free. (Associativity is the hard one — it's a substantial theorem.)

noncomputable instance : AddCommGroup (Point E.toAffine) := inferInstance

-- The identity is the point at infinity:
#check (0 : Point E.toAffine)
example : (0 : Point E.toAffine) = Point.zero := rfl

-- ----------------------------------------------------------------------------
-- Hasse's bound
-- ----------------------------------------------------------------------------
--
-- We counted 9 points in §3. Hasse (1933) says: for any elliptic curve E
-- over 𝔽_p,
--
--     |#E(𝔽_p) - (p + 1)| ≤ 2·√p.
--
-- For p = 5: p + 1 = 6 and 2√5 ≈ 4.47, so #E(𝔽₅) ∈ [2, 10]. Our 9 lands
-- comfortably in range:

-- 2√5 < 5, so the inequality is `|9 - 6| ≤ 5`, i.e. `3 ≤ 5`. Equivalently,
-- squaring both sides of `|#E - (p+1)| ≤ 2·√p` gives `(#E - p - 1)² ≤ 4p`:
example : ((9 : ℤ) - (5 + 1)) ^ 2 ≤ 4 * 5 := by decide

-- Why this matters for crypto: Hasse pins #E(𝔽_p) near p, but the EXACT
-- count varies curve-by-curve. We pick curves (e.g. secp256k1) whose order
-- is prime (or has a large prime factor) — that's what guarantees the
-- group is cyclic of large prime order, which is what ECDLP relies on.

-- ============================================================================
-- Section 7: ECDH — Diffie–Hellman on E(𝔽₅)
-- ============================================================================
--
-- The DH identity from DiffieHellman.lean §3 was
--   (g^b)^a = (g^a)^b   in any monoid.
--
-- Elliptic curves are written ADDITIVELY, so `g^n` becomes `n • P` and the
-- identity becomes
--   a • (b • P) = b • (a • P)
--
-- Free algebra: `smul_smul` + ℕ-commutativity. Same proof shape as
-- `dh_correctness` in DiffieHellman.lean §3.

theorem ecdh_correctness {G : Type*} [AddCommMonoid G] (P : G) (a b : ℕ) :
    a • (b • P) = b • (a • P) := by
  calc a • (b • P)
      = (a * b) • P := by rw [smul_smul]
    _ = (b * a) • P := by rw [Nat.mul_comm]
    _ = b • (a • P) := by rw [← smul_smul]

-- ----------------------------------------------------------------------------
-- The cyclic subgroup generated by (0, 1)
-- ----------------------------------------------------------------------------
--
-- The protocol picks a public BASE POINT P of large prime order and works
-- inside ⟨P⟩, the cyclic subgroup it generates. Computing once by hand
-- with the formulas from §5, starting from P = (0, 1):
--
--   1P = (0, 1)                  6P = (2, 4)
--   2P = (4, 2)                  7P = (4, 3)
--   3P = (2, 1)                  8P = (0, 4) = -P
--   4P = (3, 4)                  9P = O      (identity)
--   5P = (3, 1)
--
-- So P has order 9 and ⟨P⟩ = E(𝔽₅). In particular E(𝔽₅) ≅ ℤ/9ℤ — a cyclic
-- group (Cyclic.lean), exactly the setting ECDH needs.
--
-- ----------------------------------------------------------------------------
-- Protocol — concrete run
-- ----------------------------------------------------------------------------
--
-- Public: curve E, base point P. Alice's secret a = 2; Bob's secret b = 5.
--   Alice sends A := 2·P = (4, 2).
--   Bob   sends B := 5·P = (3, 1).
--
-- Shared secret: a·B = 2·(5P) = 10·P = 1·P = (0, 1)
--              = b·A = 5·(2P) = 10·P = (0, 1).
-- TODO: Demonstrate this with Lean
--
-- Correctness is `ecdh_correctness` applied to G = Point E.toAffine.
--
-- (We won't ask Lean to *evaluate* `(2 : ℕ) • P` here because the group
-- instance is `noncomputable`. The protocol's CORRECTNESS holds anyway —
-- it's the abstract identity above.)

-- ============================================================================
-- Section 8: Why ECC dominates — ECDLP vs DLP
-- ============================================================================
--
-- Same protocol as DH, three sharper properties:
--
-- 1. The eavesdropper sees (P, a·P, b·P) and needs a·b·P. Recovering a
--    from a·P is the ELLIPTIC-CURVE DISCRETE LOG PROBLEM (ECDLP). Unlike
--    plain DLP in 𝔽_pˣ, no subexponential algorithm is known — the best
--    generic attack is Pollard ρ at √n.
--
-- 2. Consequence: 256-bit curve ≈ 3072-bit RSA / DH for the same security.
--    Smaller keys → faster signatures, less bandwidth, less power. ECDSA
--    and X25519 dominate TLS, SSH, and Bitcoin/Ethereum for this reason.
--
-- 3. Curve choice matters. We need #E(𝔽_p) divisible by a large prime to
--    avoid Pohlig–Hellman (which reduces ECDLP to subgroups of prime-power
--    order). Standard curves (Curve25519, secp256k1, NIST P-256) are
--    chosen with this — and a long list of subtler — properties in mind.
--
-- ============================================================================

-- TODO: prove `E(𝔽₅) ≅ Multiplicative (ZMod 9)` (cyclicity of the point
-- group), connecting this file back to Cyclic.lean.
-- TODO: state Hasse's theorem as a Mathlib lemma, not just a comment.
-- TODO: instantiate ECDH on a larger curve where `native_decide` can
-- actually run the protocol end-to-end.
