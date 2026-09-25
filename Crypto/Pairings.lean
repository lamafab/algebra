import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Bilinear Pairings
-- ============================================================================
--
-- A bilinear pairing is a map
--
--   e : G₁ × G₂ → G_T
--
-- from two additive groups to a multiplicative group that is linear in each
-- argument separately:
--
--   e(P + P', Q)  = e(P, Q) · e(P', Q)
--   e(P, Q + Q')  = e(P, Q) · e(P, Q')
--
-- and non-degenerate: if e(P, Q) = 1 for every Q then P = 0, and
-- symmetrically. In cryptography all three groups share one prime order r.
--
-- The workhorse consequence is the exponent law of §2:
--
--   e(a • P, b • Q) = e(P, Q)^(a·b).
--
-- A hidden scalar in each input turns into one multiplication in the
-- exponent. That single multiplication, checkable by anyone, is what
-- pairings buy over plain groups: §4 (decisional Diffie-Hellman becomes
-- easy), §5 (three-party key agreement in one round), §6 (short
-- signatures).
--
-- Where the groups come from in practice, not formalized here: G₁ and G₂
-- are prime-order subgroups of elliptic curve points (EllipticCurves.lean),
-- and G_T is a subgroup of 𝔽_{pᵏ}ˣ for the embedding degree k. The actual
-- maps (Weil, Tate, ate pairings, computed by Miller's algorithm) are
-- substantial algebraic geometry; everything below needs only the abstract
-- interface of §1.
--
-- When G₁ = G₂ the pairing is called symmetric (type 1). Deployed schemes
-- use asymmetric pairings (type 3, no efficient map between G₁ and G₂) on
-- pairing-friendly curves such as BN254 or BLS12-381; the interface here
-- keeps G₁ and G₂ separate so both cases fit.
--
--   §1  The pairing interface
--   §2  Derived exponent laws
--   §3  A toy pairing: multiplication in 𝔽ₚ
--   §4  What a pairing buys: the decisional Diffie-Hellman check
--   §5  Application: Joux tripartite key agreement
--   §6  Application: BLS signatures
-- ============================================================================

-- ============================================================================
-- Section 1: The pairing interface
-- ============================================================================

section Interface

/-- A bilinear pairing between additive groups G₁, G₂ and a multiplicative
group GT.

Bilinearity is stated as additivity in each argument; the scalar versions
(`e (n • P) Q = e P Q ^ n`) are derived in §2. Non-degeneracy says the only
element that pairs trivially with everything is zero; §4 relies on it to
make the DDH check reject false tuples rather than pass vacuously. -/
structure BilinearPairing
    (G₁ G₂ : Type*) [AddCommGroup G₁] [AddCommGroup G₂]
    (GT : Type*) [CommGroup GT] where
  e : G₁ → G₂ → GT
  map_add_left : ∀ P P' : G₁, ∀ Q : G₂, e (P + P') Q = e P Q * e P' Q
  map_add_right : ∀ P : G₁, ∀ Q Q' : G₂, e P (Q + Q') = e P Q * e P Q'
  nondegenerate_left : ∀ P : G₁, (∀ Q : G₂, e P Q = 1) → P = 0
  nondegenerate_right : ∀ Q : G₂, (∀ P : G₁, e P Q = 1) → Q = 0

end Interface

-- ============================================================================
-- Section 2: Derived exponent laws
-- ============================================================================
--
-- Additivity in each argument upgrades to scalar laws by induction. The
-- final one, `map_nsmul_nsmul`, is the identity every pairing-based
-- protocol actually uses.

section Laws

namespace BilinearPairing

variable {G₁ G₂ GT : Type*} [AddCommGroup G₁] [AddCommGroup G₂] [CommGroup GT]
  (pair : BilinearPairing G₁ G₂ GT)

-- Zero pairs trivially: from e(0, Q) = e(0 + 0, Q) = e(0, Q)² cancel one
-- factor.
theorem map_zero_left (Q : G₂) : pair.e 0 Q = 1 := by
  have h : pair.e 0 Q * pair.e 0 Q = pair.e 0 Q * 1 := by
    rw [← pair.map_add_left 0 0 Q]; simp
  exact mul_left_cancel h

theorem map_zero_right (P : G₁) : pair.e P 0 = 1 := by
  have h : pair.e P 0 * pair.e P 0 = pair.e P 0 * 1 := by
    rw [← pair.map_add_right P 0 0]; simp
  exact mul_left_cancel h

-- Negation inverts: e(-P, Q) · e(P, Q) = e(-P + P, Q) = 1.
theorem map_neg_left (P : G₁) (Q : G₂) : pair.e (-P) Q = (pair.e P Q)⁻¹ := by
  have h : pair.e (-P) Q * pair.e P Q = 1 := by
    rw [← pair.map_add_left, neg_add_cancel, pair.map_zero_left]
  exact eq_inv_of_mul_eq_one_left h

theorem map_neg_right (P : G₁) (Q : G₂) : pair.e P (-Q) = (pair.e P Q)⁻¹ := by
  have h : pair.e P (-Q) * pair.e P Q = 1 := by
    rw [← pair.map_add_right, neg_add_cancel, pair.map_zero_right]
  exact eq_inv_of_mul_eq_one_left h

-- ℕ-scalars come out of the left argument as exponents.
theorem map_nsmul_left (n : ℕ) (P : G₁) (Q : G₂) :
    pair.e (n • P) Q = (pair.e P Q) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pair.map_zero_left, pow_zero]
  | succ k ih => rw [succ_nsmul, pair.map_add_left, ih, pow_succ]

theorem map_nsmul_right (n : ℕ) (P : G₁) (Q : G₂) :
    pair.e P (n • Q) = (pair.e P Q) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pair.map_zero_right, pow_zero]
  | succ k ih => rw [succ_nsmul, pair.map_add_right, ih, pow_succ]

-- The master law: e(a • P, b • Q) = e(P, Q)^(a·b).
theorem map_nsmul_nsmul (a b : ℕ) (P : G₁) (Q : G₂) :
    pair.e (a • P) (b • Q) = (pair.e P Q) ^ (a * b) := by
  rw [pair.map_nsmul_left, pair.map_nsmul_right, ← pow_mul, Nat.mul_comm]

end BilinearPairing

end Laws

-- ============================================================================
-- Section 3: A toy pairing: multiplication in 𝔽ₚ
-- ============================================================================
--
-- The simplest bilinear map in sight is multiplication itself:
--   e(x, y) = x · y   on  (𝔽ₚ, +) × (𝔽ₚ, +),
-- with the target (𝔽ₚ, +) written multiplicatively via the `Multiplicative`
-- type tag so that bilinearity reads as distributivity:
--   (x + x') · y  =  x·y + x'·y.
--
-- This instance is for demonstrations only. The discrete logarithm in
-- (𝔽ₚ, +) is division, so every hardness assumption fails here. Real
-- pairings use elliptic curve subgroups where the discrete log is hard;
-- the algebra is identical, which is why the toy instance can exercise the
-- interface honestly.

section Toy

variable (p : ℕ)

/-- The multiplication pairing on 𝔽ₚ: `e x y = x * y`, target written
multiplicatively. Non-degeneracy is evaluation against 1, which reveals the
scalar. Algebraically the instance works for any modulus; the cryptographically
meaningful case is prime order. -/
def mulPairing : BilinearPairing (ZMod p) (ZMod p) (Multiplicative (ZMod p)) where
  e x y := Multiplicative.ofAdd (x * y)
  map_add_left x x' y := by
    show Multiplicative.ofAdd ((x + x') * y) = _
    rw [add_mul, ofAdd_add]
  map_add_right x y y' := by
    show Multiplicative.ofAdd (x * (y + y')) = _
    rw [mul_add, ofAdd_add]
  nondegenerate_left x h := by
    have h1 : Multiplicative.ofAdd (x * 1) = (1 : Multiplicative (ZMod p)) := h 1
    have h2 := congrArg Multiplicative.toAdd h1
    simpa using h2
  nondegenerate_right y h := by
    have h1 : Multiplicative.ofAdd (1 * y) = (1 : Multiplicative (ZMod p)) := h 1
    have h2 := congrArg Multiplicative.toAdd h1
    simpa using h2

-- Over 𝔽₇ the map really does multiply: e(2, 3) is the multiplicative copy
-- of 6.
example : (mulPairing 7).e 2 3 = Multiplicative.ofAdd (6 : ZMod 7) := by decide

-- The exponent law, checked numerically: e(2·3, 4) = e(3, 4)². Both sides
-- are the multiplicative copy of 24 ≡ 3 (mod 7).
example : (mulPairing 7).e (2 • (3 : ZMod 7)) 4
    = ((mulPairing 7).e 3 4) ^ 2 := by decide

end Toy

-- ============================================================================
-- Section 4: What a pairing buys: the decisional Diffie-Hellman check
-- ============================================================================
--
-- In a plain group, given (P, a•P, b•P, c•P) there is no feasible way to
-- tell whether c•P = (a·b)•P; that intractability is the decisional
-- Diffie-Hellman assumption behind DiffieHellman.lean and EllipticCurves.lean.
--
-- A symmetric pairing dissolves it. Compare:
--   e(a•P, b•P) = e(P, P)^(a·b)     with     e(P, c•P) = e(P, P)^c.
-- The tuple is a real DH tuple iff the two values agree. So in
-- pairing groups DDH is easy while the computational problem (produce
-- (a·b)•P from scratch) stays hard: the pairing multiplies exponents once,
-- but nothing lets you multiply twice.

section DDH

variable {G GT : Type*} [AddCommGroup G] [CommGroup GT]
  (pair : BilinearPairing G G GT)

-- The check accepts honest tuples: e(a•P, b•P) = e(P, (a·b)•P).
theorem ddh_check_complete (P : G) (a b : ℕ) :
    pair.e (a • P) (b • P) = pair.e P ((a * b) • P) := by
  rw [pair.map_nsmul_nsmul, pair.map_nsmul_right]

-- Rejection of false tuples needs e(P, P) to have the same order as P,
-- which for prime-order groups follows from non-degeneracy; we leave the
-- order machinery out and demonstrate the rejection numerically below.

-- Over the toy pairing with P = 1: (2, 3, 6) passes, (2, 3, 5) fails.
example : (mulPairing 7).e (2 • (1 : ZMod 7)) (3 • 1)
    = (mulPairing 7).e 1 (6 • 1) := by decide

example : (mulPairing 7).e (2 • (1 : ZMod 7)) (3 • 1)
    ≠ (mulPairing 7).e 1 (5 • 1) := by decide

end DDH

-- ============================================================================
-- Section 5: Application: Joux tripartite key agreement
-- ============================================================================
--
-- Diffie-Hellman agrees a key between two parties in one round. Before
-- pairings, three parties needed two rounds. Joux (2000) does it in one
-- with a symmetric pairing:
--
--   Alice, Bob, Carol pick secrets a, b, c and broadcast a•P, b•P, c•P.
--   Alice computes  e(b•P, c•P)^a,
--   Bob computes    e(a•P, c•P)^b,
--   Carol computes  e(a•P, b•P)^c.
--
-- All three land on e(P, P)^(a·b·c), since each party contributes its own
-- secret as the outer exponent after the pairing has multiplied the other
-- two. An eavesdropper sees only the three public points; extracting the
-- key is a pairing variant of the computational DH problem.

section Joux

variable {G GT : Type*} [AddCommGroup G] [CommGroup GT]
  (pair : BilinearPairing G G GT)

theorem joux_alice (P : G) (a b c : ℕ) :
    (pair.e (b • P) (c • P)) ^ a = (pair.e P P) ^ (a * b * c) := by
  rw [pair.map_nsmul_nsmul, ← pow_mul, Nat.mul_comm (b * c) a, ← Nat.mul_assoc]

theorem joux_bob (P : G) (a b c : ℕ) :
    (pair.e (a • P) (c • P)) ^ b = (pair.e P P) ^ (a * b * c) := by
  rw [pair.map_nsmul_nsmul, ← pow_mul, Nat.mul_comm (a * c) b, ← Nat.mul_assoc,
    Nat.mul_comm b a]

theorem joux_carol (P : G) (a b c : ℕ) :
    (pair.e (a • P) (b • P)) ^ c = (pair.e P P) ^ (a * b * c) := by
  rw [pair.map_nsmul_nsmul, ← pow_mul]

-- All three computations agree on one shared key.
theorem joux_shared_key (P : G) (a b c : ℕ) :
    (pair.e (b • P) (c • P)) ^ a = (pair.e P P) ^ (a * b * c)
    ∧ (pair.e (a • P) (c • P)) ^ b = (pair.e P P) ^ (a * b * c)
    ∧ (pair.e (a • P) (b • P)) ^ c = (pair.e P P) ^ (a * b * c) :=
  ⟨joux_alice pair P a b c, joux_bob pair P a b c, joux_carol pair P a b c⟩

-- Numerically over the toy pairing: with a=2, b=3, c=5, P=1, Alice's
-- computation e(3•1, 5•1)² is the shared key e(1, 1)³⁰.
example : ((mulPairing 7).e (3 • (1 : ZMod 7)) (5 • 1)) ^ 2
    = ((mulPairing 7).e 1 1) ^ (2 * 3 * 5) := by decide

end Joux

-- ============================================================================
-- Section 6: Application: BLS signatures
-- ============================================================================
--
-- BLS (Boneh-Lynn-Shacham, 2001) is the shortest signature scheme known:
-- one group element, verified by one pairing equation. It uses the
-- asymmetric interface, with signatures in G₁ and public keys in G₂:
--
--   keygen:  secret x, public key pk = x • G₂ for a fixed generator G₂.
--   sign:    hash the message to H(m) ∈ G₁, output σ = x • H(m).
--   verify:  accept iff e(σ, G₂) = e(H(m), pk).
--
-- Correctness is one application of bilinearity: both sides equal
-- e(H(m), G₂)^x. What is not covered here: hashing into the group (a
-- construction of its own), and unforgeability, which rests on the
-- computational DH problem in G₁ inside the random oracle model.

section BLS

variable {G₁ G₂ GT : Type*} [AddCommGroup G₁] [AddCommGroup G₂] [CommGroup GT]
  (pair : BilinearPairing G₁ G₂ GT)

/-- BLS verification correctness: an honestly formed signature verifies. -/
theorem bls_verify (G₂gen : G₂) (x : ℕ) (hm : G₁) :
    pair.e (x • hm) G₂gen = pair.e hm (x • G₂gen) := by
  rw [pair.map_nsmul_left, pair.map_nsmul_right]

-- Numerically over the toy pairing: secret x = 4, message hash 2,
-- generator 1. The signature is 4•2 and the two sides agree.
example : (mulPairing 7).e (4 • (2 : ZMod 7)) 1
    = (mulPairing 7).e 2 (4 • 1) := by decide

end BLS

-- ============================================================================
-- TODOs
-- ============================================================================
-- * The real maps: Weil and Tate pairings on curve points, via divisors and
--   Miller's algorithm. This needs much more algebraic geometry than the
--   repository currently has.
-- * Embedding degree and pairing-friendly curves (BN254, BLS12-381): why a
--   generic curve does not admit a usable pairing.
-- * Product-of-pairings verification equations are also the engine of
--   pairing-based SNARKs such as Groth16; that build is left to a later
--   file.
