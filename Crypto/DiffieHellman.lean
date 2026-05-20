import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

-- ============================================================================
-- Diffie–Hellman — why B^a = A^b
-- ============================================================================
--
-- Setup: cyclic group G with generator g.
-- Protocol: Alice sends g^a, Bob sends g^b, both compute g^(a·b).
--
-- Correctness:
--   (g^b)^a = g^(b·a) = g^(a·b) = (g^a)^b.
--
-- Same identity as RSA's (m^e)^d, used differently:  RSA recovers a
-- message; DH agrees on a secret. Free algebra — `pow_mul` + ℕ-commutativity.

-- ============================================================================
-- Section 1: Setup — 𝔽₁₁ˣ with generator 2
-- ============================================================================
--
-- 11 prime ⟹ ZMod 11 is a field (Ideals §7), so 𝔽₁₁ˣ is cyclic of order 10
-- (Cyclic.lean). 2 is a primitive root.

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

example : (2 : ZMod 11) ^ 1 = 2  := by decide
example : (2 : ZMod 11) ^ 5 = 10 := by decide
example : (2 : ZMod 11) ^ 10 = 1 := by decide  -- wraps (Fermat)

-- ============================================================================
-- Section 2: Protocol — concrete run
-- ============================================================================
--
-- Public: g = 2. Alice's secret: a = 3. Bob's secret:  b = 5.

abbrev g : ZMod 11 := 2
abbrev a : ℕ := 3
abbrev b : ℕ := 5
abbrev A : ZMod 11 := g ^ a -- = 8
abbrev B : ZMod 11 := g ^ b -- = 10

example : B^a = A^b := by decide         -- shared secret
example : B^a = g ^ (a * b) := by decide -- = g^15 = 10

-- ============================================================================
-- Section 3: Why it works
-- ============================================================================
--
-- Correctness of DH is one identity:
--   (g^b)^a = g^(b·a) = g^(a·b) = (g^a)^b
--
-- Works in ANY monoid — only the EXPONENTS need to commute, and they
-- live in ℕ, which always commutes.

theorem dh_correctness {G : Type*} [Monoid G] (g : G) (a b : ℕ) :
    (g ^ b) ^ a = (g ^ a) ^ b := by
  calc (g ^ b) ^ a
      = g ^ (b * a) := by rw [← pow_mul]
    _ = g ^ (a * b) := by rw [Nat.mul_comm]
    _ = (g ^ a) ^ b := by rw [← pow_mul]

-- ============================================================================
-- Section 4: Security & Galois fields
-- ============================================================================
--
-- Eavesdropper sees (g, g^a, g^b); needs g^(a·b). Recovering a from g^a is
-- the DISCRETE LOG PROBLEM — trivial in 𝔽₁₁ˣ, conjectured HARD in large
-- cyclic groups. (As with RSA→factoring, security is a conjecture.)
--
-- Cyclic groups come from finite fields (deep theorem, Cyclic.lean):
--   𝔽_pˣ     order p - 1   — index calculus ⟹ need ~2048-bit p
--   GF(p^n)ˣ order p^n - 1 — (QuotientRings §4)
--   E(𝔽_p)   point group   — no subexp attack ⟹ ~256-bit p suffices
--
-- ECDH dominates modern crypto: same protocol, smaller keys.
