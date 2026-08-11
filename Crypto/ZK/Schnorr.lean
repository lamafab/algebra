import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Schnorr: proving knowledge of a discrete log
-- ============================================================================
--
-- A sigma protocol (three moves, public coin) for the relation "I know w
-- with A = g^w". Setup: a group of prime order q with generator g; the
-- prover's secret is the witness w ∈ Z/qZ, the public statement is A = g^w.
--
--   commit     prover samples k ← Z/qZ, sends R = g^k
--   challenge  verifier samples c ← Z/qZ, sends c
--   response   prover sends z = k + c·w (mod q)
--   verify     accept iff g^z = R · A^c
--
-- The three defining properties are proved separately (zk_todo.md, step 2):
--
--   §2 completeness        honest runs always accept; one pow_add/pow_mul
--                          identity, the same shape as dh_correctness
--   §3 special soundness   two accepting transcripts (R, c₁, z₁) and
--                          (R, c₂, z₂) with c₁ ≠ c₂ determine the witness:
--                          w = (z₁ − z₂)·(c₁ − c₂)⁻¹
--   §4 honest-verifier     a simulator that never sees w produces accepting
--     zero-knowledge       transcripts with the same distribution as real
--                          ones, so a transcript alone reveals nothing of w
--
-- What is not proved: that w is hard to recover from A alone. That is the
-- discrete log assumption, idealized here exactly as in DiffieHellman.lean.

namespace Schnorr

section Abstract

variable {G : Type*} [CommGroup G] {q : ℕ} [Fact q.Prime]

-- ============================================================================
-- Section 1: Exponent arithmetic mod q
-- ============================================================================
--
-- Everything in the protocol is exponent arithmetic in Z/qZ. The bridge from
-- ZMod q to group powers: in a group of exponent q (every x satisfies
-- x^q = 1, for instance a group of prime order q), powers may be reduced
-- mod q. This section packages that bridge once; the protocol proofs below
-- are then pure ZMod q algebra.

-- In a group of exponent q, congruent exponents give equal powers.
omit [Fact q.Prime] in
theorem pow_eq_pow_of_modEq_nat (hG : ∀ x : G, x ^ q = 1) (x : G) {n m : ℕ}
    (h : n ≡ m [MOD q]) : x ^ n = x ^ m :=
  pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one (hG x)))

theorem val_add_modEq (a b : ZMod q) : (a + b).val ≡ a.val + b.val [MOD q] := by
  rw [ZMod.val_add]
  exact Nat.mod_modEq _ _

omit [Fact q.Prime] in
theorem val_mul_modEq (a b : ZMod q) : (a * b).val ≡ a.val * b.val [MOD q] := by
  rw [ZMod.val_mul]
  exact Nat.mod_modEq _ _

-- The four power laws, lifted to ZMod q exponents.

theorem pow_add_zmod (hG : ∀ x : G, x ^ q = 1) (x : G) (a b : ZMod q) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add]
  exact pow_eq_pow_of_modEq_nat hG x (val_add_modEq a b)

omit [Fact q.Prime] in
theorem pow_mul_zmod (hG : ∀ x : G, x ^ q = 1) (x : G) (a b : ZMod q) :
    x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rw [← pow_mul]
  exact pow_eq_pow_of_modEq_nat hG x (val_mul_modEq a b)

theorem pow_neg_zmod (hG : ∀ x : G, x ^ q = 1) (x : G) (a : ZMod q) :
    x ^ (-a).val = (x ^ a.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_add_zmod hG, neg_add_cancel]
  rw [ZMod.val_zero, pow_zero]

theorem pow_sub_zmod (hG : ∀ x : G, x ^ q = 1) (x : G) (a b : ZMod q) :
    x ^ (a - b).val = x ^ a.val * (x ^ b.val)⁻¹ := by
  rw [sub_eq_add_neg, pow_add_zmod hG, pow_neg_zmod hG]

-- ============================================================================
-- Section 2: Completeness
-- ============================================================================
--
-- The verification equation for an honest run, z = k + c·w:
--
--   g^z = g^(k + c·w) = g^k · (g^w)^c = R · A^c.
--
-- Same identity as dh_correctness, used differently: DH agrees on a secret,
-- here the prover demonstrates control of the exponent behind A.

theorem completeness (hG : ∀ x : G, x ^ q = 1) (g : G) (w k c : ZMod q) :
    g ^ (k + c * w).val = g ^ k.val * (g ^ w.val) ^ c.val := by
  rw [pow_add_zmod hG, mul_comm c w, pow_mul_zmod hG]

-- ============================================================================
-- Section 3: Special soundness
-- ============================================================================
--
-- Suppose a (possibly cheating) prover can answer two different challenges
-- c₁ ≠ c₂ for the same commitment R:
--
--   g^z₁ = R · A^c₁     g^z₂ = R · A^c₂
--
-- Dividing eliminates R: g^(z₁ − z₂) = A^(c₁ − c₂). Since c₁ − c₂ ≠ 0 in
-- the field Z/qZ it has an inverse, and raising both sides to it extracts
-- the witness:
--
--   A = g^w   with   w = (z₁ − z₂)·(c₁ − c₂)⁻¹.
--
-- So any prover that answers two challenges for one commitment must know w.
-- This is the extraction half of soundness; the rewinding argument that
-- produces the two transcripts from a successful prover is the other half
-- and is standard (and probabilistic), not formalized here.

theorem special_soundness (hG : ∀ x : G, x ^ q = 1) (g R A : G)
    {c₁ c₂ z₁ z₂ : ZMod q} (hc : c₁ ≠ c₂)
    (h₁ : g ^ z₁.val = R * A ^ c₁.val)
    (h₂ : g ^ z₂.val = R * A ^ c₂.val) :
    A = g ^ ((z₁ - z₂) * (c₁ - c₂)⁻¹).val := by
  -- Divide the two verification equations: g^(z₁−z₂) = A^(c₁−c₂).
  have key : g ^ (z₁ - z₂).val = A ^ (c₁ - c₂).val := by
    rw [pow_sub_zmod hG, pow_sub_zmod hG, h₁, h₂,
        mul_inv_rev, ← mul_assoc, mul_assoc R, mul_right_comm R,
        mul_inv_cancel, one_mul]
  -- Raise both sides to (c₁ − c₂)⁻¹; the exponent on A collapses to 1.
  calc A = A ^ (1 : ZMod q).val := by
          rw [ZMod.val_one, pow_one]
    _ = A ^ ((c₁ - c₂) * (c₁ - c₂)⁻¹).val := by
          rw [mul_inv_cancel₀ (sub_ne_zero.mpr hc)]
    _ = (A ^ (c₁ - c₂).val) ^ ((c₁ - c₂)⁻¹).val := pow_mul_zmod hG A _ _
    _ = (g ^ (z₁ - z₂).val) ^ ((c₁ - c₂)⁻¹).val := by rw [← key]
    _ = g ^ ((z₁ - z₂) * (c₁ - c₂)⁻¹).val := (pow_mul_zmod hG g _ _).symm

-- ============================================================================
-- Section 4: Honest-verifier zero-knowledge
-- ============================================================================
--
-- A transcript (R, c, z) should reveal nothing about w, and the proof of
-- that is constructive: anyone can produce accepting transcripts without w.
-- Given A and a challenge c, sample z and set R = g^z · A^{-c}; then
-- g^z = R · A^c holds by construction.
--
-- The point is that these simulated transcripts are not just accepting,
-- they are indistinguishable from real ones. Real transcripts are
-- parameterized by the prover's nonce k; simulated ones by the simulator's
-- z. For fixed w and c the map k ↦ z = k + c·w is a bijection on Z/qZ
-- (adding a constant), so a uniform k and a uniform z sweep out exactly
-- the same set of transcripts.

-- The simulated transcript accepts.
omit [Fact q.Prime] in
theorem simulator_verify (g A : G) (z c : ZMod q) :
    g ^ z.val = g ^ z.val * (A ^ c.val)⁻¹ * A ^ c.val :=
  (inv_mul_cancel_right _ _).symm

-- Componentwise, the simulated transcript with randomness z = k + c·w is
-- the real transcript with nonce k: the simulated commitment is g^k.
theorem simulated_eq_real (hG : ∀ x : G, x ^ q = 1) (g : G) (w k c z : ZMod q)
    (hz : z = k + c * w) :
    g ^ z.val * ((g ^ w.val) ^ c.val)⁻¹ = g ^ k.val := by
  rw [hz, completeness hG g w k c, mul_inv_cancel_right]

-- k ↦ k + c·w is a bijection, so real and simulated distributions agree.
theorem response_bijective (w c : ZMod q) :
    Function.Bijective fun k : ZMod q => k + c * w :=
  (Equiv.addRight (c * w)).bijective

end Abstract

end Schnorr

-- ============================================================================
-- Section 5: A concrete run over 𝔽₂₃
-- ============================================================================
--
-- 𝔽₂₃ˣ is cyclic of order 22 = 2·11, and 2 has order 11 (2^11 = 2048 =
-- 89·23 + 1), so ⟨2⟩ is a prime-order subgroup with q = 11. The protocol
-- runs inside it with exponents in ZMod 11.
--
--   witness w = 4,  public A = 2^4 = 16
--   nonce   k = 3,  commitment R = 2^3 = 8
--   challenge c = 6,  response z = k + c·w = 3 + 24 = 27 ≡ 5 (mod 11)

notation "𝔽₂₃" => ZMod 23
instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

namespace Schnorr.Example

abbrev w : ZMod 11 := 4
abbrev k : ZMod 11 := 3
abbrev c : ZMod 11 := 6

example : (2 : 𝔽₂₃) ^ 11 = 1 := by decide
example : (2 : 𝔽₂₃) ^ w.val = 16 := by decide  -- public A
example : (2 : 𝔽₂₃) ^ k.val = 8 := by decide   -- commitment R
example : k + c * w = 5 := by decide           -- response z

-- Verification of the honest run: g^z = R · A^c.
example : (2 : 𝔽₂₃) ^ (k + c * w).val = 8 * 16 ^ c.val := by decide

-- A second transcript on the same R, challenge c₂ = 2: z₂ = k + 2·w ≡ 0.
example : (2 : 𝔽₂₃) ^ ((k + 2 * w : ZMod 11)).val = 8 * 16 ^ (2 : ZMod 11).val := by decide

-- Extraction from the two transcripts recovers the witness:
-- w = (z₁ − z₂)·(c₁ − c₂)⁻¹ = 5·4⁻¹ = 5·3 ≡ 4 (mod 11).
example : ((5 : ZMod 11) - 0) * (6 - 2 : ZMod 11)⁻¹ = w := by decide
example : (2 : 𝔽₂₃) ^ (((5 : ZMod 11) - 0) * (6 - 2)⁻¹).val = 16 := by decide

-- Simulation without w: z = 5, c = 6 gives R = g^z · A^{-c} = 9 · 4⁻¹ = 8,
-- the same commitment as the real run with nonce k = 3.
example : (2 : 𝔽₂₃) ^ (5 : ZMod 11).val * ((16 : 𝔽₂₃) ^ (6 : ZMod 11).val)⁻¹ = 8 := by decide

end Schnorr.Example
