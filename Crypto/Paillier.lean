import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

-- ============================================================================
-- Paillier — additively homomorphic encryption
-- ============================================================================
--
-- Plaintexts live in ZMod n, ciphertexts in ZMod n².  With the standard
-- simplification g = n + 1 the scheme is:
--
--   keygen      n = p·q,  λ = lcm(p-1, q-1),  µ = λ⁻¹ (mod n)
--   encrypt m   c = gᵐ · rⁿ           (mod n²),  r coprime to n  (RANDOM)
--   add c₁ c₂   c₁ · c₂               (mod n²)
--   decrypt c   L(c^λ) · µ            (mod n),   L(x) = (x-1)/n
--
-- The whole thing rests on two facts about arithmetic mod n²:
--
--   BINOMIAL    (1+n)^k ≡ 1 + k·n     (mod n²)   — pure algebra
--   CARMICHAEL  rⁿᐧλ   ≡ 1             (mod n²)   — number theory
--
-- This file proves the ALGEBRA that turns those two facts into decryption
-- correctness — in particular it handles the awkward L(x) = (x-1)/n integer
-- division, whose exactness is the subtle part.  The CARMICHAEL kernel is
-- deferred (`sorry`); BINOMIAL is proved here since it needs no number theory.

namespace Paillier

-- ============================================================================
-- Section 1: The L-function and decryption correctness (THE ALGEBRA)
-- ============================================================================
--
-- Work over ℤ with `a ≡ b [ZMOD m]`.  The reason we can't just stay inside
-- `ZMod n²` is L: dividing by n is not an operation on `ZMod n²` (n isn't a
-- unit there).  So decryption inherently steps out to ℤ, divides, and steps
-- back mod n — and the division is only meaningful because it's EXACT.

/-- The Paillier L-function `L(x) = (x-1)/n` (integer division). -/
def L (n x : ℤ) : ℤ := (x - 1) / n

-- The crux.  `cl` stands for the integer `c^λ`; the `kernel` hypothesis is
-- exactly what BINOMIAL and CARMICHAEL combine to give (see Section 3).  Given
-- it, decryption is pure algebra: the division by n comes out exact, and the
-- µ = λ⁻¹ step collapses λ·µ to 1.
theorem decrypt_correct (n lam mu m cl : ℤ) (hn : n ≠ 0)
    (kernel : cl ≡ 1 + m * lam * n [ZMOD n * n])
    (hinv : lam * mu ≡ 1 [ZMOD n]) :
    L n cl * mu ≡ m [ZMOD n] := by
  -- kernel gives `cl = 1 + m·λ·n - n²·t`, so (cl-1)/n is the EXACT quotient.
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp kernel
  have hLc : L n cl = m * lam - n * t := by
    unfold L
    rw [show cl - 1 = n * (m * lam - n * t) from by linear_combination -ht]
    exact Int.mul_ediv_cancel_left _ hn
  rw [hLc]
  -- λ·µ ≡ 1 (mod n), so (m·λ - n·t)·µ ≡ m·(λ·µ) ≡ m.
  obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hinv
  rw [Int.modEq_iff_dvd]
  exact ⟨m * s + t * mu, by linear_combination m * hs⟩

-- ============================================================================
-- Section 2: Additive homomorphism (a thin corollary of the above)
-- ============================================================================
--
-- The product of two ciphertexts is an encryption of the SUM of the
-- plaintexts, so once `decrypt_correct` holds for every plaintext, additive
-- homomorphism is immediate — just instantiate it at m := m₁ + m₂.  (That the
-- product really encrypts the sum is itself a kernel-level fact, folded into
-- `kernel` below.)
theorem add_correct (n lam mu m₁ m₂ cl : ℤ) (hn : n ≠ 0)
    (kernel : cl ≡ 1 + (m₁ + m₂) * lam * n [ZMOD n * n])
    (hinv : lam * mu ≡ 1 [ZMOD n]) :
    L n cl * mu ≡ m₁ + m₂ [ZMOD n] :=
  decrypt_correct n lam mu (m₁ + m₂) cl hn kernel hinv

-- ============================================================================
-- Section 3: The two kernels feeding `kernel`
-- ============================================================================

-- BINOMIAL — pure algebra, no number theory.  This is half of what produces
-- the `kernel` hypothesis: raising g = 1+n to a power only ever contributes a
-- linear term mod n².
theorem binomial_modSq (n : ℤ) (k : ℕ) :
    (1 + n) ^ k ≡ 1 + (k : ℤ) * n [ZMOD n * n] := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc (1 + n) ^ (k + 1)
        = (1 + n) ^ k * (1 + n)            := by rw [pow_succ]
      _ ≡ (1 + (k : ℤ) * n) * (1 + n) [ZMOD n * n] := ih.mul_right _
      _ ≡ 1 + ((k : ℤ) + 1) * n [ZMOD n * n] :=
            Int.modEq_iff_dvd.mpr ⟨-(k : ℤ), by ring⟩
      _ = 1 + ((k + 1 : ℕ) : ℤ) * n        := by push_cast; ring

-- CARMICHAEL — the number-theoretic kernel.  For r coprime to n, the random
-- mask rⁿ vanishes after raising to λ.  Proof needs the structure of
-- (ZMod n²)ˣ (Carmichael's theorem via CRT on the prime-power factors); it is
-- deferred for now — this is the "kernel stuff" to be handled later.
-- (λ = lcm(p-1,q-1) and the primality of p, q will become hypotheses when we
-- discharge this; for now the statement records only what the algebra consumes.)
theorem carmichael_modSq (n lam : ℤ) (r : ℤ) (hr : IsCoprime r n) (k : ℕ)
    (hk : (k : ℤ) = n * lam) :
    r ^ k ≡ 1 [ZMOD n * n] := by
  sorry

end Paillier

-- ============================================================================
-- Section 4: A concrete, executable instance (sanity check on real numbers)
-- ============================================================================
--
-- The OCaml reference uses p = 61, q = 53.  Everything below actually runs:
-- `native_decide` evaluates encryption and decryption end-to-end in ZMod n².

namespace Paillier.Example

abbrev p : ℕ   := 61
abbrev q : ℕ   := 53
abbrev n : ℕ   := p * q                    -- 3233   (public modulus)
abbrev nn : ℕ  := n * n                    -- 10452289 = n²
abbrev lam : ℕ := Nat.lcm (p - 1) (q - 1)  -- 780    (Carmichael λ, SECRET)
abbrev g : ℕ   := n + 1                    -- 3234   = 1 + n
abbrev mu : ℕ  := 1173                     -- λ⁻¹ (mod n)

example : n = 3233            := by decide
example : lam = 780           := by decide
example : Nat.gcd lam n = 1   := by decide
example : (lam * mu) % n = 1  := by decide   -- µ really is λ⁻¹ mod n

/-- Encrypt `m` with randomness `r` (coprime to n): c = gᵐ · rⁿ in ZMod n². -/
def encrypt (m r : ℕ) : ZMod nn := (g : ZMod nn) ^ m * (r : ZMod nn) ^ n

/-- Decrypt: `L(c^λ) · µ (mod n)`, with L stepping out to ℕ to divide by n. -/
def decrypt (c : ZMod nn) : ℕ := (((c ^ lam).val - 1) / n * mu) % n

/-- Homomorphic addition: multiply ciphertexts in ZMod n². -/
def homAdd (c₁ c₂ : ZMod nn) : ZMod nn := c₁ * c₂

-- Round-trip: decrypt ∘ encrypt = id  (for plaintexts < n)
example : decrypt (encrypt 111 2) = 111 := by native_decide
example : decrypt (encrypt 42 5)  = 42  := by native_decide

-- Additive homomorphism: 111 + 222 = 333, computed under encryption
example : decrypt (homAdd (encrypt 111 2) (encrypt 222 3)) = 333 := by native_decide

end Paillier.Example
