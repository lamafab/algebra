import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

-- ============================================================================
-- RSA — why (m^e)^d = m in (ZMod N)ˣ
-- ============================================================================
--
-- Correctness of RSA is one identity:
--   (m^e)^d = m^(e·d) = m   (in (ZMod N)ˣ)
--
-- First equality: monoid law, holds in any monoid.
-- Second equality: two tools:
--   * BÉZOUT  — produces d with e·d ≡ 1 (mod φ(N))  (computed in ℤ)
--   * EULER   — m^φ(N) = 1 in (ZMod N)ˣ             (Lagrange on a finite group)
--
-- Fermat is a special case of Euler (when N is prime) and is not
-- needed here. The internals of Euler's proof (Lagrange, CRT, etc.)
-- are out of scope.
--
-- TODO: Remove all references to Fermat and Lagrange in this file.

theorem monoid_law {M : Type*} [Monoid M] (m : M) (e d : Nat) :
    (m ^ e) ^ d = m ^ (e * d) := by
  rw [← pow_mul]

-- ============================================================================
-- Section 1: Parameters
-- ============================================================================

abbrev p : ℕ  := 11
abbrev q : ℕ  := 13
abbrev N : ℕ  := p * q              -- public modulus  = 143
abbrev φN : ℕ := (p - 1) * (q - 1)  -- totient = 120  (SECRET)
abbrev e : ℕ  := 7                  -- public exponent
abbrev d : ℕ  := 103                -- private exponent

example : N = 143            := by decide
example : Nat.totient N = φN := by decide
example : e * d % φN = 1     := by decide  -- ed ≡ 1 (mod φN)
example : Nat.gcd e φN = 1   := by decide

-- NOTATION:  "a ≡ b (mod n)" ⟺ "a - b is a multiple of n" ⟺ "[a] = [b]
-- in ℤ/(n)" (Ideals §6). Same fact, three vocabularies.

-- ============================================================================
-- Section 2: Bézout — where d comes from
-- ============================================================================
--
-- gcd(a, b) = 1 ⟹ ∃ x y, ax + by = 1. Computed by extended Euclidean.
-- For e = 7, φN = 120: 7·103 + 120·(-6) = 1. Take x mod φN ⟹ d = 103.

example : 7 * 103 - 120 * 6 = 1 := by decide

-- ============================================================================
-- Section 3: Fermat's Little Theorem (in 𝔽ₚ)
-- ============================================================================
--
-- For any a ∈ 𝔽_p: a^p = a  (Lagrange on the cyclic group 𝔽ₚˣ of order p-1.)

instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

example (a : ZMod 11) : a ^ 11 = a := ZMod.pow_card a
example (a : ZMod 13) : a ^ 13 = a := ZMod.pow_card a
example :   (2 : ZMod 11) ^ 10 = 1 := by decide

-- ============================================================================
-- Section 4: Euler — generalizing FLT to (ZMod N)ˣ
-- ============================================================================
--
-- For m coprime to N:  m^φ(N) = 1 in (ZMod N)ˣ.  Same Lagrange argument
-- applied to the unit group, which has order φ(N) by definition.
-- (For composite N, ZMod N isn't a field, so we MUST assume coprimality.)

example (x : (ZMod 143)ˣ) : x ^ Nat.totient 143 = 1 := ZMod.pow_totient x

-- ============================================================================
-- Section 5: Putting it together
-- ============================================================================
--
-- ed ≡ 1 (mod φN) means ed = 1 + φN·k for some k. Then m^(ed) unfolds:

theorem rsa_correctness {N : ℕ} (m : (ZMod N)ˣ) (e d k : ℕ)
    (h : e * d = 1 + Nat.totient N * k) : (m ^ e) ^ d = m :=
  calc (m ^ e) ^ d
      = m ^ (e * d)                     := by rw [← pow_mul]
    -- Bézout (via h)
    _ = m ^ (1 + Nat.totient N * k)     := by rw [h]
    -- Exponential laws
    _ = m ^ 1 * m ^ (Nat.totient N * k) := by rw [pow_add]
    _ = m * m ^ (Nat.totient N * k)     := by rw [pow_one]
    _ = m * (m ^ Nat.totient N) ^ k     := by rw [pow_mul]
    -- Euler
    _ = m * 1 ^ k                       := by rw [ZMod.pow_totient]
    _ = m * 1                           := by rw [one_pow]
    _ = m                               := by rw [mul_one]

-- Concrete: encrypt 42, decrypt back
abbrev m : ZMod 143       := 42
example : (m ^ e) ^ d = m := by native_decide
example : m ^ (e * d) = m := by native_decide

-- ============================================================================
-- Section 6: Why RSA is hard to break
-- ============================================================================
--
-- Public key (N, e) doesn't reveal d without φN — which requires factoring
-- N = p·q. Integer factoring (for N ~2048 bits) is conjectured HARD: no
-- known polynomial-time algorithm. Break the assumption, break the scheme.

-- FOOTNOTE: if gcd(m, N) > 1, our proof breaks. The Chinese Remainder
-- Theorem patches it (ZMod (p·q) ≅ ZMod p × ZMod q, FLT handles each
-- factor). In practice this case has probability ~2/N — never happens.

-- TODO: Note that RSA only requires Euler; Fermat, Lagrange, and CRT are
-- just components that can be used to prove Euler. That's outside the scope
-- of this document.
