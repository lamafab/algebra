import Crypto.HFHE.Correctness
import Mathlib.Tactic

-- ============================================================================
-- HFHE — additive & multiplicative homomorphism  (Phase 3, KEYSTONE #3)
-- ============================================================================
--
-- The payoff: computing on ciphertexts computes on plaintexts.  Like keystone
-- #2 (Correctness.lean) these are EXACT identities in 𝔽 — no noise budget.
--
-- This file is also the place to STUDY how `decrypt` and the parameters from
-- Correctness.lean (`g`, `R`, `c`, `j`) get used: `decrypt_cAdd` below applies
-- `decrypt` to two ciphertexts and their `cAdd`, so you can see the moving parts
-- in action.
--
--   ✓ ADD  — proved below (`decrypt_cAdd`).  Easy: `decrypt` is `c0 + Σ over
--            edges`, and `cAdd` concatenates edge lists + adds `c0`, so it
--            distributes over `++` via `List.map_append` / `List.sum_append`.
--   ▢ SUB  — `cNeg`/`cSub` (negate signs/weights, then add) — same shape, easy.
--   ▢ MUL  — the deep one: `ct_mul` adds PROD layers whose mask is `R(prod a b) =
--            R a · R b`; correctness is the `(a0+gA)(b0+gB)` expansion.  Needs a
--            `cMul` definition first (see SPEC.md §6 and octra.md "next steps").

namespace Octra.HFHE

-- Same conventions as Correctness.lean: `S` = SIMD slots, `F` = the field.
variable {S : ℕ} {F : Type*} [Field F]

/-- **Additive homomorphism (half of keystone #3).**  Decrypting the sum of two
    ciphertexts yields the sum of their plaintexts — EXACT, with no hypotheses
    (not even `R ≠ 0`): addition never divides by a mask, so nothing can fail.

    Parameters mirror `decrypt` / Correctness.lean:
    * `g`  — carrier base (edges weigh `g ^ idx`);
    * `R`  — the per-layer mask (`R l j` = mask of layer `l` at slot `j`);
    * `a`, `b` — the two ciphertexts being added;
    * `j`  — the slot.

    Proof: `cAdd` sets `edges := a.edges ++ b.edges` and `c0 := a.c0 + b.c0`, and
    `decrypt` is `c0 j + (edges.map …).sum`, so `List.map_append` +
    `List.sum_append` split the sum and `ring` reassociates. -/
theorem decrypt_cAdd (g : F) (R : ℕ → (Fin S → F)) (a b : Cipher S F) (j : Fin S) :
    decrypt g R (cAdd a b) j = decrypt g R a j + decrypt g R b j := by
  simp only [decrypt, cAdd, List.map_append, List.sum_append]
  ring

end Octra.HFHE
