import Crypto.HFHE.Defs
import Mathlib.Tactic

-- ============================================================================
-- HFHE — decryption correctness  (Phase 3, KEYSTONE #2)
-- ============================================================================
--
-- The analogue of `Paillier.decrypt_correct`, but EXACT: equality in 𝔽, no
-- congruence, no noise bound.  Two steps, mirroring Paillier:
--   * `decrypt_strip` — the proven ALGEBRA: every edge weight is its intended
--     coefficient times the layer mask (`w = coef · R`), so dividing by `R`
--     cancels it edge-by-edge through the sum.  Needs only `R ≠ 0`.
--   * `decrypt_correct` — add the construction KERNEL (the mask-stripped edge sum
--     telescopes to the message) and decryption returns it.  `kernel` is what the
--     full `synth` provides by construction (signal split `v − Σδ` + noise tuples);
--     it is the deferred piece, exactly like Paillier's number-theoretic kernel.
-- `encrypt1_correct` closes the K=1 noise-free case unconditionally.

namespace Octra.HFHE

-- Throughout: `S` = number of SIMD slots (a plaintext / slot-vector is `Fin S → F`);
-- `F` = the field 𝔽 (intended 𝔽_p, p = 2¹²⁷−1 — see Crypto/Field127.lean).
variable {S : ℕ} {F : Type*} [Field F]

/-- Mask cancellation through the edge sum.  If every edge's weight is the
    intended coefficient times its layer's mask, and every mask is nonzero, then
    decryption strips the masks exactly. -/
theorem decrypt_strip
    (g : F)                          -- carrier base; edge `e` weighs `g ^ e.idx`
    (R : ℕ → (Fin S → F))            -- secret mask: `R l j` = mask of layer `l` at slot `j`
    (c : Cipher S F)                 -- the ciphertext (DAG of layers + edges + `c0`)
    (j : Fin S)                      -- the slot being decrypted
    (coef : Edge S F → (Fin S → F))  -- intended unmasked coefficient: `coef e j`
    (hw : ∀ e ∈ c.edges, e.w j = coef e j * R e.layer j)  -- every weight = coefficient · mask
    (hR : ∀ e ∈ c.edges, R e.layer j ≠ 0)                 -- every mask invertible (field, not group)
  :
    decrypt g R c j
      = c.c0 j + (c.edges.map fun e => sgn e.sign * coef e j * g ^ e.idx).sum := by
  unfold decrypt
  have hmap :
      (c.edges.map fun e => sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹)
        = (c.edges.map fun e => sgn e.sign * coef e j * g ^ e.idx) := by
    apply List.map_congr_left
    intro e he
    have hne := hR e he
    rw [hw e he]
    field_simp
  rw [hmap]

/-- KEYSTONE #2 — exact decryption correctness.  Given the construction guarantee
    (`kernel`) that the mask-stripped edge sum telescopes to the message,
    decryption returns it exactly. -/
theorem decrypt_correct
    (g : F)                          -- carrier base; edge `e` weighs `g ^ e.idx`
    (R : ℕ → (Fin S → F))            -- secret mask: `R l j` = mask of layer `l` at slot `j`
    (c : Cipher S F)                 -- the ciphertext
    (j : Fin S)                      -- the slot being decrypted
    (coef : Edge S F → (Fin S → F))  -- intended unmasked coefficient: `coef e j`
    (v : Fin S → F)                  -- the plaintext (the slot-vector we expect back)
    (hw : ∀ e ∈ c.edges, e.w j = coef e j * R e.layer j)  -- every weight = coefficient · mask
    (hR : ∀ e ∈ c.edges, R e.layer j ≠ 0)                 -- every mask invertible (field, not group)
    (kernel : c.c0 j + (c.edges.map fun e => sgn e.sign * coef e j * g ^ e.idx).sum = v j)
      -- construction guarantee: mask-stripped edge sum telescopes to `v` (deferred; comes from `synth`)
  :
    decrypt g R c j = v j := by
  rw [decrypt_strip g R c j coef hw hR, kernel]

/-- The K=1 noise-free encryption decrypts exactly — a fully closed instance of
    keystone #2 (the single edge telescopes trivially, so no `kernel` hypothesis
    is needed). -/
theorem encrypt1_correct
    (g : F)                -- carrier base
    (R : ℕ → (Fin S → F))  -- secret mask (only layer 0 is used by `encrypt1`)
    (idx : ℕ)              -- carrier position the single signal edge is placed at
    (v : Fin S → F)        -- the plaintext
    (j : Fin S)            -- the slot being decrypted
    (hg : g ≠ 0)           -- carrier nonzero ⇒ `g ^ idx` invertible
    (hR : R 0 j ≠ 0)       -- layer-0 mask invertible
  :
    decrypt g R (encrypt1 g R idx v) j = v j := by
  have hgi : (g ^ idx) ≠ 0 := pow_ne_zero _ hg
  unfold decrypt encrypt1
  simp only [sgn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  field_simp

end Octra.HFHE
