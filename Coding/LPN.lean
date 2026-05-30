import Coding.LinearCode
import Mathlib.Tactic

-- ============================================================================
-- Learning Parity with Noise (LPN) — the hardness assumption  (Phase 2)
-- ============================================================================
--
-- LPN: given many samples (aᵢ, ⟨aᵢ, s⟩ ⊕ eᵢ) with secret s and sparse Bernoulli
-- noise eᵢ, recovering s is conjectured HARD (and is the dual of random
-- syndrome decoding, Coding/LinearCode.lean).  This is the post-quantum
-- assumption replacing factoring — it is what makes Octra's scheme more than
-- Paillier.
--
-- We do NOT prove LPN hard (no one can; it is an assumption).  We POSTULATE it
-- as an axiom and let Phase-3 security be a REDUCTION to it (`LPN_hard → IND-CPA`,
-- keystone #4).  The precise distribution/parameters are filled in once the
-- spec (Phase 0) is pinned; for now `LPNHard` is an opaque assumption.
--
-- Keystone #5 (Threshold.lean) will connect this to the random hypergraph:
-- at the MIPT-chosen parameters the syndrome-decoding instance lands in LPN's
-- hard regime.

namespace Octra.Coding

/-- The LPN hardness assumption (to be made parametric/precise in Phase 2). -/
axiom LPNHard : Prop

/-- We postulate LPN is hard. Every security theorem is stated *relative* to
    this axiom — it is the trust root of the scheme, never proved. -/
axiom lpn_hard : LPNHard

end Octra.Coding
