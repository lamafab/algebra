import Hypergraphs.Basic
import Mathlib.Tactic

-- ============================================================================
-- Random k-uniform hypergraphs  (Phase 1)
-- ============================================================================
--
-- The hardness of Octra's syndrome code comes from sampling the underlying
-- hypergraph at RANDOM.  This file fixes the model and parameters; the sharp
-- THRESHOLD results that make the decoding instance hard live in
-- Hypergraphs/Threshold.lean.
--
-- TODO (Phase 1):
--   * edge distribution: H(n, m, k) — m edges drawn uniformly from the
--     k-subsets of an n-vertex set (the "dense random k-uniform" model);
--   * density parameter c = m / n and its role in the threshold;
--   * connect a sampled `Params` to a concrete `Hypergraph`.

namespace Hypergraph.Random

/-- Parameters of the random k-uniform model `H(n, m, k)`. -/
structure Params where
  /-- number of vertices -/
  n : ℕ
  /-- number of hyperedges -/
  m : ℕ
  /-- uniformity: every edge has exactly `k` vertices -/
  k : ℕ

/-- Edge density `c = m / n` (as a rational), the knob the threshold theory turns. -/
def Params.density (P : Params) : ℚ := (P.m : ℚ) / (P.n : ℚ)

end Hypergraph.Random
