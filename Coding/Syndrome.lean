import Hypergraphs.Incidence
import Coding.LinearCode
import Mathlib.Tactic

-- ============================================================================
-- The hypergraph syndrome map = a linear code  (Phase 2)
-- ============================================================================
--
-- This file is the hinge of the HARDNESS track: it says the combinatorial
-- syndrome map of a hypergraph (Hypergraphs/Incidence.lean) is LITERALLY the
-- parity-check syndrome of a linear code (Coding/LinearCode.lean).  So
-- "decode this hypergraph syndrome" = "solve a syndrome-decoding instance",
-- and the LPN hardness assumption (Coding/LPN.lean) applies verbatim.

namespace Octra.Coding

open Hypergraph

variable {V : Type*} [DecidableEq V] (H : Hypergraph V) (R : Type*) [Semiring R]

/-- The hypergraph syndrome map is exactly the linear-code syndrome of the
    incidence matrix used as a parity-check matrix.  (Keystone #1, in coding
    language.) -/
theorem hypergraph_syndrome_eq (x : H.VertIdx → R) :
    H.syndrome R x = Coding.syndrome (H.incidence R) x := rfl

/-- The hypergraph-decoding problem: recover a low-weight `e` on the vertices
    explaining an observed edge-syndrome `σ`.  This is the concrete instance
    whose hardness the random k-uniform hypergraph (Phase 1) is chosen to
    guarantee. -/
def IsHypergraphDecodingSolution [DecidableEq R]
    (σ : H.EdgeIdx → R) (w : ℕ) (e : H.VertIdx → R) : Prop :=
  IsSyndromeDecodingSolution (H.incidence R) σ w e

end Octra.Coding
