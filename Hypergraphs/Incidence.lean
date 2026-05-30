import Hypergraphs.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

-- ============================================================================
-- The incidence matrix — the bridge from hypergraphs to linear codes
-- ============================================================================
--
-- This is KEYSTONE #1 of the Octra roadmap (see octra.md): it turns a
-- combinatorial `Hypergraph` into linear algebra over a ring R.  The incidence
-- matrix M has rows indexed by edges, columns by vertices, and
--
--     M[e, v] = 1  ⇔  v ∈ e        (else 0).
--
-- Read as a PARITY-CHECK MATRIX, M defines a linear code; the map
-- `x ↦ M.mulVec x` is the SYNDROME map that the coding/LPN layer builds on.
-- Two facts make this the right bridge:
--   * the syndrome map is LINEAR  (`syndrome_add`, `syndrome_smul`);
--   * a k-uniform hypergraph gives a CONSTANT row weight k  (`row_weight_uniform`)
--     — i.e. a k-regular parity-check, exactly the "k-uniform" code Octra wants.

namespace Hypergraph

open Matrix

variable {V : Type*} [DecidableEq V] (H : Hypergraph V)

-- The index types: the edges and vertices of H as Fintypes (they are Finsets,
-- so their subtypes are finite).

/-- Rows of the incidence matrix: the hyperedges of `H`. -/
abbrev EdgeIdx := {e // e ∈ H.edges}
/-- Columns of the incidence matrix: the vertices of `H`. -/
abbrev VertIdx := {v // v ∈ H.vertices}

/-- The incidence matrix of `H` over a ring `R`: `M[e,v] = 1` iff `v ∈ e`. -/
def incidence (R : Type*) [Zero R] [One R] :
    Matrix H.EdgeIdx H.VertIdx R :=
  fun e v => if (v : V) ∈ (e : Finset V) then 1 else 0

@[simp] theorem incidence_apply (R : Type*) [Zero R] [One R]
    (e : H.EdgeIdx) (v : H.VertIdx) :
    H.incidence R e v = if (v : V) ∈ (e : Finset V) then 1 else 0 := rfl

-- ============================================================================
-- The syndrome map and its linearity (KEYSTONE #1)
-- ============================================================================

/-- The syndrome map `x ↦ M·x` of the incidence/parity-check matrix. -/
def syndrome (R : Type*) [Semiring R] (x : H.VertIdx → R) : H.EdgeIdx → R :=
  (H.incidence R).mulVec x

/-- The syndrome map is additive — the defining property of a parity check. -/
theorem syndrome_add (R : Type*) [Semiring R] (x y : H.VertIdx → R) :
    H.syndrome R (x + y) = H.syndrome R x + H.syndrome R y := by
  simp only [syndrome, Matrix.mulVec_add]

/-- The syndrome map commutes with scaling (over a commutative ring — the code
    field 𝔽_q is commutative). -/
theorem syndrome_smul (R : Type*) [CommSemiring R] (c : R) (x : H.VertIdx → R) :
    H.syndrome R (c • x) = c • H.syndrome R x := by
  ext e
  simp only [syndrome, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

-- ============================================================================
-- Row weight = edge size; k-uniform ⇒ constant row weight k
-- ============================================================================

/-- The weight of row `e` (number of incident vertices) is `|e|`. -/
theorem row_weight (e : H.EdgeIdx) :
    ∑ v : H.VertIdx, H.incidence ℕ e v = (e : Finset V).card := by
  have he : (e : Finset V) ⊆ H.vertices := H.mem_vertices _ e.2
  simp only [incidence_apply]
  rw [Finset.sum_coe_sort H.vertices (fun v => if v ∈ (e : Finset V) then (1 : ℕ) else 0),
    Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr he]

/-- For a k-uniform hypergraph every row of the incidence matrix has weight `k`:
    the parity-check is `k`-regular. -/
theorem row_weight_uniform {k : ℕ} (hk : H.IsUniform k) (e : H.EdgeIdx) :
    ∑ v : H.VertIdx, H.incidence ℕ e v = k := by
  rw [H.row_weight e, hk _ e.2]

end Hypergraph
