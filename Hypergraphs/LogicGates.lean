import Hypergraphs.Basic
import Mathlib.Tactic

-- ============================================================================
-- Logic Gates on Hyperedges
-- ============================================================================
--
-- Fix a hypergraph H = (V, E). A hyperedge is the set of vertices it
-- "activates" (v active ⇔ v ∈ e; see `Active`/`Inactive` in Basic.lean). The
-- Octra gates combine hyperedges vertex-by-vertex. Intersection and union need
-- no extra data, but the bar \overline{·} — inactivity — is exactly H's set of
-- inactive vertices:
--
--     \overline{e} = H.inactive e = H.vertices \ e     (vertices OF H not in e)
--
-- So the complement's universe is H.vertices, not the whole type. Consequently
-- every gate lands back inside H.vertices, i.e. produces a genuine hyperedge of
-- H (Section 0).

namespace Hypergraph.Gate

variable {V : Type*} [DecidableEq V]

-- AND — the intersection of two hyperedges, creating a new hyperedge that is
-- active only when both original hyperedges are active.
--     e_{and}(H) = e₁(H) ∩ e₂(H)
def and (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.active (e₁ ∩ e₂)

-- OR — a union of hyperedges, where a new hyperedge is active if at least one
-- of the original hyperedges is active.
--     e_{or}(H) = e₁(H) ∪ e₂(H)
def or (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.active (e₁ ∪ e₂)

-- NOT — inverting a hyperedge: a new hyperedge becomes active when the original
-- one is inactive.
--     e_{not}(H) = \overline{e(H)}
def not  (H : Hypergraph V) (e : Finset V) : Finset V := H.inactive e

-- NAND — a mix of and and not operations, with the nand hyperedge active when
-- the and hyperedge is inactive.
--     e_{nand}(H) = \overline{e₁(H) ∩ e₂(H)}
def nand (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.inactive (e₁ ∩ e₂)

-- NOR — the union of or and not activates the nor hyperedge when the or
-- hyperedge is inactive.
--     e_{nor}(H) = \overline{e₁(H) ∪ e₂(H)}
def nor  (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.inactive (e₁ ∪ e₂)

-- XOR — the combination of two hyperedges, `and` and `or`, is activated only
-- when only one of the original hyperedges is active.
--     e_{xor}(H) = (e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}
def xor  (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V :=
  (e₁ ∪ e₂) ∩ H.inactive (e₁ ∩ e₂)

-- XNOR — integration of xor and not operations, where the xnor hyperedge is
-- active when the xor hyperedge becomes inactive.
--     e_{xnor}(H) = \overline{(e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}}
def xnor (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V :=
  H.inactive ((e₁ ∪ e₂) ∩ H.inactive (e₁ ∩ e₂))

variable (H : Hypergraph V)

-- ============================================================================
-- Section 0: Every gate yields a hyperedge of H (a subset of H.vertices)
-- ============================================================================
--
-- This is what "explicit for H" buys us: the gates are closed on H's edges.
-- (AND/OR need the inputs to be edges of H; the complement-based ones land in
-- H.vertices unconditionally.)

theorem and_subset (e₁ e₂ : Finset V) (he₁ : e₁ ⊆ H.vertices) :
    and e₁ e₂ ⊆ H.vertices := Finset.inter_subset_left.trans he₁
theorem or_subset (e₁ e₂ : Finset V) (he₁ : e₁ ⊆ H.vertices) (he₂ : e₂ ⊆ H.vertices) :
    or e₁ e₂ ⊆ H.vertices := Finset.union_subset he₁ he₂
theorem not_subset  (e : Finset V)     : not  H e     ⊆ H.vertices := H.inactive_subset _
theorem nand_subset (e₁ e₂ : Finset V) : nand H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem nor_subset  (e₁ e₂ : Finset V) : nor  H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem xnor_subset (e₁ e₂ : Finset V) : xnor H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem xor_subset  (e₁ e₂ : Finset V) : xor  H e₁ e₂ ⊆ H.vertices :=
  Finset.inter_subset_right.trans (H.inactive_subset _)

-- ============================================================================
-- Section 1: The "N" gates are the negations of their bases (by definition)
-- ============================================================================

theorem nand_eq_not_and (e₁ e₂ : Finset V) : nand H e₁ e₂ = not H (and e₁ e₂) := rfl
theorem nor_eq_not_or   (e₁ e₂ : Finset V) : nor  H e₁ e₂ = not H (or  e₁ e₂) := rfl
theorem xnor_eq_not_xor (e₁ e₂ : Finset V) : xnor H e₁ e₂ = not H (xor H e₁ e₂) := rfl

-- ============================================================================
-- Section 2: De Morgan — NAND is an OR of NOTs, NOR is an AND of NOTs
-- ============================================================================

theorem nand_eq_or_not (e₁ e₂ : Finset V) : nand H e₁ e₂ = or (not H e₁) (not H e₂) := by
  ext v; simp only [nand, or, not, inactive, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto

theorem nor_eq_and_not (e₁ e₂ : Finset V) : nor H e₁ e₂ = and (not H e₁) (not H e₂) := by
  ext v; simp only [nor, and, not, inactive, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto

-- NOT is an involution — but only for genuine hyperedges of H (e ⊆ H.vertices);
-- this is exactly where the complement's universe matters.
theorem not_not (e : Finset V) (he : e ⊆ H.vertices) : not H (not H e) = e := by
  ext v
  simp only [not, inactive, Finset.mem_sdiff]
  refine ⟨fun h => ?_, fun hv => ⟨he hv, fun h => h.2 hv⟩⟩
  by_contra hv
  exact h.2 ⟨h.1, hv⟩

-- ============================================================================
-- Section 3: Truth-table semantics — which vertices each gate activates
-- ============================================================================
--
-- Note the explicit `v ∈ H.vertices`: a vertex outside H is never activated by
-- a complement-based gate, since the complement only ranges over H.vertices.

theorem mem_xor (e₁ e₂ : Finset V) (v : V) :
    v ∈ xor H e₁ e₂ ↔
      v ∈ H.vertices ∧ ((Active e₁ v ∧ ¬ Active e₂ v) ∨ (¬ Active e₁ v ∧ Active e₂ v)) := by
  simp only [xor, inactive, Active, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto

theorem mem_xnor (e₁ e₂ : Finset V) (v : V) :
    v ∈ xnor H e₁ e₂ ↔ v ∈ H.vertices ∧ (Active e₁ v ↔ Active e₂ v) := by
  simp only [xnor, inactive, Active, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto

-- ============================================================================
-- Section 4: A worked example over a hypergraph whose vertices are a PROPER
-- subset of the type — so "within H" is visible
-- ============================================================================
--
-- H has vertices {0, 1, 2} (NOT vertex 3) and edges e₁ = {0, 1}, e₂ = {1, 2}.
-- Complements are taken within {0, 1, 2}, so vertex 3 never appears — unlike a
-- whole-type complement, which would also drag in 3.

def exampleH : Hypergraph (Fin 4) where
  vertices     := {0, 1, 2}
  edges        := {{0, 1}, {1, 2}}
  mem_vertices := by decide

example : and  ({0, 1} : Finset (Fin 4)) {1, 2} = {1}       := by decide
example : or   ({0, 1} : Finset (Fin 4)) {1, 2} = {0, 1, 2} := by decide
example : not  exampleH {0, 1}        = ({2}     : Finset (Fin 4)) := by decide  -- not {2,3}!
example : nand exampleH {0, 1} {1, 2} = ({0, 2}  : Finset (Fin 4)) := by decide
example : nor  exampleH {0, 1} {1, 2} = (∅       : Finset (Fin 4)) := by decide
example : xor  exampleH {0, 1} {1, 2} = ({0, 2}  : Finset (Fin 4)) := by decide
example : xnor exampleH {0, 1} {1, 2} = ({1}     : Finset (Fin 4)) := by decide

end Hypergraph.Gate
