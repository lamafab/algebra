import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

-- ============================================================================
-- Logic Gates on Hyperedges
-- ============================================================================
--
-- Identify a hyperedge with the set of vertices it "activates": a vertex v is
-- active iff v ∈ e. Over a finite vertex type V the hyperedges then form a
-- Boolean algebra under intersection, union, and complement — so the usual
-- logic gates ARE the lattice operations, applied vertex-by-vertex (i.e. on
-- the characteristic vectors of the edges).
--
-- The complement \overline{e} is taken within the whole vertex set V, that is
-- eᶜ = Finset.univ \ e. (See Basic.lean for hyperedges inside a fixed H.)

namespace Hypergraph.Gate

variable {V : Type*} [Fintype V] [DecidableEq V]

-- The seven gates from the Octra docs. AND, OR, NOT are primitive; the rest
-- are built from them. Each definition is annotated with the docs' formula,
-- in which the bar \overline{·} is the complement within V — here `·ᶜ`.

-- AND — the intersection of two hyperedges, active only where BOTH are active.
-- Octra:  e_{and}(H) = e₁(H) ∩ e₂(H)
def and  (e₁ e₂ : Finset V) : Finset V := e₁ ∩ e₂

-- OR — the union of two hyperedges, active where AT LEAST ONE is active.
-- Octra:  e_{or}(H) = e₁(H) ∪ e₂(H)
def or   (e₁ e₂ : Finset V) : Finset V := e₁ ∪ e₂

-- NOT — inverting a hyperedge: active exactly where the input is INACTIVE.
-- Octra:  e_{not}(H) = \overline{e(H)}
def not  (e : Finset V)      : Finset V := eᶜ

-- NAND — AND followed by NOT: active unless both inputs are active.
-- Octra:  e_{nand}(H) = \overline{e₁(H) ∩ e₂(H)}
def nand (e₁ e₂ : Finset V) : Finset V := (e₁ ∩ e₂)ᶜ

-- NOR — OR followed by NOT: active only where neither input is active.
-- Octra:  e_{nor}(H) = \overline{e₁(H) ∪ e₂(H)}
def nor  (e₁ e₂ : Finset V) : Finset V := (e₁ ∪ e₂)ᶜ

-- XOR — active where EXACTLY ONE input is active.
-- Octra:  e_{xor}(H) = (e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}
def xor  (e₁ e₂ : Finset V) : Finset V := (e₁ ∪ e₂) ∩ (e₁ ∩ e₂)ᶜ

-- XNOR — XOR followed by NOT: active where the two inputs AGREE.
-- Octra:  e_{xnor}(H) = \overline{(e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}}
def xnor (e₁ e₂ : Finset V) : Finset V := ((e₁ ∪ e₂) ∩ (e₁ ∩ e₂)ᶜ)ᶜ

-- ============================================================================
-- Section 1: The "N" gates are the negations of their bases (by definition)
-- ============================================================================

theorem nand_eq_not_and (e₁ e₂ : Finset V) : nand e₁ e₂ = not (and e₁ e₂) := rfl
theorem nor_eq_not_or   (e₁ e₂ : Finset V) : nor  e₁ e₂ = not (or  e₁ e₂) := rfl
theorem xnor_eq_not_xor (e₁ e₂ : Finset V) : xnor e₁ e₂ = not (xor e₁ e₂) := rfl

-- ============================================================================
-- Section 2: De Morgan — NAND is an OR of NOTs, NOR is an AND of NOTs
-- ============================================================================

theorem nand_eq_or_not (e₁ e₂ : Finset V) : nand e₁ e₂ = or (not e₁) (not e₂) := by
  ext v; simp only [nand, or, not, Finset.mem_compl, Finset.mem_inter, Finset.mem_union]; tauto

theorem nor_eq_and_not (e₁ e₂ : Finset V) : nor e₁ e₂ = and (not e₁) (not e₂) := by
  ext v; simp only [nor, and, not, Finset.mem_compl, Finset.mem_union, Finset.mem_inter]; tauto

-- NOT is an involution: ¬¬e = e
theorem not_not (e : Finset V) : not (not e) = e := by simp only [not, compl_compl]

-- ============================================================================
-- Section 3: Truth-table semantics — which vertices each gate activates
-- ============================================================================
--
-- XOR activates exactly the vertices active in precisely one input; XNOR
-- activates the vertices on which the two inputs agree.

theorem mem_xor (v : V) (e₁ e₂ : Finset V) :
    v ∈ xor e₁ e₂ ↔ (v ∈ e₁ ∧ v ∉ e₂) ∨ (v ∉ e₁ ∧ v ∈ e₂) := by
  simp only [xor, Finset.mem_inter, Finset.mem_union, Finset.mem_compl]; tauto

theorem mem_xnor (v : V) (e₁ e₂ : Finset V) :
    v ∈ xnor e₁ e₂ ↔ (v ∈ e₁ ↔ v ∈ e₂) := by
  simp only [xnor, Finset.mem_compl, Finset.mem_inter, Finset.mem_union]; tauto

-- ============================================================================
-- Section 4: A worked example over the 4-vertex universe {0, 1, 2, 3}
-- ============================================================================
--
-- Take e₁ = {0, 1} and e₂ = {1, 2}; complements are within V = {0, 1, 2, 3}.

example : and  ({0, 1} : Finset (Fin 4)) {1, 2} = {1}       := by decide
example : or   ({0, 1} : Finset (Fin 4)) {1, 2} = {0, 1, 2} := by decide
example : not  ({0, 1} : Finset (Fin 4))        = {2, 3}    := by decide
example : nand ({0, 1} : Finset (Fin 4)) {1, 2} = {0, 2, 3} := by decide
example : nor  ({0, 1} : Finset (Fin 4)) {1, 2} = {3}       := by decide
example : xor  ({0, 1} : Finset (Fin 4)) {1, 2} = {0, 2}    := by decide
example : xnor ({0, 1} : Finset (Fin 4)) {1, 2} = {1, 3}    := by decide

end Hypergraph.Gate
