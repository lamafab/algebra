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
-- are built from them.
def and  (e₁ e₂ : Finset V) : Finset V := e₁ ∩ e₂
def or   (e₁ e₂ : Finset V) : Finset V := e₁ ∪ e₂
def not  (e : Finset V)      : Finset V := eᶜ
def nand (e₁ e₂ : Finset V) : Finset V := (e₁ ∩ e₂)ᶜ
def nor  (e₁ e₂ : Finset V) : Finset V := (e₁ ∪ e₂)ᶜ
def xor  (e₁ e₂ : Finset V) : Finset V := (e₁ ∪ e₂) ∩ (e₁ ∩ e₂)ᶜ
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
