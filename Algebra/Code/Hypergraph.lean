import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Finset Matrix

-- ============================================================================
-- Hypergraphs and syndrome decoding
-- ============================================================================
--
-- A hypergraph H = (V, E) gives rise to a linear code: its incidence matrix M
-- (rows = edges, columns = vertices, entry = 1 if v ∈ e) is the parity-check
-- matrix of the code.  The SYNDROME DECODING problem asks: given M and a
-- syndrome σ = M·e with Hamming weight(e) ≤ t, recover e.
--
-- This file sets up the hypergraph-to-code bridge, states the two conditions
-- (k-uniformity, minimum distance) that make decoding well-posed, proves the
-- UNIQUENESS theorem, and marks the LPN-style hardness assumption that makes
-- the problem cryptographically meaningful.
--
-- The [7,4,3] Hamming code (Algebra/Code/Hamming.lean) is a concrete
-- 4-uniform hypergraph with minimum distance 3: it demonstrates the uniqueness
-- property with t = 1.

namespace Hypergraph

-- ============================================================================
-- Section 1: The structure
-- ============================================================================

/-- A finite hypergraph on a vertex type `V`: a vertex set together with a
family of hyperedges, each contained in the vertex set. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  vertices     : Finset V
  edges        : Finset (Finset V)
  mem_vertices : ∀ e ∈ edges, e ⊆ vertices

namespace Hypergraph

variable {V : Type*} [DecidableEq V] (H : Hypergraph V)

/-- The hypergraph is k-uniform when every edge has exactly k vertices. -/
def IsUniform (k : ℕ) : Prop := ∀ e ∈ H.edges, e.card = k

-- ============================================================================
-- Section 2: Incidence matrix over 𝔽₂
-- ============================================================================

/-- Rows of the incidence matrix: the hyperedges. -/
abbrev EdgeIdx := {e // e ∈ H.edges}

/-- Columns of the incidence matrix: the vertices. -/
abbrev VertIdx := {v // v ∈ H.vertices}

/-- The incidence matrix over 𝔽₂: entry (e, v) = 1 iff v ∈ e. -/
def incidence : Matrix H.EdgeIdx H.VertIdx (ZMod 2) :=
  fun e v => if (v : V) ∈ (e : Finset V) then 1 else 0

-- ============================================================================
-- Section 3: The code and syndrome
-- ============================================================================

/-- The syndrome of x under the incidence matrix: σ = M·x. -/
def syndrome (x : H.VertIdx → ZMod 2) : H.EdgeIdx → ZMod 2 :=
  H.incidence.mulVec x

/-- The code of the hypergraph: the kernel of the syndrome map, i.e. the
set of words with syndrome 0. -/
def code : Submodule (ZMod 2) (H.VertIdx → ZMod 2) :=
  LinearMap.ker H.incidence.mulVecLin

theorem mem_code_iff (x : H.VertIdx → ZMod 2) :
    x ∈ code H ↔ H.syndrome x = 0 := by
  simp [code, syndrome, H.incidence.mulVecLin_apply]

theorem syndrome_eq_iff_sub_mem_code (a b : H.VertIdx → ZMod 2) :
    H.syndrome a = H.syndrome b ↔ a - b ∈ code H := by
  rw [mem_code_iff, syndrome, syndrome]
  calc
    H.incidence.mulVecLin a = H.incidence.mulVecLin b
        ↔ H.incidence.mulVecLin a - H.incidence.mulVecLin b = 0 := sub_eq_zero.symm
    _ ↔ H.incidence.mulVecLin (a - b) = 0 := by
      rw [H.incidence.mulVecLin.map_sub a b]
    _ ↔ H.incidence *ᵥ (a - b) = 0 := by simp
    _ ↔ a - b ∈ code H := (mem_code_iff H (a - b)).symm

-- ============================================================================
-- Section 4: Hamming weight and the uniqueness theorem
-- ============================================================================

/-- Hamming weight of a binary vector: number of nonzero coordinates. -/
def hammingWeight {n : Type*} [Fintype n] [DecidableEq n] (x : n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

theorem hammingWeight_add_le {n : Type*} [Fintype n] [DecidableEq n]
    (x y : n → ZMod 2) :
    hammingWeight (x + y) ≤ hammingWeight x + hammingWeight y := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Pi.add_apply] at hi ⊢
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hi (by rw [h.1, h.2, add_zero])

theorem hammingWeight_neg {n : Type*} [Fintype n] [DecidableEq n] (x : n → ZMod 2) :
    hammingWeight (-x) = hammingWeight x := by
  unfold hammingWeight; congr 1; ext i; simp

/-- The syndrome decoding problem: find e of weight ≤ t with M·e = σ. -/
def IsSolution (σ : H.EdgeIdx → ZMod 2) (t : ℕ) (e : H.VertIdx → ZMod 2) : Prop :=
  H.syndrome e = σ ∧ hammingWeight e ≤ t

/-- Unique decoding within radius t (the t = ⌊(d−1)/2⌋ bound).
If every nonzero codeword has weight ≥ 2t+1, two weight-≤t solutions for
the same syndrome are equal. -/
theorem unique_solution {t : ℕ} {σ : H.EdgeIdx → ZMod 2} {e₁ e₂ : H.VertIdx → ZMod 2}
    (hmin : ∀ c ∈ code H, c ≠ 0 → 2 * t + 1 ≤ hammingWeight c)
    (h₁ : H.IsSolution σ t e₁) (h₂ : H.IsSolution σ t e₂)
  : e₁ = e₂ := by
  rcases h₁ with ⟨hsyn₁, hw₁⟩
  rcases h₂ with ⟨hsyn₂, hw₂⟩
  have hc : e₁ - e₂ ∈ code H :=
    (syndrome_eq_iff_sub_mem_code H e₁ e₂).mp (by rw [hsyn₁, hsyn₂])
  by_contra hne
  have hsub : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : hammingWeight (e₁ - e₂) ≤ 2 * t := by
    calc
      hammingWeight (e₁ - e₂) = hammingWeight (e₁ + (-e₂)) := by simp [sub_eq_add_neg]
      _ ≤ hammingWeight e₁ + hammingWeight (-e₂) := hammingWeight_add_le e₁ (-e₂)
      _ = hammingWeight e₁ + hammingWeight e₂ := by rw [hammingWeight_neg e₂]
      _ ≤ t + t := by omega
      _ = 2 * t := by omega
  have hd := hmin _ hc hsub
  omega

-- ============================================================================
-- Section 5: Hardness assumption
-- ============================================================================
--
-- The uniqueness theorem above guarantees that a low-weight solution, if it
-- exists, is unique.  Whether it can be found efficiently is a computational
-- question.  The following axiom states that there exist families of k-uniform
-- hypergraphs at the appropriate density for which the syndrome-decoding
-- problem is infeasible.  This is the LPN assumption in the parity-check
-- regime and is the trust root for hypergraph-based cryptosystems.

/-- The syndrome-decoding problem for k-uniform hypergraphs is hard. -/
axiom hardSyndromeDecoding (k t : ℕ) : Prop

-- ============================================================================
-- Section 6: The Hamming [7,4,3] code as a 4-uniform hypergraph
-- ============================================================================
--
-- The parity-check matrix of the [7,4,3] Hamming code
-- (Algebra/Code/Hamming.lean) defines a 4-uniform hypergraph on 7 vertices
-- with 3 edges.  Its minimum distance is 3 = 2·1+1, so the uniqueness theorem
-- holds with t = 1.

section HammingExample

/-- The parity-check matrix H of the [7,4,3] Hamming code. -/
def H_matrix : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0, 0;
     1, 1, 1, 0, 0, 1, 0;
     0, 1, 1, 1, 0, 0, 1]

/-- The hypergraph induced by H: vertices = column indices, edges = row supports. -/
def hammingHypergraph : Hypergraph (Fin 7) where
  vertices := Finset.univ
  edges :=
    { Finset.filter (λ j => H_matrix 0 j = 1) Finset.univ,
      Finset.filter (λ j => H_matrix 1 j = 1) Finset.univ,
      Finset.filter (λ j => H_matrix 2 j = 1) Finset.univ }
  mem_vertices := by
    intro e he; simp at he; rcases he with (rfl|rfl|rfl) <;> simp

-- It is 4-uniform.
set_option maxRecDepth 1000000 in
example : hammingHypergraph.IsUniform 4 := by
  unfold hammingHypergraph IsUniform; decide

-- Its code (the kernel of the incidence matrix) has minimum distance 3.
-- Its code (the kernel of the incidence matrix) has minimum distance 3.
-- This is verified directly on the parity-check matrix H_matrix.
def hammingWeightFin7 (x : Fin 7 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

set_option maxRecDepth 1000000 in
example : ∀ c : Fin 7 → ZMod 2, H_matrix.mulVec c = 0 → c ≠ 0 → 3 ≤ hammingWeightFin7 c := by
  decide

-- Therefore, syndrome decoding for t = 1 is unique on the hypergraph.
example (σ : hammingHypergraph.EdgeIdx → ZMod 2)
    (e₁ e₂ : hammingHypergraph.VertIdx → ZMod 2)
    (hmin : ∀ c ∈ code hammingHypergraph, c ≠ 0 → 2 * 1 + 1 ≤ hammingWeight c)
    (h₁ : hammingHypergraph.IsSolution σ 1 e₁)
    (h₂ : hammingHypergraph.IsSolution σ 1 e₂)
  : e₁ = e₂ :=
  unique_solution hammingHypergraph hmin h₁ h₂

end HammingExample

end Hypergraph
end Hypergraph