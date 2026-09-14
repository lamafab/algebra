import Mathlib.Tactic

-- ============================================================================
-- Merkle paths and their verification
-- ============================================================================
--
-- Generic binary hash trees, protocol-agnostic, leaves are committed with a
-- binary hash tree. The compression function h is an arbitrary function here;
-- the binding property (a prover cannot open one leaf two ways) is the
-- random-oracle assumption on h, idealized per repo style. What is proved:
-- honest paths verify.

namespace Merkle

-- TODO: Use a "Hash" type alias for F → F → F, or similar

variable {F : Type*}

/-- A binary tree of field elements; the codeword sits at the leaves. -/
inductive Tree (F : Type*) where
  | leaf : F → Tree F
  | node : Tree F → (Tree F → Tree F)

/-- The Merkle root: hash the two child roots at each internal node. -/
def Tree.root (h : F → F → F) : Tree F → F
  | leaf x => x
  | node l r => h (root h l) (root h r)

/-- Follow directions (true = left) down to a leaf value. -/
def Tree.lookup : Tree F → (List Bool → Option F)
  | leaf x, [] => some x
  | node l _, true :: bs => lookup l bs
  | node _ r, false :: bs => lookup r bs
  | _, _ => none

/-- An authentication path: at each level the sibling's root hash and a flag
for whether the path went left. Ordered from the leaf up to the root. -/
abbrev Path (F : Type*) := List (Bool × F)

/-- Fold a leaf value up along an authentication path to a candidate root. -/
def verify (h : F → F → F) (acc : F) (p : Path F) : F :=
  p.foldl (fun a e => if e.1 then h a e.2 else h e.2 a) acc

/-- The honest path for a direction list, leaf-to-root. -/
def Tree.path (h : F → F → F) : Tree F → List Bool → Option (Path F)
  | leaf _, [] => some []
  | node l r, true :: bs => (Tree.path h l bs).map (· ++ [(true, Tree.root h r)])
  | node l r, false :: bs => (Tree.path h r bs).map (· ++ [(false, Tree.root h l)])
  | _, _ => none

/-- Verifying one appended step matches the fold. -/
theorem verify_append (h : F → F → F) (acc : F) (p : Path F) (b : Bool) (s : F) :
    verify h acc (p ++ [(b, s)]) =
      (if b then h (verify h acc p) s else h s (verify h acc p)) := by
  simp [verify, List.foldl_append]

/-- Honest paths verify: folding the leaf value along its authentication path
lands on the Merkle root. Completeness of the opening; binding is idealized. -/
theorem verify_path (h : F → F → F) :
    ∀ (t : Tree F) (bs : List Bool) (x : F) (p : Path F),
      t.lookup bs = some x → t.path h bs = some p → verify h x p = t.root h := by
  intro t
  induction t with
  | leaf y =>
      intro bs x p hl hp
      cases bs with
      | nil =>
          simp [Tree.lookup] at hl
          subst hl
          simp [Tree.path] at hp
          subst hp
          rfl
      | cons => simp [Tree.lookup] at hl
  | node l r ihl ihr =>
      intro bs x p hl hp
      cases bs with
      | nil => simp [Tree.lookup] at hl
      | cons b bs =>
          cases b
          · -- go right into r; the sibling is l
            simp only [Tree.lookup] at hl
            simp only [Tree.path] at hp
            obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
            rw [verify_append]
            rw [ihr bs x p' hl hp']
            rfl
          · -- go left into l; the sibling is r
            simp only [Tree.lookup] at hl
            simp only [Tree.path] at hp
            obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hp
            rw [verify_append]
            simp only []
            rw [ihl bs x p' hl hp']
            rfl

end Merkle
