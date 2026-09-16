import Mathlib.Tactic
import Algebra.Field.G8

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

-- ============================================================================
-- Workshop: a concrete tree over GF(8), and why the hash must be nonlinear
-- ============================================================================
--
-- The machinery above is field-agnostic; here it is exercised over G8
-- (Algebra/Field/G8.lean), committed leaves being the codeword of
-- Examples/BinaryFRI.lean. The compression function is h(a, b) = a² + b² + b;
-- the simpler a² + b³ would be vacuous on GF(8), because cubing is a
-- bijection there (gcd(3, 7) = 1), which makes every b-fiber surjective
-- and every edit compensatable, exactly like the toy a + b of
-- BiniusToy.lean. With b² + b the b-fiber lands in a coset of the
-- 4-element subspace {t² + t}, so half the values are unreachable:
-- binding is a real property of this hash, demonstrated below.

open G8 -- activates the α, α² notations

/-- The compression function: h(a, b) = a² + b² + b. -/
def hash1 (a b : G8) : G8 := a * a + b * b + b

/-- The committed word, leaves [1, 1, 0, α²+α, 0, α, 0, α²]. -/
def codewordTree : Tree G8 :=
  .node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf (α² + α))))
        (.node (.node (.leaf 0) (.leaf α)) (.node (.leaf 0) (.leaf α²)))

-- The root is α⁵ = α²+α+1: level 1 gives h(1,1) = 1, h(0,α⁴) = α²,
-- h(0,α) = α⁴, h(0,α²) = α; level 2 gives h(1,α²) = α³, h(α⁴,α) = α²;
-- the root is h(α³, α²) = α⁶ + α⁴ + α² = α⁵.
example : codewordTree.root hash1 = α² + α + 1 := by decide

-- The honest path to the α-leaf (directions [false, true, false]),
-- computed by Tree.path rather than written out by hand, verifies against
-- the root, both by decide and by the general honest-path theorem.
example : Tree.path hash1 codewordTree [false, true, false] =
    some [(false, 0), (true, α), (false, α + 1)] := by decide

example : codewordTree.lookup [false, true, false] = some α ∧
    verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
      codewordTree.root hash1 :=
  ⟨by decide, by decide⟩

example : verify hash1 α [(false, 0), (true, α), (false, α + 1)] =
    codewordTree.root hash1 :=
  verify_path hash1 codewordTree [false, true, false] α
    [(false, 0), (true, α), (false, α + 1)] (by decide) (by decide)

-- Tampering is detected: flipping the first leaf 1 ↦ 0 changes the root.
def tamperedTree : Tree G8 :=
  .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf (α² + α))))
        (.node (.node (.leaf 0) (.leaf α)) (.node (.leaf 0) (.leaf α²)))

example : tamperedTree.root hash1 ≠ codewordTree.root hash1 := by decide

-- Why the hash matters. With h₀(a, b) = a + b (the BiniusToy toy), EVERY
-- single-leaf edit x ↦ x' can be hidden by editing the sibling to
-- y' = y + x + x': the parent hash is unchanged, so the root survives and
-- the tree is not binding at all.
example : ∀ x x' y : G8, ∃ y' : G8, x' + y' = x + y :=
  fun x x' y => ⟨y + x + x', by revert x x' y; decide⟩

-- With hash1, compensation can fail: after the edit 0 ↦ 1 at the leaf
-- whose sibling value is 0, no sibling value y' restores the parent hash,
-- because hash1(1, ·) only ever outputs 1, α³, α⁵ or α⁶, never 0.
example : ∃ x x' y : G8, ∀ y' : G8, hash1 x' y' ≠ hash1 x y :=
  ⟨0, 1, 0, by decide⟩

end Merkle
