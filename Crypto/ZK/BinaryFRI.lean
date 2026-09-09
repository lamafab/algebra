import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Algebra.Code.ReedSolomonReedMuller

-- ============================================================================
-- Binary FRI: proximity testing by additive folding
-- ============================================================================
--
-- FRI (Fast Reed-Solomon Interactive oracle proof of proximity) convinces a
-- verifier that a committed word is close to a Reed-Solomon codeword, by
-- repeatedly folding the polynomial to half its degree until only a constant
-- remains. Prime-field FRI folds along the squaring map x ↦ x² on a
-- multiplicative subgroup; squaring is 2-to-1 there, the odd-characteristic
-- half of the dichotomy (Characteristic.lean §4). Binary fields cannot do
-- that: GF(2ᵏ)ˣ has odd order, so there are no 2-power roots of unity to
-- halve around (BinaryFields.lean §3), and squaring is injective rather than
-- 2-to-1 in characteristic 2 (BinaryFields.lean §4b, Characteristic.lean §4).
--
-- Binary FRI folds along the additive map q(x) = x² + β·x instead. In
-- characteristic 2 this map is 𝔽₂-linear, its kernel is {0, β}, and it
-- sends each pair {x, x + β} to a single value. Applied to an 𝔽₂-subspace
-- domain of size 2ᵐ, it collapses the domain to size 2^{m−1}: one round of
-- folding.
--
-- Iterating with fresh β's halves the domain each round until one point is
-- left.
--
--   §1  The additive fold q(x) = x² + β·x
--   §2  Committing: RS-encode the MLE table, Merkle-hash the leaves
--   §3  Merkle paths and their verification
--   §4  The query phase and the soundness sketch
--
-- Prerequisites: Characteristic.lean (the squaring dichotomy §4, the
-- freshman's dream §3), BinaryFields.lean (§3 no 2-power roots of unity,
-- §4b squaring cannot fold), ReedSolomonReedMuller.lean (the RS code),
-- Multilinear.lean (the MLE table being committed to).

namespace BinaryFRI

-- ============================================================================
-- Section 1: The additive fold
-- ============================================================================

section AdditiveFold

variable {F : Type*} [Field F] [CharP F 2]

/-- The additive fold map q(x) = x² + β·x. Degree 2, but 𝔽₂-linear. -/
def foldMap (β x : F) : F := x ^ 2 + β * x

omit [CharP F 2] in
/-- The two readings of q: expanded for linearity, factored for the roots.
The factored form shows the kernel directly (foldMap_eq_zero_iff). -/
theorem foldMap_eq_mul_add (β x : F) : foldMap β x = x * (x + β) := by
  rw [foldMap]; ring

/-- q is additive: q(x + y) = q(x) + q(y). The square is linear in
characteristic 2 by Freshman's dream (Characteristic.lean §3,
BinaryFields.lean §4). -/
theorem foldMap_add (β x y : F) : foldMap β (x + y) = foldMap β x + foldMap β y := by
  rw [foldMap, foldMap, foldMap, add_pow_char (R := F) (x := x) (y := y) (p := 2)]
  ring

/-- The kernel of q is {0, β}: q(x) = x·(x+β) vanishes exactly at 0 and β.
Remember that -β = β when the characteristic is 2 (Characteristic.lean §2) -/
theorem foldMap_eq_zero_iff (β x : F) :
    foldMap β x = 0 ↔ x = 0 ∨ x = β := by
  rw [foldMap_eq_mul_add, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · have h' : x = -β := eq_neg_of_add_eq_zero_left h
      rw [h', CharTwo.neg_eq]
      exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (h ▸ CharTwo.add_self_eq_zero x)

/-- The 2-to-1 collapse at the heart of binary FRI: q(x + β) = q(x). Each
fold round pairs up the domain {x, x+β} and halves its size. Unlike the
squaring pair {x, −x}, which collapses in characteristic 2 (Characteristic.lean
§4, BinaryFields.lean §4b), this pair is always distinct when β ≠ 0, so the
fold really is 2-to-1.

Worked example over GF(4) = {0, 1, ω, ω+1} with ω² = ω+1, taking β = ω:

  x        x²        ω·x         q(x) = x² + ω·x
  ─────────────────────────────────────────────
  0        0         0           0
  1        1         ω           1 + ω
  ω        ω+1       ω² = ω+1    (ω+1)+(ω+1) = 0
  ω+1      ω         ω(ω+1) = 1  ω + 1

Four inputs, two outputs; the two inputs in each fiber differ by exactly ω:

  0   ──┐
        ├──→  0
  ω   ──┘        (0 + ω = ω)

  1   ──┐
        ├──→  1 + ω
  ω+1 ──┘        (1 + ω = ω+1)

Adding ω flips each element to its partner; adding ω again flips back,
since ω + ω = 0. -/
theorem foldMap_pair (β x : F) : foldMap β (x + β) = foldMap β x := by
  rw [foldMap, foldMap, add_pow_char (R := F) (x := x) (y := β) (p := 2)]
  have hββ : β ^ 2 + β * β = 0 := by
    have h : β ^ 2 = β * β := by ring
    rw [h]
    exact CharTwo.add_self_eq_zero _
  linear_combination hββ

end AdditiveFold

-- ============================================================================
-- Section 2: Committing to the MLE table
-- ============================================================================
--
-- The prover's message is one field element: the Merkle root of a Reed-Solomon
-- codeword. The codeword is built in two steps:
--
--   1. The MLE table (Multilinear.lean) assigns a field element to each
--      point of the hypercube 𝔽₂ᵐ. Viewed on an 𝔽₂-subspace of size 2ᵐ
--      inside GF(2ᵏ), that table is the evaluation table of a unique
--      univariate polynomial p of degree < 2ᵐ (RootsInterpolation.lean).
--      Interpolating the table recovers p.
--   2. Stretch: evaluate p on a larger domain L containing that subspace
--      (ReedSolomonReedMuller.lean §1). The stretched table is the RS
--      codeword that gets Merkle-hashed in §3.
--
-- The stretching is what buys distance. Two different polynomials of degree
-- < 2ᵐ agree on at most 2ᵐ − 1 points, so their codewords differ in at
-- least |L| − 2ᵐ + 1 positions. FRI's proximity question, "is the committed
-- word close to some codeword?", only has content because codewords are
-- this far apart: a word near the code is near exactly one codeword, so
-- the polynomial it came from is pinned down.
--
--   `rsEncode L p`       : the codeword, evaluations of p on L
--   `rsEncode_injective` : the codeword determines the polynomial
--     (the roots bound from RootsInterpolation.lean, applied to p − q)
--   `rs_min_distance`    : distinct codewords differ in at least
--     |L| − d + 1 positions

#check @rsEncode
#check @rsEncode_injective
#check @rs_min_distance

-- Encoding over GF(4), concretely: p(X) = X + 1 becomes the pointwise map
-- α ↦ α + 1 on any domain (the full walkthrough, with the four-entry
-- codeword table, is ReedSolomonReedMuller.lean §1).
example (L : Finset (GaloisField 2 2)) :
    rsEncode L (Polynomial.C (1 : GaloisField 2 2) * Polynomial.X + Polynomial.C 1) =
      fun α : L => (α : GaloisField 2 2) + 1 := by
  funext α
  show (Polynomial.C (1 : GaloisField 2 2) * Polynomial.X + Polynomial.C 1).eval
      (α : GaloisField 2 2) = (α : GaloisField 2 2) + 1
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  simp

-- Distinct polynomials give codewords that disagree: X + 1 and X already
-- differ at α = 0, and by rs_min_distance they differ almost everywhere.
example :
    (Polynomial.C (1 : GaloisField 2 2) * Polynomial.X + Polynomial.C 1).eval
      (0 : GaloisField 2 2) ≠ Polynomial.X.eval (0 : GaloisField 2 2) := by
  simp

-- ============================================================================
-- Section 3: Merkle paths
-- ============================================================================
--
-- The codeword leaves are committed with a binary hash tree. The compression
-- function h is an arbitrary function here; the binding property (a prover
-- cannot open one leaf two ways) is the random-oracle assumption on h,
-- idealized per repo style. What is proved: honest paths verify.

section Merkle

variable {F : Type*}

/-- A binary tree of field elements; the codeword sits at the leaves. -/
inductive Tree (F : Type*) where
  | leaf : F → Tree F
  | node : Tree F → Tree F → Tree F

/-- The Merkle root: hash the two child roots at each internal node. -/
def Tree.root (h : F → F → F) : Tree F → F
  | leaf x => x
  | node l r => h (root h l) (root h r)

/-- Follow directions (true = left) down to a leaf value. -/
def Tree.lookup : Tree F → List Bool → Option F
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

-- ============================================================================
-- Section 4: The query phase, concretely on a toy tree
-- ============================================================================
--
-- After the folding rounds the verifier queries at random points: it asks for
-- a leaf value plus its authentication path, and checks (a) the path verifies
-- against the committed root, and (b) the value is consistent with the fold
-- chain, i.e. the two sibling values of one round determine the parent value
-- of the next. Soundness: if the committed word is far from every codeword,
-- some fold round inherits that distance, and a random query catches an
-- inconsistency with constant probability per query.
--
-- Toy arithmetic sanity checks over 𝔽₂ with h = addition (not binding, just
-- to exercise the definitions).

-- The truth table of AND, committed as four leaves.
example :
    let t : Tree (ZMod 2) := .node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))
    t.lookup [false, false] = some 1 := by decide

-- The honest path to the (1,1)-leaf verifies against the root.
example :
    let h : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => a + b
    let t : Tree (ZMod 2) := .node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))
    verify h 1 [(false, 0), (false, 0)] = t.root h := by decide

-- The same check via the verified-path theorem.
example (h : ZMod 2 → ZMod 2 → ZMod 2)
    (t : Tree (ZMod 2)) (bs : List Bool) (x : ZMod 2) (p : Path (ZMod 2))
    (hl : t.lookup bs = some x) (hp : t.path h bs = some p) :
    verify h x p = t.root h :=
  verify_path h t bs x p hl hp

end BinaryFRI
