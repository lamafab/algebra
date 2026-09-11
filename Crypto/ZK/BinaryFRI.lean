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
--   §1  The additive fold q(x) = x² + β·x: the map, one round on words,
--       the fold chain
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

-- ----------------------------------------------------------------------------
-- §1b: One fold round, on words
-- ----------------------------------------------------------------------------
--
-- The verifier holds words, not polynomials. One round folds a word
-- w : F → F along the fibers of q: on the fiber {x, x + β} over y = q(x)
-- the values w(x), w(x + β) determine the two half-degree components of p
-- at y by a 2×2 solve, and the challenge r combines them into the next
-- layer's value:
--
--   w(x)     = p₀(y) + x·p₁(y)         p₁(y) = (w(x) + w(x+β)) / β
--   w(x + β) = p₀(y) + (x+β)·p₁(y)     p₀(y) = w(x) + x·p₁(y)
--
--   folded value at y := p₀(y) + r·p₁(y)
--
-- The components come from dividing p by q (base-q digits, see
-- exists_fold_decomp below); the word fold itself is field arithmetic only.

open Polynomial

/-- The fold template as a polynomial: q(X) = X² + β·X. Evaluating gives
foldMap; dividing by it produces the two components of a fold round. -/
noncomputable def foldQ (β : F) : Polynomial F := X ^ 2 + C β * X

omit [CharP F 2] in
theorem foldQ_eval (β x : F) : (foldQ β).eval x = foldMap β x := by
  simp [foldQ, foldMap]

omit [CharP F 2] in
theorem foldQ_monic (β : F) : (foldQ β).Monic := by
  unfold foldQ
  apply monic_X_pow_add
  compute_degree!

omit [CharP F 2] in
theorem foldQ_natDegree (β : F) : (foldQ β).natDegree = 2 := by
  unfold foldQ
  compute_degree!

omit [CharP F 2] in
/-- A polynomial of natDegree < 2 is a single digit a·X + b. -/
theorem eq_digit_of_natDegree_lt_two {p : Polynomial F} (h : p.natDegree < 2) :
    p = C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 2 by omega)]
    simp

omit [CharP F 2] in
/-- Base-q decomposition: f = p₀(q(X)) + X·p₁(q(X)) with halved degrees.
Existence is polynomial long division in base q, one digit at a time; the
digits' constant parts collect into p₀, the X-parts into p₁. This is the
generalization of the even/odd split along X² (parity of exponents) to the
fold polynomial q. Uniqueness (used by the soundness argument, not by the
honest prover) is not formalized here. -/
theorem exists_fold_decomp (β : F) (f : Polynomial F) :
    ∃ p₀ p₁ : Polynomial F,
      f = p₀.comp (foldQ β) + X * p₁.comp (foldQ β) ∧
      2 * p₀.natDegree ≤ f.natDegree ∧ 2 * p₁.natDegree ≤ f.natDegree := by
  induction' h : f.natDegree using Nat.strong_induction_on with n ih generalizing f
  by_cases hdeg : f.natDegree < 2
  · rw [eq_digit_of_natDegree_lt_two hdeg]
    refine ⟨C (f.coeff 0), C (f.coeff 1), ?_, by rw [natDegree_C]; omega,
      by rw [natDegree_C]; omega⟩
    rw [C_comp, C_comp]; ring
  · push Not at hdeg
    have hq := foldQ_monic β
    have hq2 : (foldQ β).natDegree = 2 := foldQ_natDegree β
    have hq1 : foldQ β ≠ 1 := by
      intro h1; rw [h1, natDegree_one] at hq2; omega
    set f' := f /ₘ foldQ β with hf'
    set d := f %ₘ foldQ β with hd
    have hdd : d.natDegree < 2 := by rw [hd, ← hq2]; exact natDegree_modByMonic_lt f hq hq1
    have hfdecomp : d + foldQ β * f' = f := by rw [hd, hf']; exact modByMonic_add_div _ _
    have hdf' : f'.natDegree = n - 2 := by rw [hf', natDegree_divByMonic f hq, h, hq2]
    have hlt : f'.natDegree < n := by omega
    obtain ⟨p₀', p₁', hcomp, hd0, hd1⟩ := ih _ hlt f' rfl
    rw [eq_digit_of_natDegree_lt_two hdd] at hfdecomp
    refine ⟨p₀' * X + C (d.coeff 0), p₁' * X + C (d.coeff 1), ?_, ?_, ?_⟩
    · have e1 : (p₀' * X + C (d.coeff 0)).comp (foldQ β) =
          p₀'.comp (foldQ β) * foldQ β + C (d.coeff 0) := by
        simp [add_comp, mul_comp, X_comp, C_comp]
      have e2 : (p₁' * X + C (d.coeff 1)).comp (foldQ β) =
          p₁'.comp (foldQ β) * foldQ β + C (d.coeff 1) := by
        simp [add_comp, mul_comp, X_comp, C_comp]
      rw [e1, e2]
      linear_combination foldQ β * hcomp - hfdecomp
    · have h0 : (p₀' * X + C (d.coeff 0)).natDegree ≤ p₀'.natDegree + 1 := by
        by_cases hp : p₀' = 0
        · subst hp; rw [zero_mul, zero_add, natDegree_C]; omega
        · exact (natDegree_add_le _ _).trans (by rw [natDegree_mul_X hp, natDegree_C]; omega)
      omega
    · have h1 : (p₁' * X + C (d.coeff 1)).natDegree ≤ p₁'.natDegree + 1 := by
        by_cases hp : p₁' = 0
        · subst hp; rw [zero_mul, zero_add, natDegree_C]; omega
        · exact (natDegree_add_le _ _).trans (by rw [natDegree_mul_X hp, natDegree_C]; omega)
      omega

/-- The folded word's value at y = q(x), computed from the fiber {x, x+β}
of the current word w. This is p₀(y) + r·p₁(y) with the components read
off the 2×2 solve above; field arithmetic only. -/
def foldWord (β r : F) (w : F → F) (x : F) : F :=
  w x + (x + r) * (w x + w (x + β)) / β

/-- The folded value is the same from either representative of a fiber, so
foldWord defines a word on the halved image domain q(L). -/
theorem foldWord_pair (β r : F) (hβ : β ≠ 0) (w : F → F) (x : F) :
    foldWord β r w (x + β) = foldWord β r w x := by
  have hfib : x + β + β = x := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hs : β * ((w x + w (x + β)) / β) = w x + w (x + β) :=
    mul_div_cancel₀ _ hβ
  unfold foldWord
  rw [hfib, add_comm (w (x + β)) (w x)]
  linear_combination hs + CharTwo.add_self_eq_zero (w (x + β))

/-- Fold consistency: if w is the evaluation table of f and f decomposes
along q as (p₀, p₁) — always possible, by exists_fold_decomp — then the
folded word at x is the folded polynomial p₀ + r·p₁ evaluated at q(x).
The verifier's per-round check is this equality at random points. -/
theorem foldWord_eval (β r : F) (hβ : β ≠ 0) (f p₀ p₁ : Polynomial F)
    (hcomp : f = p₀.comp (foldQ β) + X * p₁.comp (foldQ β))
    (w : F → F) (hw : ∀ x, w x = f.eval x) (x : F) :
    foldWord β r w x = (p₀ + C r * p₁).eval (foldMap β x) := by
  have e1 : w x = p₀.eval (foldMap β x) + x * p₁.eval (foldMap β x) := by
    rw [hw x, hcomp, eval_add, eval_mul, eval_X, eval_comp, eval_comp, foldQ_eval]
  have e2 : w (x + β) = p₀.eval (foldMap β x) + (x + β) * p₁.eval (foldMap β x) := by
    rw [hw (x + β), hcomp, eval_add, eval_mul, eval_X, eval_comp, eval_comp,
      foldQ_eval, foldMap_pair]
  set a := p₀.eval (foldMap β x) with ha
  set b := p₁.eval (foldMap β x) with hb
  have hsum : w x + w (x + β) = β * b := by
    rw [e1, e2]
    linear_combination CharTwo.add_self_eq_zero a + CharTwo.add_self_eq_zero (x * b)
  unfold foldWord
  rw [hsum, e1, eval_add, eval_mul, eval_C, mul_div_assoc, mul_div_cancel_left₀ _ hβ]
  linear_combination CharTwo.add_self_eq_zero (x * b)

-- ----------------------------------------------------------------------------
-- §1c: The fold chain
-- ----------------------------------------------------------------------------
--
-- The loop from the header, as a consistency predicate. word 0 is the
-- committed RS codeword; in round i the prover commits word (i+1), the
-- verifier samples r i, and `step` is the spot-check repeated at random
-- points in the query phase (§4): the sibling values of round i determine
-- the parent value of round i+1. The last word's domain is a single point,
-- so the verifier reads the final constant directly.
--
-- Not tracked in the type: the domains (word i is only meaningful on its
-- image subspace of size 2^(m−i)) and the distance and soundness claims
-- (those live in §2 and §4).

/-- A fold chain of length m: words linked round by round by the fold. -/
structure FoldChain (F : Type*) [Field F] [CharP F 2] (m : ℕ) where
  word : ℕ → F → F
  β : ℕ → F
  r : ℕ → F
  β_ne_zero : ∀ i, β i ≠ 0
  step : ∀ i, i < m → ∀ x, word (i + 1) (foldMap (β i) x) = foldWord (β i) (r i) (word i) x

-- Sanity over 𝔽₂: q(x) = x² + x has kernel {0, 1}, the whole two-point
-- domain, so one round folds any word to a constant.
example : foldMap (1 : ZMod 2) 0 = 0 ∧ foldMap (1 : ZMod 2) 1 = 0 := by decide

-- The word w = [0, 1] (the evaluation table of X) folds with β = 1 and
-- challenge r₀ = 1 to the constant 1: X = 0·q + X·1, so p₀ = 0, p₁ = 1
-- and the folded value is 0 + 1·1. Both fiber representatives agree.
example : foldWord (1 : ZMod 2) 1 (fun x => x) 0 = 1 := by decide
example : foldWord (1 : ZMod 2) 1 (fun x => x) 1 = 1 := by decide

-- A one-round chain: word 0 = [0, 1] folds to the constant word [1].
example : Nonempty (FoldChain (F := ZMod 2) 1) :=
  ⟨{  word := fun i => if i = 0 then (fun x : ZMod 2 => x) else fun _ => 1
      β := fun _ => 1
      r := fun _ => 1
      β_ne_zero := fun _ => one_ne_zero
      step := by
        intro i hi x
        interval_cases i
        fin_cases x <;> decide }⟩

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

-- ============================================================================
-- Section 4: The query phase, concretely on a toy tree
-- ============================================================================
--
-- After the folding rounds the verifier queries at random points: it asks for
-- a leaf value plus its authentication path, and checks (a) the path verifies
-- against the committed root, and (b) the value is consistent with the fold
-- chain (FoldChain.step, §1c), i.e. the two sibling values of one round
-- determine the parent value of the next. Soundness: if the committed word is
-- far from every codeword,
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
