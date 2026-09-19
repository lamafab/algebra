import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Algebra.Code.ReedSolomonReedMuller

-- ============================================================================
-- Binary FRI: proximity testing by additive folding
-- ============================================================================
--
-- FRI (Fast Reed-Solomon interactive oracle proof of proximity) convinces a
-- verifier that a committed word is close to a Reed-Solomon codeword, by
-- repeatedly folding the polynomial to half its degree until only a constant
-- remains. The prover computes and commits each folded word; the verifier
-- only samples the challenges and spot-checks fold consistency at random
-- points.
--
-- Prime-field FRI folds along the squaring map x ↦ x² on a multiplicative
-- subgroup; squaring is 2-to-1 there, the odd-characteristic half of the
-- dichotomy (Characteristic.lean §4). Binary fields cannot do that: GF(2ᵏ)ˣ
-- has odd order, so there are no 2-power roots of unity to halve around
-- (BinaryFields.lean §3), and squaring is injective rather than 2-to-1 in
-- characteristic 2 (BinaryFields.lean §4b, Characteristic.lean §4).
--
-- Binary FRI folds along the additive map q(x) = x² + β·x instead. In
-- characteristic 2 this map is 𝔽₂-linear, its kernel is {0, β}, and it
-- sends each pair {x, x + β} to a single value. Applied to an 𝔽₂-subspace
-- domain of size 2ᵐ, it collapses the domain to size 2^{m−1}: one round of
-- folding. Iterating with fresh β's halves the domain each round until one
-- point is left.
--
--   §1  The additive fold q(x) = x² + β·x: the map, one round on words,
--       the fold chain
--   §2  The Reed-Solomon properties behind the proximity question
--
-- Prerequisites: Characteristic.lean (the squaring dichotomy §4, the
-- freshman's dream §3), BinaryFields.lean (§3 no 2-power roots of unity,
-- §4b squaring cannot fold), ReedSolomonReedMuller.lean (the RS code).
-- Examples/BinaryFRI.lean has a worked end-to-end run over GF(8).
--
-- EvalOpening.lean turns the proximity test into an evaluation opening
-- of a claim p(r) = v (the quotient trick) in combination with Sumcheck.lean.

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
Remember that β = -β when the characteristic is 2 (Characteristic.lean §2) -/
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

-- TODO: Expand on how a high-degree polynomial does not survive the fold
-- (via coefficient canceling).
--
-- ----------------------------------------------------------------------------
-- §1b: One fold round, on words
-- ----------------------------------------------------------------------------
--
-- The verifier holds words, not polynomials. One round folds a word
-- w : F → F along the fibers of q. Write the polynomial behind w in
-- base q (exists_fold_decomp below):
--
--   f(X) = p₀(q(X)) + X·p₁(q(X))     with 2·deg pᵢ ≤ deg f
--
-- On the fiber {x, x + β} over y = q(x) = q(x + β) (foldMap_pair above),
-- evaluating at the two fiber points gives two equations in the two
-- unknowns p₀(y), p₁(y):
--
--   w(x)     = p₀(y) + x·p₁(y)
--   w(x + β) = p₀(y) + (x+β)·p₁(y)
--
-- Solving recovers the unknowns per fiber, by adding the equations:
--
--   w(x) + w(x + β) = (p₀(y) + x·p₁(y)) + (p₀(y) + (x+β)·p₁(y))
--                   = (1 + 1)·p₀(y) + (x + (x + β))·p₁(y)
--
-- The p₀ coefficient is 1 + 1 = 0 and the p₁ coefficient is
-- x + (x + β) = β, leaving β·p₁(y) = w(x) + w(x + β). Dividing through
-- and back-substituting (minus is plus in char 2):
--
--   p₁(y) = (w(x) + w(x+β)) / β     p₀(y) = w(x) + x·p₁(y)
--
-- The division by β is why β ≠ 0 is assumed throughout (FoldChain.β_ne_zero):
-- β = 0 collapses the fiber to one point and the two equations coincide.
--
-- The challenge c combines the components into the next layer's value,
-- the half-degree folded polynomial p₀ + c·p₁ evaluated at y:
--
--   folded value at y := p₀(y) + c·p₁(y)
--
-- The word fold itself is field arithmetic only (foldWord); the 2×2
-- solve is the fiber-local reading of the global division by foldQ.

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

-- TODO: Uniqueness *should* be formalized, or at least explicitly stated
-- via a proxy `sorry` theorem.
omit [CharP F 2] in
/-- Base-q decomposition: f = p₀(q(X)) + X·p₁(q(X)) with halved degrees.
Existence is polynomial long division in base q, one digit at a time; the
digits' constant parts collect into p₀, the X-parts into p₁. This is the
generalization of the even/odd split along X² (parity of exponents) to the
fold polynomial q. Uniqueness (used by the soundness argument, not by the
honest prover) is not formalized here. -/
theorem exists_fold_decomp (β : F) (f : Polynomial F) :
    ∃ p₀ p₁ : Polynomial F,
      -- f(X) = p₀(q(X)) + X·p₁(q(X))
      f = p₀.comp (foldQ β) + X * p₁.comp (foldQ β) ∧
      2 * p₀.natDegree ≤ f.natDegree ∧
      2 * p₁.natDegree ≤ f.natDegree := by
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
of the current word w. This is p₀(y) + c·p₁(y) with the components read
off the 2×2 solve above (§1b) -/
def foldWord (β c : F) (w : F → F) (x : F) : F :=
  w x + (x + c) * (w x + w (x + β)) / β

/-- The folded value is the same from either representative of a fiber, so
foldWord defines a word on the halved image domain q(L). -/
theorem foldWord_pair (β c : F) (hβ : β ≠ 0) (w : F → F) (x : F) :
    foldWord β c w (x + β) = foldWord β c w x := by
  have hfib : x + β + β = x := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hs : β * ((w x + w (x + β)) / β) = w x + w (x + β) :=
    mul_div_cancel₀ _ hβ
  unfold foldWord
  rw [hfib, add_comm (w (x + β)) (w x)]
  linear_combination hs + CharTwo.add_self_eq_zero (w (x + β))

/-- Fold consistency: if w is the evaluation table of f and f decomposes
along q as (p₀, p₁), which is always possible (exists_fold_decomp), then the
folded word at x is the folded polynomial p₀ + c·p₁ evaluated at q(x).
The verifier's per-round check is this equality at random points. -/
theorem foldWord_eval
    (β c : F)
    (hβ : β ≠ 0)
    (f p₀ p₁ : Polynomial F)
    (hcomp : f = p₀.comp (foldQ β) + X * p₁.comp (foldQ β))
    (w : F → F)
    (hw : ∀ x, w x = f.eval x)
    (x : F)
  :
    foldWord β c w x = (p₀ + C c * p₁).eval (foldMap β x) := by
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
-- verifier samples c i, and `step` is the spot-check repeated at random
-- points in the query phase: the sibling values of round i determine the
-- parent value of round i+1. The last word's domain is a single point,
-- so the verifier reads the final constant directly.
--
-- Not tracked in the type: the domains (word i is only meaningful on its
-- image subspace of size 2^(m−i)) and the distance and soundness claims
-- (those live in §2).

/-- A fold chain of length m: words linked round by round by the fold. -/
structure FoldChain (F : Type*) [Field F] [CharP F 2] (m : ℕ) where
  word : ℕ → F → F
  β : ℕ → F
  c : ℕ → F
  β_ne_zero : ∀ i, β i ≠ 0
  step : ∀ i, i < m → ∀ x, word (i + 1) (foldMap (β i) x) = foldWord (β i) (c i) (word i) x

-- Sanity over 𝔽₂: q(x) = x² + x has kernel {0, 1}, the whole two-point
-- domain, so one round folds any word to a constant.
example : foldMap (1 : ZMod 2) 0 = 0 ∧ foldMap (1 : ZMod 2) 1 = 0 := by decide

-- The word w = [0, 1], the evaluation table of X on the two-point domain
-- 𝔽₂ (its RS codeword), folds with β = 1 and challenge c₀ = 1 to the
-- constant 1: X = 0·q + X·1, so p₀ = 0, p₁ = 1 and the folded value is
-- 0 + 1·1. Both fiber representatives agree.
example : foldWord (1 : ZMod 2) 1 (fun x => x) 0 = 1 := by decide
example : foldWord (1 : ZMod 2) 1 (fun x => x) 1 = 1 := by decide

-- A one-round chain: word 0 = [0, 1] folds to the constant word [1].
example : Nonempty (FoldChain (F := ZMod 2) 1) :=
  ⟨{  word := fun i => if i = 0 then (fun x : ZMod 2 => x) else fun _ => 1
      β := fun _ => 1
      c := fun _ => 1
      β_ne_zero := fun _ => one_ne_zero
      step := by
        intro i hi x
        interval_cases i
        fin_cases x <;> decide }⟩

end AdditiveFold

-- ============================================================================
-- Section 2: The Reed-Solomon properties behind the proximity question
-- ============================================================================
--
-- TODO: Rework this section; might be better to demonstrate this using
-- a commitment layer like Merkle.lean, or in the context of the larger
-- Binius mechanism.
--
-- The verifier's question, "is the committed word close to some codeword?",
-- only has content because of two properties of the RS code RS[L, d]
-- (ReedSolomonReedMuller.lean §1, where they are proved and demonstrated
-- with a computed GF(8) example):
--
--   rsEncode_injective : a codeword comes from exactly one polynomial of
--     degree < d, so a word near the code pins down the message.
--   rs_min_distance    : distinct codewords differ in at least |L| − d + 1
--     positions, so a word can be close to at most one codeword.
--
-- What the verifier checks. It never sees the polynomial and never
-- measures a degree directly. The prover commits each folded word (the
-- commitment layer lives outside this file), the verifier samples the
-- challenge cᵢ, and after m rounds it queries: pick a random point of
-- the initial domain, open the two fiber values of each round along its
-- fold path, and check FoldChain.step at every link. The last word has
-- a one-point domain and is read outright. A chain that passes is
-- accepted as "word 0 is close to a degree < 2ᵐ codeword": the degree
-- is certified by the m halvings ending in a constant, not by
-- interpolating anything. The evaluation claim p(r) = v itself, at a
-- point r almost surely outside the committed domain, is discharged by
-- the quotient opening (EvalOpening.lean).
--
-- Why the constraints hold up during the fold. Completeness: folding
-- preserves the code. If word i is the table of f with deg f < 2^{m−i},
-- the folded polynomial p₀ + cᵢ·p₁ has degree < 2^{m−i−1} (the degree
-- bounds of exists_fold_decomp) and word (i+1) is its table on the
-- halved domain (foldWord_eval): every honest word is again an RS
-- codeword of the same rate, so every check passes. Soundness (not
-- formalized here): folding also preserves distance with high
-- probability over the challenges, so a word 0 far from every codeword
-- has some round inheriting that distance, and a random query catches
-- the inconsistency there.
--
-- How many samples. One query catches a word at distance δ with
-- probability ≈ δ, so s independent queries drop the soundness error
-- to ≈ (1 − δ)ˢ; s ≈ λ/δ gives 2⁻λ. The distance bound is what the
-- prover cannot fake: far from the code, no fold chain stays
-- consistent all the way down to the constant.

#check @rsEncode
#check @rsEncode_injective
#check @rs_min_distance

end BinaryFRI
