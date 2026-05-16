import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

-- ============================================================================
-- Quotient Rings
-- ============================================================================
--
-- Ideals.lean built the THEORY (R/I, maximal → field, prime → domain).
-- This file builds the CONSTRUCTION — using R ⧸ I in Lean to make the
-- abstract examples concrete:
--
--   ℤ / (5)           = 𝔽₅     (modular arithmetic)
--   𝔽₃[X] / (X² + 1)  = GF(9)  (a 9-element field)
--   ℝ[X] / (X² + 1)   ≅ ℂ      (the complex numbers)
--
-- Mathlib's API:
--   R ⧸ I                 the quotient ring (\quot for ⧸)
--   Ideal.Quotient.mk I   projection R → R ⧸ I,  a ↦ [a]
--   Ideal.Quotient.eq     [a] = [b] ⟺ a - b ∈ I

private abbrev I5 : Ideal ℤ := Ideal.span {(5 : ℤ)}
private abbrev π5 : ℤ →+* (ℤ ⧸ I5) := Ideal.Quotient.mk _

-- ============================================================================
-- Section 1: The basic API
-- ============================================================================

example : Type := ℤ ⧸ I5
example (a b : ℤ) : Ideal.Quotient.mk (I5) a = Ideal.Quotient.mk (I5) b ↔ a - b ∈ I5 :=
    Ideal.Quotient.eq

-- ============================================================================
-- Section 2: ℤ/(5) — modular arithmetic in Lean
-- ============================================================================
--
-- ℤ/(5) has 5 cosets {[0], [1], [2], [3], [4]}, and (5) is maximal so it's
-- a field (Ideals.lean §7).

-- Reduction: integers wrap mod 5
example : π5 7 = π5 2 := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨1, by ring⟩

example : π5 12 = π5 2 := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨2, by ring⟩

example : π5 (-3) = π5 2 := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-1, by ring⟩

-- Arithmetic: + and · respect the projection
example : π5 2 + π5 3 = π5 0 := by
  rw [← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton];
  exact ⟨1, by ring⟩

example : π5 2 * π5 3 = π5 1 := by
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨1, by ring⟩

example : π5 4 * π5 4 = π5 1 := by
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨3, by ring⟩

-- Inverses (read off the multiplications above):
--   [1]⁻¹ = [1],  [2]⁻¹ = [3],  [3]⁻¹ = [2],  [4]⁻¹ = [4]

-- Mathlib's `ZMod 5` is the same field, built differently:
example : (ℤ ⧸ I5) ≃+* ZMod 5 := Int.quotientSpanNatEquivZMod 5

-- ============================================================================
-- Section 3: When the quotient ISN'T a field
-- ============================================================================
--
-- (6) ⊆ ℤ is not maximal — and not even prime as an ideal: 2 · 3 = 6 ∈ (6)
-- but neither 2 nor 3 is. So ℤ/(6) is just a ring, with zero divisors:

private abbrev I6 : Ideal ℤ := Ideal.span {(6 : ℤ)}
private abbrev π6 : ℤ →+* (ℤ ⧸ I6) := Ideal.Quotient.mk _

-- [2] · [3] = [6] = [0]   yet [2] and [3] are nonzero
example : π6 2 * π6 3 = π6 0 := by
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨1, by ring⟩

example : π6 2 ≠ π6 0 := by
  rw [Ne, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  decide

example : π6 3 ≠ π6 0 := by
  rw [Ne, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  decide

--   ℤ/(5)   prime → maximal → field  (no zero divisors)
--   ℤ/(6)   composite → just a ring  (zero divisors, no cancellation)
--
-- Polynomial analog: ℝ[X]/(X² - 1) has [X-1] · [X+1] = [0] via the
-- factorization X² - 1 = (X-1)(X+1). Same moral.

-- ============================================================================
-- Section 4: Polynomial quotients — building GF(9)
-- ============================================================================
--
-- Same recipe in 𝔽₃[X]: an irreducible polynomial generates a maximal
-- ideal whose quotient is a field. "Prime" in ℤ and "irreducible" in 𝔽₃[X]
-- play the same structural role.

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local notation "𝔽₃" => ZMod 3
open Polynomial

-- p(X) = X² + 1 has no roots in 𝔽₃: p(0)=1, p(1)=2, p(2)=2 — all nonzero.
-- Mathlib turns "no roots" into irreducibility for degree ≤ 3 polynomials.

noncomputable abbrev p3 : 𝔽₃[X] := X^2 + 1

lemma p3_natDegree : p3.natDegree = 2 := by
  show (X^2 + 1 : 𝔽₃[X]).natDegree = 2; compute_degree!

lemma p3_ne_zero : p3 ≠ 0 := by
  intro h; have := p3_natDegree
  rw [h, natDegree_zero] at this; exact absurd this (by norm_num)

lemma p3_irreducible : Irreducible p3 := by
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three
        (by rw [p3_natDegree]) (by rw [p3_natDegree]; decide)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx; rw [mem_roots p3_ne_zero, IsRoot] at hx
  fin_cases x <;> simp [p3] at hx <;> revert hx <;> decide

-- GF(9) := 𝔽₃[X] / (X² + 1).   α := [X] is a "formal root":  α² + 1 = 0.
noncomputable abbrev GF9 := AdjoinRoot p3
noncomputable abbrev α : GF9 := AdjoinRoot.root p3

instance : Fact (Irreducible p3) := ⟨p3_irreducible⟩
noncomputable instance : Field GF9 := inferInstance

-- 9 elements of the form  a + b·α  with  a, b ∈ 𝔽₃:
--   { 0, 1, 2, α, α+1, α+2, 2α, 2α+1, 2α+2 }

lemma p3_monic : p3.Monic := by
  show (X^2 + 1 : 𝔽₃[X]).Monic; apply monic_X_pow_add_C; decide

noncomputable instance : Module.Finite 𝔽₃ GF9 := p3_monic.finite_adjoinRoot
instance : Finite GF9 := Module.finite_of_finite 𝔽₃
noncomputable instance : Fintype GF9 := Fintype.ofFinite GF9

example : Fintype.card GF9 = 9 := by
  rw [Module.card_fintype (AdjoinRoot.powerBasisAux' p3_monic)]
  simp [p3_natDegree, ZMod.card]

-- ============================================================================
-- Section 5: The First Isomorphism Theorem
-- ============================================================================
--
-- The bridge between ideals-as-kernels (Ideals.lean §5) and quotients:
--
--   For any ring hom φ : R → S,    R / ker(φ)  ≅  image(φ)
--
-- Mathlib: `RingHom.quotientKerEquivOfSurjective` (surjective case),
--          `RingHom.quotientKerEquivRange`        (general).

-- φ = Int.castRingHom (ZMod 5) is surjective with kernel (5):
example : Function.Surjective (Int.castRingHom (ZMod 5)) := ZMod.intCast_surjective
example : RingHom.ker (Int.castRingHom (ZMod 5)) = Ideal.span ({(5 : ℤ)} : Set ℤ) :=
  ZMod.ker_intCastRingHom 5

-- First Iso then hands us  ℤ / (5)  ≅  ZMod 5  for free:
noncomputable example :
    (ℤ ⧸ RingHom.ker (Int.castRingHom (ZMod 5))) ≃+* ZMod 5 :=
  RingHom.quotientKerEquivOfSurjective ZMod.intCast_surjective

-- This is the engine behind §2's `Int.quotientSpanNatEquivZMod`. The recipe
-- generalizes — for any surjective hom φ : R → S, R/ker(φ) is automatically S:
--   ℝ[X] / (X² + 1)  ≅  ℂ        via  X ↦ i
--   𝔽₃[X] / (X² + 1) ≅  GF(9)    via  X ↦ α
--   ℤ[X] / (X² + 1)  ≅  ℤ[i]     via  X ↦ i

-- ============================================================================
-- Section 6: ℝ[X] / (X² + 1) ≅ ℂ — the showpiece
-- ============================================================================
--
-- The most famous quotient: ℂ. X² + 1 has no real roots (x² + 1 > 0), so
-- it's irreducible, so the quotient is a field. The element [X] squares to
-- -1 — that's i. Every element is a + b·[X], which is a + b·i.

example : ∀ x : ℝ, eval x ((X^2 + 1 : ℝ[X])) ≠ 0 := by
  intro x
  simp only [eval_add, eval_pow, eval_X, eval_one]
  positivity

-- (Mathlib defines `Complex` as primitive pairs (re, im) — we don't formalize
-- the iso here. The recipe is the same as GF(9):
--    PID  +  irreducible  +  AdjoinRoot  =  field extension)

-- ============================================================================
-- Section 7: The universal property of the quotient
-- ============================================================================
--
-- The projection sends elements INTO the quotient. The universal property
-- tells us how to map OUT:
--
--   For any ring hom  φ : R → S  with  I ⊆ ker(φ),
--   there is a UNIQUE  φ̄ : R ⧸ I → S  with  φ = φ̄ ∘ π.
--
--     R ──φ──→ S
--      \     ↗
--       π   ∃! φ̄
--        ↘ /
--        R⧸I
--
-- Mathlib: `Ideal.Quotient.lift`.

-- The cast hom ℤ → ZMod 5 kills (5), so it factors through ℤ ⧸ (5):
example : (ℤ ⧸ I5) →+* ZMod 5 :=
  Ideal.Quotient.lift I5 (Int.castRingHom (ZMod 5)) (fun _ ha => by
    rw [← RingHom.mem_ker, ZMod.ker_intCastRingHom]
    exact ha
  )

-- The full picture:
--   mk    : R   → R ⧸ I        (into the quotient)
--   lift  : R/I → S             (out, for any I-killing φ)
--   first : R/ker ≅ image       (special case: φ surjective)
