import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

-- ============================================================================
-- Euclidean Domains: division, Bézout, and fields from irreducibles
-- ============================================================================
--
-- Why is ℤ/(p) a field when p is prime, and F[X]/(m) a field when m is
-- irreducible? Both answers rest on one elementary fact: division with
-- remainder. From it the Euclidean algorithm produces Bézout coefficients,
-- Bézout produces inverses modulo anything with no factors, and inverses
-- are exactly what a quotient needs to be a field.
--
-- Terminology, since the standard names hide how little is going on:
--   - integral domain: a commutative ring with no zero divisors
--     (a * b = 0 ⟹ a = 0 or b = 0). The world where cancellation is legal.
--   - UFD (unique factorization domain): everything factors into
--     irreducibles uniquely, so "irreducible" and "prime" coincide.
--   - Euclidean domain: has division with remainder. The chain
--     "Euclidean ⟹ PID ⟹ UFD" is textbook packaging; the engine, for ℤ
--     and F[X], is just long division, and that is what this file uses.
--
-- Prerequisites: Ideals.lean for quotient rings. Pairs with
-- Field/VectorSpaces.lean, whose §5 hand-rolls the same quotient as §4
-- here, and whose theme (GF(pⁿ) as remainders mod an irreducible) is the
-- payoff.
--
--   §1  Division with remainder
--   §2  The Euclidean algorithm and Bézout's identity
--   §3  Irreducible modulus ⟹ every nonzero remainder is coprime to it
--   §4  The quotient: field if irreducible, zero divisors if reducible
--   §5  Why domains matter: the roots bound, and where it fails

open Polynomial

-- ============================================================================
-- Section 1: Division with remainder
-- ============================================================================
--
-- In ℤ: for any a and nonzero b there are q, r with a = q*b + r and
-- 0 ≤ r < |b|. In F[X]: same with "smaller" meaning "smaller degree".
-- Mathlib packages this as the typeclass EuclideanDomain, with the
-- quotient-remainder identity as div_add_mod.

-- divisor · quotient + remainder = dividend
example (a b : ℤ) : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b

-- 37 = 3 * 11 + 4.
example : (37 : ℤ) / 11 = 3 ∧ (37 : ℤ) % 11 = 4 := by decide

-- Polynomial long division over GF(2): X³ + X + 1 = X·(X² + 1) + 1.
-- The remainder 1 has degree < 2, the degree of the divisor X² + 1.
example : (X^3 + X + 1 : (ZMod 2)[X]) = X * (X^2 + 1) + 1 := by ring

-- ============================================================================
-- Section 2: The Euclidean algorithm and Bézout's identity
-- ============================================================================
--
-- Iterating division with remainder drives the remainders down to the
-- gcd; unwinding the steps expresses the gcd as a combination of the
-- inputs. So for any a, b there exist s, t with s*a + t*b = gcd(a, b):
-- Bézout's identity. Mathlib's gcdA and gcdB are those coefficients, and
-- gcd_eq_gcd_ab is the identity.

#check @EuclideanDomain.gcd_eq_gcd_ab
-- EuclideanDomain.gcd_eq_gcd_ab (a b : R) :
--   gcd a b = a * gcdA a b + b * gcdB a b

-- For 12 and 18 the gcd is 6, and the coefficients are −1 and 1.
example : Int.gcd 12 18 = 6 := by decide
example : Int.gcdA 12 18 * 12 + Int.gcdB 12 18 * 18 = (Int.gcd 12 18 : ℤ) := by
  native_decide
example : (-1 : ℤ) * 12 + 1 * 18 = 6 := by norm_num

-- Over GF(2)[X], one division step is already the whole algorithm for
-- X and X³ + X + 1: the identity from §1 rearranges (char 2) to
-- Bézout form, (X² + 1)·X + 1·(X³ + X + 1) = 1.
example : (X^2 + 1 : (ZMod 2)[X]) * X + 1 * (X^3 + X + 1) = 1 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ _
  ring_nf
  simp [h2]

-- Reading Bézout mod m: s*g + t*m = 1 says s*g ≡ 1 (mod m). So whenever
-- the gcd is 1, g has an inverse modulo m, namely s. Here: X⁻¹ = X² + 1
-- modulo X³ + X + 1. G8.lean verifies the same fact with decide,
-- as α * (α² + 1) = 1.

-- ============================================================================
-- Section 3: Irreducible modulus ⟹ every nonzero remainder is coprime
-- ============================================================================
--
-- Irreducible means no nontrivial factorizations; it is the polynomial
-- analogue of prime. In a Euclidean domain, an irreducible x has the key
-- prime-like property: for every y, either x ∣ y or gcd(x, y) = 1.

#check @EuclideanDomain.dvd_or_coprime
-- EuclideanDomain.dvd_or_coprime (x y : α) :
--   Irreducible x → x ∣ y ∨ IsCoprime x y

-- The running modulus gets a name, and is irreducible over GF(2): a
-- factorization of a degree-3 polynomial needs a degree-1 factor, hence
-- a root; evaluating at 0 and 1 rules that out.

/-- The running example modulus. -/
noncomputable def modPoly : (ZMod 2)[X] := X^3 + X + 1

theorem irreducible_modPoly : Irreducible modPoly := by
  show Irreducible (X^3 + X + 1 : (ZMod 2)[X])
  exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [show (X^3 + X + 1 : (ZMod 2)[X]).natDegree = 3 by compute_degree!]; decide)
    (fun x => by fin_cases x <;> simp [Polynomial.IsRoot] <;> decide)

-- X is not a multiple of modPoly: a divisor cannot have larger degree
-- than a nonzero element it divides.
theorem not_modPoly_dvd_X : ¬ modPoly ∣ X := by
  intro hdiv
  have hle := Polynomial.natDegree_le_of_dvd hdiv X_ne_zero
  have hdeg : modPoly.natDegree = 3 := by
    show (X^3 + X + 1 : (ZMod 2)[X]).natDegree = 3; compute_degree!
  rw [hdeg, natDegree_X] at hle
  omega

-- So the dichotomy gives gcd(modPoly, X) = 1: the Bézout coefficients of
-- §2 exist, and X is invertible modulo modPoly. IsCoprime m g is defined
-- as ∃ s t, s * m + t * g = 1, i.e. exactly Bézout.
example : IsCoprime modPoly X := by
  rcases EuclideanDomain.dvd_or_coprime _ _ irreducible_modPoly with hd | hc
  · exact absurd hd not_modPoly_dvd_X
  · exact hc

-- ============================================================================
-- Section 4: The quotient: field if irreducible, zero divisors if reducible
-- ============================================================================
--
-- The same theorem twice:
--   ℤ/(n)    is a field iff n is prime
--   F[X]/(m) is a field iff m is irreducible
-- and both directions are visible concretely.

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- ℤ/(5) is a field: every nonzero residue is invertible.
example : Field (ZMod 5) := inferInstance
example : (2 : ZMod 5) * 3 = 1 := by decide

-- ℤ/(6) is not: 2 and 3 are nonzero with product zero.
example : (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by decide

-- AdjoinRoot f is Mathlib's F[α]/(f), with α = mk f X the image of the
-- indeterminate. With modPoly irreducible (§3), the quotient is a field.
instance : Fact (Irreducible modPoly) := ⟨irreducible_modPoly⟩
#synth Field (AdjoinRoot modPoly)
#check @AdjoinRoot.instField
-- AdjoinRoot.instField [Fact (Irreducible f)] : Field (AdjoinRoot f)

-- The inverse of α = mk modPoly X is certified by Bézout: the identity
-- X·(X² + 1) = 1 + 1·modPoly maps through the quotient map, where the
-- modPoly term dies (mk_self). So mk X * mk (X² + 1) = 1.
example : (AdjoinRoot.mk modPoly X) * (AdjoinRoot.mk modPoly (X^2 + 1)) = 1 := by
  have hid : (X * (X^2 + 1) : (ZMod 2)[X]) = 1 + 1 * modPoly := by
    show X * (X^2 + 1) = 1 + 1 * (X^3 + X + 1 : (ZMod 2)[X])
    have h2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ _
    ring_nf
    simp [h2]
  rw [← map_mul, hid, map_add, map_mul, map_one, AdjoinRoot.mk_self, mul_zero, add_zero]

-- With a reducible modulus the wrap relation manufactures zero divisors:
-- in GF(2)[X]/(X³), the relation X³ = 0 makes X and X² nonzero with
-- product zero.
example : (AdjoinRoot.mk (X^3 : (ZMod 2)[X]) X)
    * (AdjoinRoot.mk (X^3 : (ZMod 2)[X]) (X^2)) = 0 := by
  rw [← map_mul, show (X * X^2 : (ZMod 2)[X]) = X^3 by ring, AdjoinRoot.mk_self]

example : (AdjoinRoot.mk (X^3 : (ZMod 2)[X]) X) ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow 3) X_ne_zero (by compute_degree!)

example : (AdjoinRoot.mk (X^3 : (ZMod 2)[X]) (X^2)) ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow 3) (pow_ne_zero 2 X_ne_zero)
    (by compute_degree!)

-- Note: AdjoinRoot does not evaluate with decide, which is why G8.lean
-- hand-rolls this same quotient GF(2)[X]/(X³ + X + 1) as bit triples.

-- ============================================================================
-- Section 5: Why domains matter: the roots bound, and where it fails
-- ============================================================================
--
-- The no-zero-divisors property is exactly what bounds a polynomial's
-- roots by its degree: if a product of linear factors is zero, one factor
-- is zero, so each root supplies one factor and factors compose at most
-- deg-many times. Mathlib states it for any integral domain.

#check @Polynomial.card_roots'
-- Polynomial.card_roots' (p : R[X]) [IsDomain R] :
--   p.roots.card ≤ p.natDegree

-- Over a non-domain the bound fails: X² − X has 4 roots in ℤ/6ℤ, since
-- both 0, 1 and the zero-divisor pair residues 3, 4 satisfy it.
example : ∀ x : ZMod 6, x^2 - x = 0 ↔ x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 4 := by decide

-- This is why the sumcheck and FRI soundness analyses run over a field:
-- their per-round error bounds are applications of the roots bound, and
-- the roots bound is false without no-zero-divisors.
