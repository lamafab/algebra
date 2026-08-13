import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic

-- ============================================================================
-- Binary Fields: GF(2) and GF(2ⁿ)
-- ============================================================================
--
-- A binary field is a finite field of characteristic 2, the smallest possible
-- prime characteristic. The prime binary field GF(2) = {0,1} is the field of
-- two elements. Its extension GF(2ⁿ) is the field with 2ⁿ elements.
--
-- Why "binary"? Because in GF(2), addition *is* XOR and multiplication *is*
-- AND. So every boolean circuit is an arithmetic circuit over GF(2) with the
-- same gate count. This makes binary fields the natural home for proving
-- bit-oriented hash functions (SHA-2, BLAKE) inside a SNARK, for example.
--
-- Prerequisites: Galois.lean for the general theory of finite fields.
--
--   §1  GF(2): the field of two elements
--   §2  Boolean gates as polynomials over GF(2)
--   §3  GF(2ⁿ): extension fields of characteristic 2
--   §4  Freshman's dream, Frobenius, and the trace map
--   §5  The tower of binary fields
--   §6  Boolean circuits = arithmetic circuits over GF(2)

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

notation "𝔽₂" => ZMod 2

-- ============================================================================
-- Section 1: 𝔽₂, the field of two elements
-- ============================================================================

-- 𝔽₂ = ZMod 2 is a finite field (Galois.lean §1).
instance : Field 𝔽₂     := inferInstance
instance : Fintype 𝔽₂   := inferInstance
instance : CharP 𝔽₂ 2   := inferInstance

-- The elements are 0 and 1.
example : Fintype.card 𝔽₂ = 2 := by decide

-- Every nonzero element is invertible.
example (a : 𝔽₂) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ ha

-- The multiplicative group is trivial (cyclic of order 1).
instance : IsCyclic 𝔽₂ˣ := inferInstance
example : Fintype.card 𝔽₂ˣ = 1 := by decide

-- Characteristic 2: 1 + 1 = 0.
example : (1 + 1 : 𝔽₂) = 0 := by decide

-- So every element is its own additive inverse: a + a = 0.
example (a : 𝔽₂) : a + a = 0 := by
  fin_cases a <;> decide

-- Equivalently, subtraction is the same as addition: a − b = a + b.
example (a b : 𝔽₂) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

-- Elements are idempotent under squaring: a² = a (since the only elements are
-- 0 and 1, both satisfy this).
example (a : 𝔽₂) : a^2 = a := by
  fin_cases a <;> decide

-- ============================================================================
-- Section 2: Boolean gates as polynomials over 𝔽₂
-- ============================================================================
--
-- Because 𝔽₂ addition is XOR and multiplication is AND, every boolean gate can
-- be expressed as a polynomial with coefficients in 𝔽₂:

--   NOT(x) = 1 + x    (since ¬0 = 1, ¬1 = 0)
example : (fun (x : 𝔽₂) => 1 + x) 0 = 1 := by decide
example : (fun (x : 𝔽₂) => 1 + x) 1 = 0 := by decide

--   AND(x,y) = x·y
example : (fun (x y : 𝔽₂) => x * y) 0 0 = 0 := by decide
example : (fun (x y : 𝔽₂) => x * y) 0 1 = 0 := by decide
example : (fun (x y : 𝔽₂) => x * y) 1 0 = 0 := by decide
example : (fun (x y : 𝔽₂) => x * y) 1 1 = 1 := by decide

--   OR(x,y) = x + y + x·y
example : (fun (x y : 𝔽₂) => x + y + x * y) 0 0 = 0 := by decide
example : (fun (x y : 𝔽₂) => x + y + x * y) 0 1 = 1 := by decide
example : (fun (x y : 𝔽₂) => x + y + x * y) 1 0 = 1 := by decide
example : (fun (x y : 𝔽₂) => x + y + x * y) 1 1 = 1 := by decide

--   XOR(x,y) = x + y
example : (fun (x y : 𝔽₂) => x + y) 0 0 = 0 := by decide
example : (fun (x y : 𝔽₂) => x + y) 0 1 = 1 := by decide
example : (fun (x y : 𝔽₂) => x + y) 1 0 = 1 := by decide
example : (fun (x y : 𝔽₂) => x + y) 1 1 = 0 := by decide

--   NAND(x,y) = 1 + x·y
example : (fun (x y : 𝔽₂) => 1 + x * y) 0 0 = 1 := by decide
example : (fun (x y : 𝔽₂) => 1 + x * y) 0 1 = 1 := by decide
example : (fun (x y : 𝔽₂) => 1 + x * y) 1 0 = 1 := by decide
example : (fun (x y : 𝔽₂) => 1 + x * y) 1 1 = 0 := by decide

-- Every boolean function f : {0,1}ⁿ → {0,1} can be written uniquely as a
-- multilinear polynomial over 𝔽₂ (the "algebraic normal form", ANF).  For
-- example, the majority function Maj(x,y,z) = xy + yz + xz:
def majority (x y z : 𝔽₂) : 𝔽₂ := x * y + y * z + x * z

-- Its truth table matches the boolean majority gate:
example : majority 0 0 0 = 0 := by decide
example : majority 0 0 1 = 0 := by decide
example : majority 0 1 0 = 0 := by decide
example : majority 0 1 1 = 1 := by decide
example : majority 1 0 0 = 0 := by decide
example : majority 1 0 1 = 1 := by decide
example : majority 1 1 0 = 1 := by decide
example : majority 1 1 1 = 1 := by decide

-- ============================================================================
-- Section 3: GF(2ⁿ), extension fields of characteristic 2
-- ============================================================================
--
-- For any n ≥ 1, there exists a unique (up to isomorphism) field GF(2ⁿ) with
-- 2ⁿ elements.  In Mathlib it is constructed as `GaloisField 2 n`, the
-- splitting field of X^{2ⁿ} − X over 𝔽₂.  It is noncomputable (the field is
-- defined by its universal property, not by explicit arithmetic), so we can
-- prove theorems about it but cannot `dec_trivial` or `native_decide`
-- element-wise.

open FiniteField

noncomputable section

-- GF(2ⁿ) is a field of characteristic 2.
example (n : ℕ) : Field (GaloisField 2 n) := by infer_instance
example (n : ℕ) : CharP (GaloisField 2 n) 2 := by infer_instance

-- GF(2ⁿ) is a finite extension of 𝔽₂ of degree n.
example (n : ℕ) : Finite (GaloisField 2 n) := by
  infer_instance

-- Finite fields of order 2ⁿ satisfy x^{2ⁿ} = x for all x (Fermat's little
-- theorem for finite fields).
#check FiniteField.pow_card

-- The multiplicative group GF(2ⁿ)ˣ is cyclic of order 2ⁿ − 1 (odd; there
-- are NO 2-power roots of unity in the multiplicative group).
example (n : ℕ) : IsCyclic (Units (GaloisField 2 n)) := by infer_instance

-- Unique: any two finite fields of the same order are isomorphic.
#check @FiniteField.algEquivOfCardEq

-- Subfield structure: GF(2ᵐ) embeds into GF(2ⁿ) iff m ∣ n.
#check @FiniteField.nonempty_algHom_iff_finrank_dvd

-- ============================================================================
-- Section 4: Freshman's dream, Frobenius, and the trace map
-- ============================================================================
--
-- In characteristic 2, squaring is a ring homomorphism: (x + y)² = x² + y²
-- ("Freshman's dream").  The map x ↦ x² is the Frobenius automorphism.

-- Freshman's dream over 𝔽₂:
example (x y : 𝔽₂) : (x + y)^2 = x^2 + y^2 :=
  add_pow_char (R := 𝔽₂) (x := x) (y := y) (p := 2)

-- Over any binary field GF(2ⁿ):
example (F : Type*) [Field F] [CharP F 2] (x y : F) : (x + y)^2 = x^2 + y^2 :=
  add_pow_char (R := F) (x := x) (y := y) (p := 2)

-- Multiplication also works: (x·y)² = x²·y² (true in any commutative ring).
example (F : Type*) [CommRing F] (x y : F) : (x * y)^2 = x^2 * y^2 := by ring

-- The Frobenius map F(x) = x² is a field automorphism of GF(2ⁿ) over 𝔽₂,
-- meaning it respects addition, multiplication, and fixes 𝔽₂ pointwise.
#check frobeniusAlgEquiv (ZMod 2) (GaloisField 2 4) 2

-- Applying Frobenius to an element gives x²:
example (x : GaloisField 2 4) : frobeniusAlgEquiv (ZMod 2) (GaloisField 2 4) 2 x = x^2 := by
  simp

-- Its powers generate the Galois group Gal(GF(2ⁿ)/𝔽₂) ≅ ℤ/nℤ.  The k-th
-- iterate is x ↦ x^{2ᵏ}.
example (x : GaloisField 2 4) (k : ℕ) :
    (frobeniusAlgEquiv (ZMod 2) (GaloisField 2 4) 2)^[k] x = x^(2^k) := by
  induction' k with k ih
  · simp
  · simp [ih, pow_succ, pow_mul]

-- The trace map Tr_{GF(2ⁿ)/𝔽₂} : GF(2ⁿ) → 𝔽₂ is the sum of the Galois
-- conjugates: Tr(x) = x + x² + x⁴ + ... + x^{2ⁿ⁻¹}.
--
-- Mathlib provides it as `Algebra.trace 𝔽₂ (GaloisField 2 n)`, and the
-- formula above is given by the lemma `algebraMap_trace_eq_sum_pow` from
-- `FieldTheory.Finite.Trace`.
#check Algebra.trace (𝔽₂) (GaloisField 2 4)

-- The trace formula for GF(2ⁿ)/𝔽₂: Tr(x) embedded into GF(2ⁿ) equals
-- Σ_{i=0}^{n-1} x^{2ⁱ}.  The actual trace lives in 𝔽₂.
-- (The RHS is written as x^(2^i) because Nat.card 𝔽₂ = 2.)
example (n : ℕ) (x : GaloisField 2 n) :
    algebraMap 𝔽₂ (GaloisField 2 n) (Algebra.trace 𝔽₂ (GaloisField 2 n) x) =
      ∑ i ∈ Finset.range (Module.finrank 𝔽₂ (GaloisField 2 n)), x ^ (Nat.card 𝔽₂ ^ i) :=
  algebraMap_trace_eq_sum_pow 𝔽₂ (GaloisField 2 n) x

-- The trace is linear over 𝔽₂, i.e., Tr(x + y) = Tr(x) + Tr(y) and
-- Tr(c·x) = c·Tr(x) for c ∈ 𝔽₂.
#check (Algebra.trace 𝔽₂ (GaloisField 2 4) : (GaloisField 2 4) →ₗ[𝔽₂] 𝔽₂)

-- The trace is nonzero (it is a surjective linear map onto 𝔽₂).
#check FiniteField.trace_to_zmod_nondegenerate

end

-- ============================================================================
-- Section 5: The tower of binary fields
-- ============================================================================
--
-- Binary fields pack neatly into towers: GF(2) ⊂ GF(2²) ⊂ GF(2⁴) ⊂ ... ⊂
-- GF(2^{2ᵏ}).  Each step is a degree-2 extension, built by adjoining a root
-- of t² + t + β for some β in the base field.  This "tower" representation
-- is what makes Binius arithmetic efficient: elements are bit-packed, addition
-- is XOR of the packed bits, and the Frobenius/trace maps decompose along the
-- tower.

-- Subfield embedding: GF(2²) ⊂ GF(2⁴) because 2 ∣ 4.
example : Nonempty (GaloisField 2 2 →ₐ[𝔽₂] GaloisField 2 4) :=
  (FiniteField.nonempty_algHom_iff_finrank_dvd (F := 𝔽₂) (K := GaloisField 2 2) (L := GaloisField 2 4)).mpr (by
    -- finrank(GF(2⁴)/𝔽₂) = 4, finrank(GF(2²)/𝔽₂) = 2, and 2 ∣ 4.
    have h2 : Module.finrank 𝔽₂ (GaloisField 2 2) = 2 := by
      apply GaloisField.finrank (p := 2) (n := 2)
      norm_num
    have h4 : Module.finrank 𝔽₂ (GaloisField 2 4) = 4 := by
      apply GaloisField.finrank (p := 2) (n := 4)
      norm_num
    rw [h2, h4]
    exact ⟨2, by norm_num⟩)

-- ============================================================================
-- Section 6: Boolean circuits = arithmetic circuits over 𝔽₂
-- ============================================================================
--
-- A boolean circuit on w wires can be represented as an arithmetic circuit
-- over 𝔽₂: each boolean gate becomes a polynomial, and the circuit output is
-- a multivariate polynomial over 𝔽₂.  Packing w bits into one element of
-- GF(2ʷ) lets the circuit process them in one field operation.
--
-- The simplest example: a half-adder.  Given bits a, b, the sum is S = a + b
-- (XOR) and the carry is C = a·b (AND).  This is exactly the arithmetic over
-- 𝔽₂.

def halfAdderSum (a b : 𝔽₂) : 𝔽₂ := a + b
def halfAdderCarry (a b : 𝔽₂) : 𝔽₂ := a * b

example : halfAdderSum 0 0 = 0 := by decide
example : halfAdderSum 0 1 = 1 := by decide
example : halfAdderSum 1 0 = 1 := by decide
example : halfAdderSum 1 1 = 0 := by decide

example : halfAdderCarry 0 0 = 0 := by decide
example : halfAdderCarry 0 1 = 0 := by decide
example : halfAdderCarry 1 0 = 0 := by decide
example : halfAdderCarry 1 1 = 1 := by decide

-- A full adder is built from two half-adders.
def fullAdderSum (a b c : 𝔽₂) : 𝔽₂ := a + b + c
def fullAdderCarry (a b c : 𝔽₂) : 𝔽₂ := a * b + (a + b) * c

-- The carry expression matches the boolean majority:
example (a b c : 𝔽₂) : fullAdderCarry a b c = majority a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
