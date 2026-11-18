import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Bulletproofs: short proofs for secret values and arithmetic circuits
-- ============================================================================
--
-- A Bulletproof proves that a committed value lies in an interval, or more
-- generally that an arithmetic circuit is satisfied, without revealing the
-- secret inputs. There is no trusted setup. For a vector of length n the main
-- argument has 2·log₂(n) group elements plus two final scalars, rather than a
-- proof containing all n secret coordinates.
--
-- The construction has three layers:
--
--   secret value v
--     │  Pedersen commitment: V = v·G + γ·H
--     ▼
--   binary decomposition v = Σᵢ 2ⁱ·aᵢ, with every aᵢ ∈ {0,1}
--     │  random challenges fold all bit constraints into one inner product
--     ▼
--   inner-product argument: halve the vectors in every round
--
-- This file develops the algebra of all three layers:
--
--   §1  Pedersen commitments: homomorphism and binding from independence
--   §2  Bit decomposition and the polynomial identity behind a range proof
--   §3  The inner-product commitment and its two cross terms
--   §4  One folding round, with exact verifier-side correctness
--   §5  A computed four-coordinate proof over ZMod 101
--   §6  Proof sizes, security assumptions, and what is not formalized
--
-- The worked instance uses the additive group of ZMod 101 for arithmetic
-- convenience. It is not cryptographically secure: in a real instance the
-- group is a large prime-order elliptic-curve group and discrete logs are
-- hard. The distinction between proved equations and security assumptions is
-- stated explicitly in §6.

namespace Bulletproofs

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Scalar vectors and group-generator vectors are functions on `Fin n`. -/
abbrev Vec (F : Type*) (n : ℕ) := Fin n → F

/-- The inner product of two scalar vectors. -/
def inner {n : ℕ} (a b : Vec F n) : F := ∑ i, a i * b i

/-- A multiexponentiation: the Pedersen vector commitment `<a, gs>`. -/
def combine {n : ℕ} (a : Vec F n) (gs : Fin n → G) : G := ∑ i, a i • gs i

/-- Componentwise multiplication, also called the Hadamard product. -/
def hadamard {n : ℕ} (a b : Vec F n) : Vec F n := fun i => a i * b i

/-- The vector `[1, y, y², ...]`. -/
def powers {n : ℕ} (y : F) : Vec F n := fun i => y ^ i.val

/-- The little-endian binary weights `[1, 2, 4, ...]`. -/
def twoPowers (n : ℕ) : Vec F n := fun i => 2 ^ i.val

/-- Multiexponentiation is linear in the scalar vector. -/
theorem combine_add_left {n : ℕ} (a b : Vec F n) (gs : Fin n → G) :
    combine (a + b) gs = combine a gs + combine b gs := by
  simp [combine, add_smul, Finset.sum_add_distrib]

/-- Multiexponentiation respects scalar multiplication on the left. -/
theorem combine_smul_left {n : ℕ} (c : F) (a : Vec F n) (gs : Fin n → G) :
    combine (c • a) gs = c • combine a gs := by
  simp [combine, Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- Multiexponentiation is additive in the generator vector. -/
theorem combine_add_right {n : ℕ} (a : Vec F n) (gs hs : Fin n → G) :
    combine a (gs + hs) = combine a gs + combine a hs := by
  simp [combine, smul_add, Finset.sum_add_distrib]

/-- Multiexponentiation respects scalar multiplication on the right. -/
theorem combine_smul_right {n : ℕ} (c : F) (a : Vec F n) (gs : Fin n → G) :
    combine a (c • gs) = c • combine a gs := by
  simp [combine, Pi.smul_apply, smul_smul, Finset.smul_sum, mul_comm]

/-- Inner products are additive in the first argument. -/
theorem inner_add_left {n : ℕ} (a b c : Vec F n) :
    inner (a + b) c = inner a c + inner b c := by
  simp [inner, add_mul, Finset.sum_add_distrib]

/-- Inner products are additive in the second argument. -/
theorem inner_add_right {n : ℕ} (a b c : Vec F n) :
    inner a (b + c) = inner a b + inner a c := by
  simp [inner, mul_add, Finset.sum_add_distrib]

/-- Inner products are homogeneous in the first argument. -/
theorem inner_smul_left {n : ℕ} (x : F) (a b : Vec F n) :
    inner (x • a) b = x * inner a b := by
  simp [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Inner products are homogeneous in the second argument. -/
theorem inner_smul_right {n : ℕ} (x : F) (a b : Vec F n) :
    inner a (x • b) = x * inner a b := by
  simp [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

-- ============================================================================
-- Section 1: Pedersen commitments
-- ============================================================================
--
-- A commitment to v with blinding factor γ is
--
--   commit(v, γ) = v·G + γ·H.
--
-- The value term binds the statement; the blinding term hides v. Both group
-- generators are public. The additive notation matches elliptic-curve
-- implementations. In a multiplicative group the same formula is Gᵛ·Hᵞ.

/-- A Pedersen commitment to `v`, with secret blinding factor `r`. -/
def commit (g h : G) (v r : F) : G := v • g + r • h

/-- Commitments are additively homomorphic, including their blinding factors. -/
theorem commit_add (g h : G) (v₁ v₂ r₁ r₂ : F) :
    commit g h (v₁ + v₂) (r₁ + r₂) = commit g h v₁ r₁ + commit g h v₂ r₂ := by
  simp only [commit, add_smul]
  module

/-- Scaling a committed value scales the whole commitment. -/
theorem commit_smul (g h : G) (c v r : F) :
    commit g h (c * v) (c * r) = c • commit g h v r := by
  simp only [commit, smul_add, smul_smul]

/-- If `g` and `h` are treated as independent, two openings have the same
value and the same blinding factor. This is the algebraic content of binding.
In a prime-order group a scalar relation always exists; cryptographic binding
assumes that an adversary cannot find it. -/
theorem commit_unique_of_independent (g h : G)
    (independent : ∀ c d : F, c • g + d • h = 0 → c = 0 ∧ d = 0)
    {v₁ v₂ r₁ r₂ : F}
    (heq : commit g h v₁ r₁ = commit g h v₂ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  have hzero : (v₁ - v₂) • g + (r₁ - r₂) • h = 0 := by
    calc
      (v₁ - v₂) • g + (r₁ - r₂) • h =
          commit g h v₁ r₁ - commit g h v₂ r₂ := by
        simp only [commit, sub_smul]
        abel
      _ = 0 := sub_eq_zero.mpr heq
  have h := independent _ _ hzero
  exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩

-- Hiding is a statement about distributions, not just this group equation.
-- If H is nonidentity and γ is uniform, then γ·H is uniform. Adding v·G only
-- translates that distribution, so the commitment alone has the same
-- distribution for every v. Finding γ from the commitment is a discrete log.

-- ============================================================================
-- Section 2: From a range to an inner product
-- ============================================================================

/-- The natural number represented by little-endian binary digits. -/
def bitValue {n : ℕ} (a : Fin n → ℕ) : ℕ := ∑ i, 2 ^ i.val * a i

/-- Split off the least significant bit of a binary decomposition. -/
theorem bitValue_succ {n : ℕ} (a : Fin (n + 1) → ℕ) :
    bitValue a = a 0 + 2 * bitValue (fun i => a i.succ) := by
  simp only [bitValue, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  apply congrArg (a 0 + ·)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `n` binary digits represent exactly the interval `0 ≤ v < 2^n`. -/
theorem bitValue_lt {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, a i < 2) :
    bitValue a < 2 ^ n := by
  induction n with
  | zero => simp [bitValue]
  | succ n ih =>
      rw [bitValue_succ]
      have htail : bitValue (fun i => a i.succ) < 2 ^ n :=
        ih (fun i => a i.succ) (fun i => ha i.succ)
      have hhead := ha 0
      rw [pow_succ]
      omega

/-- The field equation selecting the two binary values. -/
def bitConstraint (b : F) : F := b * (1 - b)

/-- Over any field, `b·(1-b) = 0` says precisely `b ∈ {0,1}`. -/
theorem bitConstraint_eq_zero_iff (b : F) : bitConstraint b = 0 ↔ b = 0 ∨ b = 1 := by
  rw [bitConstraint, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (sub_self 1)

/-- Casting a natural binary decomposition into a field preserves its weighted
sum. In a scalar field of order q, range proofs take `2^n < q` so that two
different integers in the interval cannot become equal by wrapping modulo q. -/
theorem cast_bitValue {n : ℕ} (a : Fin n → ℕ) :
    (bitValue a : F) = inner (fun i => (a i : F)) (twoPowers n) := by
  simp [bitValue, inner, twoPowers, mul_comm]

/-- `aR` is the complementary bit vector when `aL` contains bits. -/
def complement {n : ℕ} (a : Vec F n) : Vec F n := a - 1

/-- The unblinded left polynomial in the range-proof construction. -/
def rangeLeft {n : ℕ} (aL : Vec F n) (z : F) : Vec F n := aL - z • 1

/-- The unblinded right polynomial. The powers of `y` keep coordinates
separate, while `z²·2^n` attaches the claimed value to the bit vector. -/
def rangeRight {n : ℕ} (aR : Vec F n) (y z : F) : Vec F n :=
  hadamard (powers y) (aR + z • 1) + z ^ 2 • twoPowers n

/-- The offset in the Bulletproofs range identity. -/
def rangeOffset (n : ℕ) (y z : F) : F :=
  (z - z ^ 2) * inner (1 : Vec F n) (powers y) -
    z ^ 3 * inner (1 : Vec F n) (twoPowers n)

/-- The central range identity. If `aR = aL - 1` and every coordinate of `aL`
is a bit, then

  `<aL-z·1, y^n ∘ (aR+z·1) + z²·2^n>`
    `= z²·v + (z-z²)·<1,y^n> - z³·<1,2^n>`,

where `v = <aL,2^n>`. The right side contains only the claimed value and
public challenge-dependent offsets. -/
theorem range_inner_product {n : ℕ} (aL aR : Vec F n) (y z : F)
    (hcomplement : ∀ i, aR i = aL i - 1)
    (hbits : ∀ i, bitConstraint (aL i) = 0) :
    inner (rangeLeft aL z) (rangeRight aR y z) =
      z ^ 2 * inner aL (twoPowers n) + rangeOffset n y z := by
  simp only [inner, rangeLeft, rangeRight, rangeOffset, hadamard, powers,
    twoPowers, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcomplement i]
  have hb := hbits i
  rw [bitConstraint] at hb
  linear_combination -(y ^ i.val) * hb

/-- The prover blinds both vectors with `sL` and `sR` before evaluation at a
fresh challenge `x`. -/
def blindedLeft {n : ℕ} (aL sL : Vec F n) (z x : F) : Vec F n :=
  rangeLeft aL z + x • sL

/-- The blinding on the right also passes through the Hadamard product. -/
def blindedRight {n : ℕ} (aR sR : Vec F n) (y z x : F) : Vec F n :=
  rangeRight aR y z + x • hadamard (powers y) sR

/-- The three coefficients of `<l(X),r(X)>`. -/
def rangeT0 {n : ℕ} (aL aR : Vec F n) (y z : F) : F :=
  inner (rangeLeft aL z) (rangeRight aR y z)

/-- The linear coefficient. -/
def rangeT1 {n : ℕ} (aL aR sL sR : Vec F n) (y z : F) : F :=
  inner (rangeLeft aL z) (hadamard (powers y) sR) +
    inner sL (rangeRight aR y z)

/-- The quadratic coefficient, containing only the blinding vectors. -/
def rangeT2 {n : ℕ} (sL sR : Vec F n) (y : F) : F :=
  inner sL (hadamard (powers y) sR)

/-- Evaluating the blinded inner product gives a quadratic polynomial. The
prover commits to `t1` and `t2` before seeing `x`; the verifier later checks
the announced value `t(x)` against those commitments and the value commitment. -/
theorem blinded_inner_product {n : ℕ} (aL aR sL sR : Vec F n) (y z x : F) :
    inner (blindedLeft aL sL z x) (blindedRight aR sR y z x) =
      rangeT0 aL aR y z + x * rangeT1 aL aR sL sR y z +
        x ^ 2 * rangeT2 sL sR y := by
  have hleft : blindedLeft aL sL z x = rangeLeft aL z + x • sL := rfl
  have hright : blindedRight aR sR y z x =
      rangeRight aR y z + x • hadamard (powers y) sR := rfl
  simp only [inner, hleft, hright, rangeT0, rangeT1, rangeT2,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

-- Why the challenges matter. The single equation `<a, a-1> = 0` only says
-- that the sum of the bit errors is zero, so positive and negative errors can
-- cancel. Multiplying coordinate i by the independent power yⁱ prevents that
-- cancellation when the identity holds as a polynomial in y. The challenge z
-- separates the bit, complement, and value terms. The actual protocol samples
-- y and z after commitments to aL and aR, then samples x after commitments to
-- t1 and t2. Soundness bounds the probability that a nonzero polynomial
-- accidentally vanishes at these challenges.

-- ============================================================================
-- Section 3: Inner-product commitments and cross terms
-- ============================================================================
--
-- The remaining claim is `<a,b> = c` for secret vectors a and b. The public
-- commitment binds the vectors and their inner product together:
--
--   P = <a,gs> + <b,hs> + <a,b>·Q.
--
-- A separate c is unnecessary because it is already the coefficient of Q.
-- Split every vector into low and high halves:
--
--   a = aL | aH,  b = bL | bH,  gs = gsL | gsH,  hs = hsL | hsH.
--
-- Two cross commitments expose just the terms needed for one fold:
--
--   L = <aL,gsH> + <bH,hsL> + <aL,bH>·Q
--   R = <aH,gsL> + <bL,hsH> + <aH,bL>·Q.

/-- The low half of a vector of even length. -/
def low {α : Type*} {n : ℕ} (a : Fin (n + n) → α) : Fin n → α :=
  fun i => a (Fin.castAdd n i)

/-- The high half of a vector of even length. -/
def high {α : Type*} {n : ℕ} (a : Fin (n + n) → α) : Fin n → α :=
  fun i => a (Fin.natAdd n i)

/-- Split a multiexponentiation into its two halves. -/
theorem combine_split {n : ℕ} (a : Vec F (n + n)) (gs : Fin (n + n) → G) :
    combine a gs = combine (low a) (low gs) + combine (high a) (high gs) := by
  simp only [combine, low, high, Fin.sum_univ_add]

/-- Split an inner product into its two halves. -/
theorem inner_split {n : ℕ} (a b : Vec F (n + n)) :
    inner a b = inner (low a) (low b) + inner (high a) (high b) := by
  simp only [inner, low, high, Fin.sum_univ_add]

/-- The combined vector and inner-product commitment. -/
def ipaCommit {n : ℕ} (a b : Vec F n) (gs hs : Fin n → G) (q : G) : G :=
  combine a gs + combine b hs + inner a b • q

/-- The left cross commitment for one folding round. -/
def crossL {n : ℕ} (a b : Vec F (n + n)) (gs hs : Fin (n + n) → G) (q : G) : G :=
  combine (low a) (high gs) + combine (high b) (low hs) +
    inner (low a) (high b) • q

/-- The right cross commitment for one folding round. -/
def crossR {n : ℕ} (a b : Vec F (n + n)) (gs hs : Fin (n + n) → G) (q : G) : G :=
  combine (high a) (low gs) + combine (low b) (high hs) +
    inner (high a) (low b) • q

-- ============================================================================
-- Section 4: One logarithmic folding round
-- ============================================================================
--
-- After receiving L and R, the verifier samples x ≠ 0. Both sides compute
--
--   a'  = aL + x·aH          b'  = bL + x⁻¹·bH
--   gs' = gsL + x⁻¹·gsH      hs' = hsL + x·hsH
--   P'  = P + x⁻¹·L + x·R.
--
-- Each new vector has half the length. The mixed products are exactly L and R:
--
--   <a',b'> = <a,b> + x⁻¹·<aL,bH> + x·<aH,bL>,
--
-- and the two vector commitments have the same cross-term pattern. Repeating
-- log₂(n) rounds leaves vectors of length one, padding n to a power of two if
-- needed. The proof contains L,R for each round and the final two scalars a',b'.

/-- Fold the first secret vector. -/
def foldA {n : ℕ} (x : F) (a : Vec F (n + n)) : Vec F n := low a + x • high a

/-- Fold the second secret vector with the inverse challenge. -/
def foldB {n : ℕ} (x : F) (b : Vec F (n + n)) : Vec F n := low b + x⁻¹ • high b

/-- Fold the first generator vector in the dual direction to `foldA`. -/
def foldGs {n : ℕ} (x : F) (gs : Fin (n + n) → G) : Fin n → G :=
  low gs + x⁻¹ • high gs

/-- Fold the second generator vector in the dual direction to `foldB`. -/
def foldHs {n : ℕ} (x : F) (hs : Fin (n + n) → G) : Fin n → G :=
  low hs + x • high hs

/-- The verifier's update of the public inner-product commitment. -/
def foldCommitment (x : F) (p l r : G) : G := p + x⁻¹ • l + x • r

/-- Expanding a folded multiexponentiation produces the diagonal terms and
the two cross terms, with the expected powers of the challenge. -/
theorem combine_foldA_foldGs {n : ℕ} (x : F) (hx : x ≠ 0)
    (a : Vec F (n + n)) (gs : Fin (n + n) → G) :
    combine (foldA x a) (foldGs x gs) =
      combine (low a) (low gs) + combine (high a) (high gs) +
        x⁻¹ • combine (low a) (high gs) + x • combine (high a) (low gs) := by
  simp only [foldA, foldGs, combine_add_left, combine_add_right,
    combine_smul_left, combine_smul_right, smul_add, smul_smul,
    inv_mul_cancel₀ hx, one_smul]
  abel

/-- The same expansion for the other vector-generator pair. -/
theorem combine_foldB_foldHs {n : ℕ} (x : F) (hx : x ≠ 0)
    (b : Vec F (n + n)) (hs : Fin (n + n) → G) :
    combine (foldB x b) (foldHs x hs) =
      combine (low b) (low hs) + combine (high b) (high hs) +
        x • combine (low b) (high hs) + x⁻¹ • combine (high b) (low hs) := by
  simp only [foldB, foldHs, combine_add_left, combine_add_right,
    combine_smul_left, combine_smul_right, smul_add, smul_smul,
    mul_inv_cancel₀ hx, one_smul]
  abel

/-- The inner product transforms with the same cross terms. -/
theorem inner_fold {n : ℕ} (x : F) (hx : x ≠ 0) (a b : Vec F (n + n)) :
    inner (foldA x a) (foldB x b) =
      inner (low a) (low b) + inner (high a) (high b) +
        x⁻¹ * inner (low a) (high b) + x * inner (high a) (low b) := by
  simp only [foldA, foldB, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  abel

/-- Correctness of one full inner-product folding round. The verifier never
sees `a` or `b`; it only computes the right side from public commitments. -/
theorem ipaCommit_fold {n : ℕ} (x : F) (hx : x ≠ 0)
    (a b : Vec F (n + n)) (gs hs : Fin (n + n) → G) (q : G) :
    ipaCommit (foldA x a) (foldB x b) (foldGs x gs) (foldHs x hs) q =
      foldCommitment x (ipaCommit a b gs hs q) (crossL a b gs hs q)
        (crossR a b gs hs q) := by
  rw [ipaCommit, combine_foldA_foldGs x hx, combine_foldB_foldHs x hx, inner_fold x hx,
    foldCommitment, ipaCommit, crossL, crossR, combine_split a gs,
    combine_split b hs, inner_split a b]
  module

-- Why this is sound. At a generic challenge the cross terms cannot be chosen
-- to repair an incorrect inner product after the fact. A formal extractor
-- rewinds the prover to obtain several accepting transcripts with different
-- challenges, then solves for openings of all cross commitments. Repeating
-- this extraction at every round produces an opening of the original claim.
-- That rewinding argument, and its concrete soundness probability, are outside
-- this algebraic development.

-- ============================================================================
-- Section 5: A computed four-coordinate inner-product proof
-- ============================================================================

section Demo

notation "𝔽₁₀₁" => ZMod 101

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- Four little-endian bits represent 13 = 1 + 4 + 8. -/
def demoBits : Fin 4 → ℕ := ![1, 0, 1, 1]

example : bitValue demoBits = 13 := by decide
example : bitValue demoBits < 2 ^ 4 := bitValue_lt demoBits (by decide)
example : (bitValue demoBits : 𝔽₁₀₁) = 13 := by decide
example : ∀ i, bitConstraint (demoBits i : 𝔽₁₀₁) = 0 := by decide

/-- The range identity at challenges y = 3 and z = 5. -/
example :
    inner (rangeLeft (fun i => (demoBits i : 𝔽₁₀₁)) 5)
      (rangeRight (complement (fun i => (demoBits i : 𝔽₁₀₁))) 3 5) =
    5 ^ 2 * inner (fun i => (demoBits i : 𝔽₁₀₁)) (twoPowers 4) +
      rangeOffset 4 3 5 := by decide

/-- A Pedersen commitment in the toy additive group. -/
example : commit (2 : 𝔽₁₀₁) (7 : 𝔽₁₀₁) (13 : 𝔽₁₀₁) (9 : 𝔽₁₀₁) = 89 := by decide

/-- Homomorphism: commitments to 13 and 7 add to a commitment to 20. -/
example :
    commit (2 : 𝔽₁₀₁) (7 : 𝔽₁₀₁) (13 + 7 : 𝔽₁₀₁) (9 + 4 : 𝔽₁₀₁) =
      commit 2 7 (13 : 𝔽₁₀₁) 9 + commit 2 7 (7 : 𝔽₁₀₁) 4 := by decide

/-- Initial secret vectors. -/
def a0 : Vec 𝔽₁₀₁ (2 + 2) := ![3, 5, 2, 7]

/-- The second secret vector. -/
def b0 : Vec 𝔽₁₀₁ (2 + 2) := ![1, 4, 6, 2]

/-- Public generators for `a0`. -/
def gs0 : Fin (2 + 2) → 𝔽₁₀₁ := ![2, 3, 5, 7]

/-- Public generators for `b0`. -/
def hs0 : Fin (2 + 2) → 𝔽₁₀₁ := ![11, 13, 17, 19]

/-- The generator carrying the inner-product term. -/
def q0 : 𝔽₁₀₁ := 23

/-- The original statement. -/
def p0 : 𝔽₁₀₁ := ipaCommit a0 b0 gs0 hs0 q0

/-- First-round cross commitments. -/
def l1 : 𝔽₁₀₁ := crossL a0 b0 gs0 hs0 q0

/-- The other first-round cross commitment. -/
def r1 : 𝔽₁₀₁ := crossR a0 b0 gs0 hs0 q0

/-- First verifier challenge. -/
def x1 : 𝔽₁₀₁ := 3

/-- Vectors and generators after folding four coordinates to two. -/
def a1 : Vec 𝔽₁₀₁ (1 + 1) := foldA x1 a0

/-- The folded second vector. -/
def b1 : Vec 𝔽₁₀₁ (1 + 1) := foldB x1 b0

/-- The folded first generators. -/
def gs1 : Fin (1 + 1) → 𝔽₁₀₁ := foldGs x1 gs0

/-- The folded second generators. -/
def hs1 : Fin (1 + 1) → 𝔽₁₀₁ := foldHs x1 hs0

/-- The verifier's first-round statement update. -/
def p1 : 𝔽₁₀₁ := foldCommitment x1 p0 l1 r1

example : ipaCommit a1 b1 gs1 hs1 q0 = p1 :=
  ipaCommit_fold x1 (by decide) a0 b0 gs0 hs0 q0
example : ipaCommit a1 b1 gs1 hs1 q0 = p1 := by native_decide

/-- Second-round cross commitments. -/
def l2 : 𝔽₁₀₁ := crossL a1 b1 gs1 hs1 q0

/-- The other second-round cross commitment. -/
def r2 : 𝔽₁₀₁ := crossR a1 b1 gs1 hs1 q0

/-- Second verifier challenge. -/
def x2 : 𝔽₁₀₁ := 5

/-- The final one-coordinate vectors. -/
def a2 : Vec 𝔽₁₀₁ 1 := foldA x2 a1

/-- The final second vector. -/
def b2 : Vec 𝔽₁₀₁ 1 := foldB x2 b1

/-- The final first generator. -/
def gs2 : Fin 1 → 𝔽₁₀₁ := foldGs x2 gs1

/-- The final second generator. -/
def hs2 : Fin 1 → 𝔽₁₀₁ := foldHs x2 hs1

/-- The verifier's final statement update. -/
def p2 : 𝔽₁₀₁ := foldCommitment x2 p1 l2 r2

/-- Two folds reduce the original claim to a check on four public group
elements and two final scalars. The verifier also derives `gs2` and `hs2`
from the original public generators and the challenges. -/
example : ipaCommit a2 b2 gs2 hs2 q0 = p2 := by native_decide

/-- Adding one to the final `a` response breaks verification. -/
example : ipaCommit (a2 + 1) b2 gs2 hs2 q0 ≠ p2 := by native_decide

end Demo

-- ============================================================================
-- Section 6: Sizes, security, and scope
-- ============================================================================

/-- Group elements sent by the bare inner-product argument after `k` folds. -/
def ipaGroupElements (k : ℕ) : ℕ := 2 * k

/-- Scalars sent at the end of the bare inner-product argument. -/
def ipaFinalScalars : ℕ := 2

/-- A single range proof adds the vector commitments A,S and coefficient
commitments T1,T2 to the `2·log₂(n)` inner-product cross commitments. -/
def rangeGroupElements (k : ℕ) : ℕ := 2 * k + 4

/-- The usual final scalar responses are `tHat`, `tauX`, `mu`, `a`, and `b`. -/
def rangeFinalScalars : ℕ := 5

example : ipaGroupElements 2 = 4 := by decide
example : rangeGroupElements 2 = 8 := by decide
example : rangeGroupElements 6 = 16 := by decide  -- one 64-bit range
example : rangeFinalScalars = 5 := by decide

-- Verification is linear, even though communication is logarithmic. The
-- verifier must combine the original n pairs of generators using all round
-- challenges to obtain the final generators. Fast multiexponentiation makes
-- this practical but does not change that asymptotic cost.
--
-- A full range proof wraps the inner-product argument in these messages:
--
--   1. Commit to aL,aR with A, and to blinding vectors sL,sR with S.
--   2. Receive y,z and form the polynomials l(X),r(X) from §2.
--   3. Commit to t1,t2 with T1,T2, receive x, and reveal tHat = t(x)
--      together with the blinding responses tauX and mu.
--   4. Check tHat against V,T1,T2 and the public offset rangeOffset.
--   5. Run the inner-product argument for l(x),r(x), using generators for
--      the right vector rescaled by y⁻ⁱ to absorb the Hadamard product.
--
-- Aggregating m range proofs uses vectors of length m·n, so the inner-product
-- part still grows logarithmically. The same argument also proves arithmetic
-- circuit satisfaction by encoding multiplication gates as inner products.
--
-- Security assumptions not supplied by the algebra:
--   * binding needs a prime-order group with no efficiently computable
--     discrete-log relation among the independently generated bases;
--   * hiding needs uniform, independent blinding factors; the blinding vectors
--     and responses also hide the witness in evaluations and final scalars;
--   * soundness needs unpredictable nonzero challenges and a rewinding
--     extraction argument;
--   * a noninteractive deployment derives all challenges with Fiat-Shamir,
--     hashing the statement and every preceding transcript message.
--
-- The implementation of random sampling, hash-to-curve generator derivation,
-- Fiat-Shamir, and the full probabilistic soundness proof is intentionally
-- absent. The executable example demonstrates only the verification algebra.

end Bulletproofs
