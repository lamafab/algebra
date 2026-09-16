import Mathlib.Tactic
import Algebra.Field.G8

-- ============================================================================
-- Binary FRI, end to end on a real codeword
-- ============================================================================
--
-- Companion to Examples/Sumcheck.lean: a self-contained micro-run of binary
-- FRI (Crypto/ZK/BinaryFRI.lean) over GF(8) (Algebra/Field/G8.lean). The
-- committed word is a genuine Reed-Solomon codeword of a message
-- polynomial, and two fold rounds take it down to a constant.
--
--   §1  The claim: the message and its RS codeword
--   §2  The fold map and its fibers
--   §3  Round 1: folding the codeword
--   §4  Round 2: folding to a constant
--
-- The run (the prover computes every word; the verifier only samples
-- challenges and spot-checks):
--
--   claim:      word₀ is the table of a degree < 4 polynomial on L
--   round 1:    verifier sends r₀ = 1; prover folds word₀ → word₁ on q(L)
--               check: foldW α r₀ word₀ x = word₁ (qmap α x), any fiber
--   round 2:    verifier sends r₁ = α; prover folds word₁ → a constant
--               check: foldW (α+1) r₁ word₁ y = const, any fiber
--   final:      the last word is the constant α
--
-- In the real protocol each word is committed as a Merkle root before the
-- next challenge is revealed (Crypto/Merkle.lean), and the checks run on a
-- few random fibers; here the words are computed outright and everything
-- is checked on all fibers by decide. The fold map and folded word are
-- redefined locally (two lines each) because instantiating BinaryFRI's
-- Field-polymorphic definitions would need a Field instance on G8.

namespace Examples.BinaryFRI

open G8

-- ============================================================================
-- Section 1: The claim, as an RS codeword
-- ============================================================================
--
-- The message is the degree-3 polynomial m(X) = X³ + X + 1 over GF(8). Its
-- Reed-Solomon codeword is the evaluation table on the full domain
-- L = GF(8) (ReedSolomonReedMuller.lean §1, written here as a function
-- rather than a Polynomial so everything stays decidable).

/-- The message polynomial m(X) = X³ + X + 1. -/
def m : G8 → G8 := fun x => x * x * x + x + 1

/-- The evaluation domain: all of GF(8), ordered
0, 1, α, α+1, α², α²+1, α²+α, α²+α+1. -/
def L : List G8 := [0, 1, α, α + 1, α², α² + 1, α² + α, α² + α + 1]

/-- Word 0 of the fold chain: evaluations of m on L. -/
def word₀ : G8 → G8 := m

-- The codeword really is the evaluation table of the message. The three
-- zeros sit at α, α², α²+α = α⁴: exactly the roots of m, since m is the
-- minimal polynomial of α over GF(2).
example : L.map word₀ = [1, 1, 0, α² + α, 0, α, 0, α²] := by decide

-- TODO: Briefly clarify the notation of RS [..]
--
-- Distance, concretely. With deg m = 3 and |L| = 8 the code is
-- RS [8, 4, 5]: rate 1/2, and two distinct codewords agree in at most
-- n − d = 3 positions.
--
-- The bound is tight: z(X) = (α+1)X² + (α+1)X + 1 agrees with m in exactly
-- 3 positions, since the difference m − z = X(X+1)(X+α) vanishes exactly
-- at {0, 1, α} (rs_agreement_card_le in ReedSolomonReedMuller.lean).
def z : G8 → G8 := fun x => (α + 1) * x * x + (α + 1) * x + 1

example : m != z := by decide
example : (L.filter fun x => word₀ x = z x) = [0, 1, α] := by decide
example : (L.filter fun x => word₀ x ≠ z x).length = 5 := by decide

-- ============================================================================
-- Section 2: The fold map and its fibers
-- ============================================================================
--
-- NOTE: `def qmap` is Binius specific, ie. enabling a 2-to-1 Frobenius map for
-- characteristic 2 fields.
--
-- The fold map q(x) = x² + β·x with any nonzero β (foldMap in BinaryFRI.lean
-- §1, redefined locally). Round 1 takes β₀ = α: the kernel is {0, α}, so it
-- pairs each x with x + α and halves the 8-element domain to the 4-element
-- image {0, α+1, α²+1, α²+α}.

/-- The additive fold map, local copy. Round i of the fold chain uses its
own βᵢ (FoldChain in BinaryFRI.lean §1c); round 1 below has β₀ = α. -/
def qmap (β x : G8) : G8 := x * x + β * x

-- The kernel is exactly {0, α}: q vanishes only at 0 and α.
example : ∀ x : G8, qmap α x = 0 ↔ x = 0 ∨ x = α := by decide

-- The 2-to-1 collapse: q(x + α) = q(x) for every x (foldMap_pair).
example : ∀ x : G8, qmap α (x + α) = qmap α x := by decide

-- The fibers, concretely:
--   {0, α} ↦ 0          {1, α+1} ↦ α+1
--   {α², α²+α} ↦ α²+1   {α²+1, α²+α+1} ↦ α²+α
example : qmap α 0 = 0 := by decide
example : qmap α α = 0 := by decide
--
example : qmap α 1 = α + 1 := by decide
example : qmap α (α + 1) = α + 1 := by decide
--
example : qmap α α² = α² + 1 := by decide
example : qmap α (α² + α) = α² + 1 := by decide
--
example : qmap α (α² + 1) = α² + α := by decide
example : qmap α (α² + α + 1) = α² + α := by decide

-- ============================================================================
-- Section 3: Round 1, folding the codeword
-- ============================================================================
--
-- The prover's fold, as polynomial arithmetic. Divide m by q:
--
--   m = (X + α)·q + ((α² + 1)X + 1) = p₀(q) + X·p₁(q)
--
-- NOTE: (α² + 1) is an element in GF(8) and has degree 1.
--
-- The quotient and remainder are digits (degree < deg q = 2). Their
-- constant parts collect into p₀(t) = 1 + αt, their X-coefficients
-- into p₁(t) = (α² + 1) + t: the two half-degree components of the
-- fold. The general statement is exists_fold_decomp in
-- BinaryFRI.lean §1b; the digit form below is written inline.

/-- The verifier's per-fiber check, recomputed from two opened values:
the folded word's value at q(x) is p₀(y) + r·p₁(y) with slope
p₁(y) = (w(x) + w(x+β)) / β read off the fiber {x, x + β}.

(foldWord in BinaryFRI.lean §1b, redefined locally; inv β is 1/β). -/
def foldW (β r : G8) (w : G8 → G8) (x : G8) : G8 :=
  w x + (x + r) * (w x + w (x + β)) * inv β

/-- The round-1 challenge, sampled by the verifier after the commitment.
r₀ = 1 here; the chain needs it to be unpredictable, not any particular
value. -/
def r₀ : G8 := 1

-- The choice matters: a different challenge folds differently.
example : foldW α r₀ word₀ 0 = α² ∧ foldW α α word₀ 0 = 0 := by decide

-- The verifier's fold-consistency check: both representatives of each
-- fiber give the same folded value (foldWord_pair, checked on all fibers).
example : foldW α r₀ word₀ 0 = foldW α r₀ word₀ α := by decide
example : foldW α r₀ word₀ 1 = foldW α r₀ word₀ (α + 1) := by decide
example : foldW α r₀ word₀ α² = foldW α r₀ word₀ (α² + α) := by decide
example : foldW α r₀ word₀ (α² + 1) = foldW α r₀ word₀ (α² + α + 1) := by decide

-- The verifier's fiber-local computation agrees with the prover's fold
-- at every point and every challenge: p₀(y) + r·p₁(y) with the fiber
-- coordinate replaced by r.
example : ∀ r x : G8, foldW α r word₀ x =
    (1 + α * qmap α x) + r * ((α² + 1) + qmap α x) := by decide

-- Round 1's output on the image {0, α+1, α²+1, α²+α}: with r₀ = 1 the
-- fold is p₀(t) + r₀·p₁(t) = α² + (α+1)t, the values α², 1, 0, α²+1
-- (in the order listed). The degree halved: 3 → 1.
example : foldW α r₀ word₀ 0 = α² ∧ foldW α r₀ word₀ 1 = 1 ∧
    foldW α r₀ word₀ α² = 0 ∧ foldW α r₀ word₀ (α² + 1) = α² + 1 := by decide

-- ============================================================================
-- Section 4: Round 2, folding to a constant
-- ============================================================================
--
-- Round 1's image {0, α+1, α²+1, α²+α} is the new domain. The next fold
-- needs its β₁ inside it (the fibers {y, y + β₁} must stay in the
-- domain), and α is not in the image, so β₁ = α+1.

/-- The round-2 challenge r₁ = α, chosen independently of r₀ = 1. -/
def r₁ : G8 := α
/-- The word after round 1: word₁(t) = α² + (α+1)t, the degree-1
polynomial that round 2 below folds again. -/
def word₁ : G8 → G8 := fun t => α * α + (α + 1) * t

-- word₁ really is the round-1 folded word, at every point.
example : ∀ x : G8, word₁ (qmap α x) = foldW α r₀ word₀ x := by decide

-- Round 2's fold map q₁(y) = y² + (α+1)·y: kernel {0, α+1}, fibers
-- {0, α+1} and {α²+1, α²+α}, new image the 2-element subspace {0, α+1}.
example : qmap (α + 1) 0 = 0 ∧ qmap (α + 1) (α + 1) = 0 ∧
    qmap (α + 1) (α² + 1) = α + 1 ∧ qmap (α + 1) (α² + α) = α + 1 := by decide

-- Fold-consistency on both fibers (foldWord_pair).
example : foldW (α + 1) r₁ word₁ 0 = foldW (α + 1) r₁ word₁ (α + 1) := by decide
example : foldW (α + 1) r₁ word₁ (α² + 1) =
    foldW (α + 1) r₁ word₁ (α² + α) := by decide

-- The final word: word₁ is itself a digit (degree 1 < 2), so its
-- components are the constants p₀ = α², p₁ = α+1, and the fold with
-- r₁ = α is the constant p₀ + r₁·p₁ = α. Two rounds folded degree
-- 3 → 1 → 0; the verifier reads one constant from the prover's last
-- message.
example : foldW (α + 1) r₁ word₁ 0 = α ∧
    foldW (α + 1) r₁ word₁ (α² + 1) = α := by decide

end Examples.BinaryFRI
