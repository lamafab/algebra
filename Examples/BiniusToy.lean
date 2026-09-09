import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Algebra.Ring.Multilinear
import Crypto.ZK.BinaryFRI

open MvPolynomial
open BinaryFRI

-- ============================================================================
-- End-to-end toy: proving one AND-gate evaluation
-- ============================================================================
--
-- The smallest complete run of the Binius pipeline (Binius.lean, header).
-- One claim, walked through every station. Nothing here is new mathematics;
-- each step is one checked example that instantiates a theorem from the
-- component files, so the file reads as the wiring diagram between them.
--
-- The agreed-upon system (public input):
--   the circuit f(x₀, x₁) = x₀ · x₁ over 𝔽₂   — an AND gate
-- The claim (public):
--   the hypercube sum of f's MLE is 1          — "f has a satisfying input"
-- The witness (prover's private input):
--   the satisfying assignment w = (1, 1)
--
--   Step 0  the claim, as an arithmetic statement
--   Step 1  commit: MLE table → Merkle root
--   Step 2  sumcheck: the sum reduces to one evaluation p̃(r) = v
--   Step 3  open: the verifier checks the committed value at r
--
-- Toy sizes throughout: the "hash" is addition mod 2 (not binding, just
-- exercising the arithmetic), the challenges are 𝔽₂ points, and there is
-- no RS stretching. The soundness terms (sumcheck n·2⁻ᵏ, FRI distance,
-- Merkle binding) are what scale this up; see Binius.lean §5.

namespace Examples.BiniusToy

-- ============================================================================
-- Step 0: The claim
-- ============================================================================
--
-- "AND is satisfiable" arithmetized: the MLE of the circuit, summed over the
-- hypercube, counts satisfying assignments. The claimed sum is C = 1.

/-- The system: a two-input AND gate. -/
def circuit (v : Fin 2 → ZMod 2) : ZMod 2 := v 0 * v 1

-- The truth table, as a sanity check.
example : circuit ![0, 0] = 0 := by decide
example : circuit ![0, 1] = 0 := by decide
example : circuit ![1, 0] = 0 := by decide
example : circuit ![1, 1] = 1 := by decide

/-- The witness: x₀ = 1, x₁ = 1 satisfies the gate. -/
example : circuit ![1, 1] = 1 := by decide

/-- The arithmetized claim: the hypercube sum of the circuit's MLE is 1.
Only (1,1) contributes (Multilinear.lean; Sumcheck.lean §1). -/
example : ∑ v : Fin 2 → ZMod 2, eval v (mle circuit) = 1 := by
  simp only [eval_mle]
  decide

-- ============================================================================
-- Step 1: The prover commits
-- ============================================================================
--
-- Before any challenge exists, the prover fixes the object the proof is
-- about: it evaluates the MLE on the hypercube (off-chain, so the tree
-- holds literal values), lays the four values into a Merkle tree, and
-- publishes the root. Binding (idealized here) means that after this point
-- there is exactly one value the prover can present at each leaf position.

/-- The committed table: the circuit's truth table, leaf order
(0,0)=0, (0,1)=0, (1,0)=0, (1,1)=1.

        root = 1
       /        \
      0          1
     / \        / \
    0   0      0   1
   —————————————————
   00  01     10  11   ← leaf corners (x₀, x₁)

Internal nodes hold toyHash of their children (addition mod 2), so the
root is the leaf parity. -/
def table : BinaryFRI.Tree (ZMod 2) :=
  .node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))

/-- The toy compression function: addition mod 2. -/
def toyHash : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => a + b

/-- The published root. With h = addition it is the leaf parity: 1. -/
example : table.root toyHash = 1 := by decide

/-- The commitment is honestly formed: each leaf equals the MLE at its
corner. This is what ties the tree to the circuit (eval_mle). -/
example : table.lookup [true,  true]  = some (eval ![0, 0] (mle circuit)) := by
  rw [eval_mle]; decide
example : table.lookup [true,  false] = some (eval ![0, 1] (mle circuit)) := by
  rw [eval_mle]; decide
example : table.lookup [false, true]  = some (eval ![1, 0] (mle circuit)) := by
  rw [eval_mle]; decide
example : table.lookup [false, false] = some (eval ![1, 1] (mle circuit)) := by
  rw [eval_mle]; decide

-- ============================================================================
-- Step 2: Sumcheck reduces the claim to one evaluation
-- ============================================================================
--
-- The verifier cannot sum 2ⁿ terms itself. Sumcheck (Sumcheck.lean §1)
-- replaces the claim "sum = 1" by "p̃(r) = v" at one random point, one
-- variable per round. Round 1 groups the corners by x₀; the verifier
-- checks the two slices sum to C, then fixes x₀ := r₀.

/-- Round 1 consistency: the x₀ = 0 slice and the x₀ = 1 slice sum to the
claimed C = 1. -/
example :
    (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 0}, eval v.1 (mle circuit)) +
    (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 1}, eval v.1 (mle circuit)) = 1 := by
  simp only [eval_mle]
  decide

/-- The honest slice values: g₀(0) = 0 and g₀(1) = 1. -/
example : (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 0}, eval v.1 (mle circuit)) = 0 := by
  simp only [eval_mle]; decide
example : (∑ v : {w : Fin 2 → ZMod 2 // w 0 = 1}, eval v.1 (mle circuit)) = 1 := by
  simp only [eval_mle]; decide

/-- The verifier samples r₀ = 1. Round 2's claim is now about p̃(1, x₁):
the one-variable slice containing the witness. Its two values must sum to
g₀(1) = 1. -/
example : eval ![1, 0] (mle circuit) + eval ![1, 1] (mle circuit) = 1 := by
  simp only [eval_mle]; decide

/-- The verifier samples r₁ = 1. The reduction is complete: the sum claim
has become the single evaluation claim p̃(1, 1) = 1, with v = 1. -/
example : eval ![1, 1] (mle circuit) = 1 := by rw [eval_mle]; decide

-- ============================================================================
-- Step 3: The verifier opens the commitment at r = (1, 1)
-- ============================================================================
--
-- Sumcheck's final line needs the value of the committed table at r, from a
-- prover the verifier does not trust. The prover reveals the leaf and its
-- authentication path; the verifier folds the path and compares against
-- the root from Step 1 (verify_path, BinaryFRI.lean §3).

/-- The prover's opening for r = (1, 1): the leaf value and the path
(sibling hashes, leaf-to-root). With h = addition the siblings are both 0. -/
def opening : ZMod 2 × BinaryFRI.Path (ZMod 2) := (1, [(false, 0), (false, 0)])

/-- The verifier's final check: the opened value is the v that sumcheck
produced, and the path reconstructs the committed root. The second
conjunct is the honest-run case of verify_path. -/
example : opening.1 = 1 ∧ verify toyHash opening.1 opening.2 = table.root toyHash :=
  ⟨by decide, by decide⟩

/-- The opened value is not arbitrary: it is the MLE at r (eval_mle),
so the table the verifier read is the polynomial sumcheck reasoned about. -/
example : opening.1 = eval ![1, 1] (mle circuit) := by rw [eval_mle]; decide

/-- The closing picture: one leaf of a four-leaf tree carried the entire
claim. Scaling replaces `decide` arithmetic by the three soundness terms
(Binius.lean §5); the shape of the run is exactly this one. -/
example : table.lookup [false, false] = some opening.1 := by decide

end Examples.BiniusToy
