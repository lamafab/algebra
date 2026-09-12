import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Algebra.Ring.Multilinear
import Crypto.ZK.BinaryFRI

open MvPolynomial
open BinaryFRI

-- ============================================================================
-- Binius: a full binary-field argument for a boolean circuit
-- ============================================================================
--
-- TODO: Slim this file to the architecture (the pipeline diagram, the
-- interface facts, and the §5 soundness budget) and let the worked run live
-- in Examples/BiniusToy.lean, which already carries one claim through every
-- station. Sections 1-4 here duplicate that toy; replace them with pointers
-- so each execution detail exists in exactly one place.
--
-- The pipeline that turns "this boolean circuit is satisfied" into a proof:
--
--   circuit f : {0,1}ⁿ → 𝔽₂
--     │  MLE (Multilinear.lean): the unique multilinear polynomial
--     │  matching f on the whole hypercube
--     ▼
--   sumcheck (Sumcheck.lean): a claim about all 2ⁿ gate evaluations
--     │  reduces, round by round, to one evaluation claim p̃(r) = v
--     ▼
--   polynomial commitment (BinaryFRI.lean): the MLE table is RS-encoded
--     │  over GF(2ᵏ), Merkle-committed, and proximity-tested by additive
--     │  folding; the verifier opens the committed table at r
--
-- Note on that step: the MLE is multivariate, FRI needs a univariate
-- polynomial, so "RS-encoded" includes a conversion: embed the hypercube
-- as an 𝔽₂-subspace of GF(2ⁿ) by an 𝔽₂-basis choice, interpret the MLE
-- table as values of a univariate function on that subspace, and
-- interpolate (RootsInterpolation.lean) to the degree-< 2ⁿ polynomial.
-- That embedding is currently comment-level only (BinaryFRI.lean §2's
-- header has the same note); formalizing it is the open gap here.
--     ▼
--   verifier accepts iff the opened value equals v
--
-- Soundness is the sum of three terms (union bound):
--   sumcheck:  n·2⁻ᵏ      per-round Schwartz-Zippel over the extension field
--   FRI:       per-query fold consistency against the code distance
--   Merkle:    binding of h, the random-oracle assumption (idealized)
--
-- Prerequisites: Multilinear.lean (Step 2), ReedSolomonReedMuller.lean
-- (Step 3), Sumcheck.lean (Step 4), BinaryFRI.lean (Step 5).
--
--   §1  A small boolean circuit
--   §2  Its multilinear extension
--   §3  The sumcheck reduction
--   §4  The commitment and a toy end-to-end opening
--   §5  The composed argument, with its soundness budget
-- ============================================================================

namespace Binius

-- ============================================================================
-- Section 1: A small boolean circuit
-- ============================================================================
--
-- The running example is a single AND gate. Over 𝔽₂, AND is multiplication
-- (BinaryFields.lean §1), so the circuit is already an arithmetic circuit.

/-- The circuit: a two-input AND, as a function on the hypercube. -/
def andCircuit (v : Fin 2 → ZMod 2) : ZMod 2 := v 0 * v 1

-- The truth table, as a sanity check.
example : andCircuit ![0, 0] = 0 := by decide
example : andCircuit ![0, 1] = 0 := by decide
example : andCircuit ![1, 0] = 0 := by decide
example : andCircuit ![1, 1] = 1 := by decide

-- ============================================================================
-- Section 2: Its multilinear extension
-- ============================================================================
--
-- The MLE of the AND truth table is the polynomial x₀·x₁: multilinear, and
-- equal to the circuit on all four corners of the square (Multilinear.lean,
-- header and §3).

-- The MLE agrees with the circuit at every hypercube point.
example (w : Fin 2 → ZMod 2) : eval w (mle andCircuit) = andCircuit w :=
  eval_mle _ _

-- The four corners, concretely.
example : eval ![0, 0] (mle andCircuit) = 0 := by rw [eval_mle]; decide
example : eval ![0, 1] (mle andCircuit) = 0 := by rw [eval_mle]; decide
example : eval ![1, 0] (mle andCircuit) = 0 := by rw [eval_mle]; decide
example : eval ![1, 1] (mle andCircuit) = 1 := by rw [eval_mle]; decide

-- The MLE is multilinear: degree at most 1 in each variable. This is what
-- keeps every sumcheck round's univariate claim to degree 1.
example : IsMultilinear (mle andCircuit) := isMultilinear_mle andCircuit

-- ============================================================================
-- Section 3: The sumcheck reduction
-- ============================================================================
--
-- A gate-satisfaction claim over the whole hypercube is a hypercube sum:
-- for the AND gate, the sum of its MLE over {0,1}² counts the satisfying
-- assignments (one: the point (1,1)). Sumcheck lets the verifier check such
-- a claim without summing 2ⁿ terms itself; after 2 rounds it only needs the
-- MLE at one random point r ∈ GF(2ᵏ)².

-- The hypercube sum of the AND circuit is 1.
example : ∑ w : Fin 2 → ZMod 2, eval w (mle andCircuit) = 1 := by
  simp only [eval_mle]
  decide

-- ============================================================================
-- Section 4: The commitment and a toy end-to-end opening
-- ============================================================================
--
-- To answer the final evaluation claim, the prover must have committed to the
-- MLE before seeing the challenges. The commitment is the Merkle root of the
-- RS encoding of the evaluation table (BinaryFRI.lean §2). Toy instance over
-- 𝔽₂ with h = addition: not binding, only exercising the arithmetic.

-- The AND truth table [0, 0, 0, 1] committed as a 4-leaf tree.
example :
    let h : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => a + b
    let t : BinaryFRI.Tree (ZMod 2) := .node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1))
    -- the leaf at (1,1) is 1, and its path opens correctly against the root
    t.lookup [false, false] = some 1 ∧
      verify h 1 [(false, 0), (false, 0)] = t.root h := by
  exact ⟨by decide, by decide⟩

-- ============================================================================
-- Section 5: The composed argument
-- ============================================================================
--
-- The full proof for a circuit f, restated:
--
--   1. The prover commits to the MLE table of f (Merkle root of the RS
--      encoding over GF(2ᵏ)).
--   2. The satisfaction claim, written as a hypercube sum, is reduced by
--      sumcheck to one evaluation claim: MLE(r) = v for a random r.
--   3. The verifier opens the commitment at r (Merkle path + fold-consistency
--      checks along the FRI layers) and accepts iff the opened value is v.
--
-- A cheating prover must either break sumcheck (n·2⁻ᵏ per round, Step 4),
-- or commit to a word far from every codeword and survive the FRI queries
-- (per-query probability from the code distance, Step 5), or break the Merkle
-- binding (random-oracle assumption, idealized). For the real system every
-- constant is tuned so the total stays below 2⁻¹²⁸; here the point is only
-- that each term is one of the pieces built in Steps 2-5.

#check @eval_mle
#check @isMultilinear_mle
#check @MvPolynomial.schwartz_zippel_totalDegree
#check @rsEncode_injective
#check @foldMap_pair
#check @verify_path

end Binius
