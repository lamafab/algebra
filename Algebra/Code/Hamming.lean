import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Matrix

namespace Hamming

-- ============================================================================
-- The [7,4,3] Hamming code over 𝔽₂
-- ============================================================================
--
-- [n, k, d] notation: n = block length (7 bits per codeword), k = dimension
-- (4 bits of message), d = minimum distance.
--
-- Minimum distance d = 3 means any two distinct codewords differ in at least
-- 3 positions. Equivalently, every nonzero codeword has Hamming weight ≥ 3.
-- This implies the code corrects up to t = ⌊(d−1)/2⌋ = 1 error.
--
-- The generator matrix G is in systematic form [I₄ | A]: the first 4
-- coordinates of a codeword are the original message. The 4×3 submatrix A
-- determines the parity bits: the parity-check matrix is H = [Aᵀ | I₃],
-- so G·Hᵀ = A + A = 0.

/-- Generator matrix G = [I₄ | A] of the [7,4,3] Hamming code. -/
def G : Matrix (Fin 4) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 1, 0;
     0, 1, 0, 0, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 0, 1]

/-- Parity-check matrix H = [Aᵀ | I₃]. Every codeword w satisfies w·Hᵀ = 0. -/
def H : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 1, 1, 0, 0;
     1, 1, 1, 0, 0, 1, 0;
     0, 1, 1, 1, 0, 0, 1]

-- Every codeword has zero syndrome.
example : G * Hᵀ = 0 := by
  native_decide

-- ============================================================================
-- Encoding
-- ============================================================================

/-- The codeword (in 𝔽₂⁷) encoding a 4-bit message. -/
def encode (m : Fin 4 → ZMod 2) : Fin 7 → ZMod 2 :=
  m ᵥ* G

-- Encode a message: the first 4 bits stay, the last 3 are parity.
example : encode ![1, 0, 1, 1] = ![1, 0, 1, 1, 1, 0, 0] := by
  native_decide

-- ============================================================================
-- Syndromes
-- ============================================================================

/-- The syndrome of a word w is the 3-bit vector w·Hᵀ. -/
def syndrome (w : Fin 7 → ZMod 2) : Fin 3 → ZMod 2 := w ᵥ* Hᵀ

-- The 7 columns of H are all 7 nonzero 3-bit vectors.
example : (fun i => H i 0) = ![1, 1, 0] := by native_decide
example : (fun i => H i 1) = ![0, 1, 1] := by native_decide
example : (fun i => H i 2) = ![1, 1, 1] := by native_decide
example : (fun i => H i 3) = ![1, 0, 1] := by native_decide
example : (fun i => H i 4) = ![1, 0, 0] := by native_decide
example : (fun i => H i 5) = ![0, 1, 0] := by native_decide
example : (fun i => H i 6) = ![0, 0, 1] := by native_decide

-- A codeword has zero syndrome.
example : syndrome (encode ![1, 0, 1, 1]) = 0 := by
  native_decide

-- If a single error flips bit j, the syndrome is column j of H.
/-- Error vector with a single 1 at position j. -/
def errorVec (j : Fin 7) : Fin 7 → ZMod 2 := Function.update 0 j 1

example : syndrome (errorVec 5) = ![0, 1, 0] := by
  native_decide

-- ============================================================================
-- Syndrome decoding
-- ============================================================================
--
-- The syndrome of a received word w = c + eⱼ (codeword + single error at j)
-- is column j of H. So the syndrome directly names the error position.

/-- Syndrome decoding: match the syndrome to a column of H to find the error,
flip that bit, then extract the first 4 coordinates (the message). -/
def decode (w : Fin 7 → ZMod 2) : Fin 4 → ZMod 2 :=
  let w' := match (List.finRange 7).find? (fun j => (fun i => H i j) = syndrome w) with
    | none => w
    | some j => Function.update w j (w j + 1)
  fun i => w' (Fin.castLE (by decide) i)

-- ============================================================================
-- Walkthrough: message → codeword → error → receive → decode
-- ============================================================================

-- Step 0: a 4-bit message.
def msg : Fin 4 → ZMod 2 := ![1, 1, 0, 0]

-- Step 1: encode it as a 7-bit codeword.
--         The first 4 bits are the message; the last 3 are parity.
def codeword : Fin 7 → ZMod 2 := encode msg
example : codeword = ![1, 1, 0, 0, 1, 0, 1] := by
  native_decide

-- Step 2: a single-bit error flips position 5.
def error : Fin 7 → ZMod 2 := errorVec 5
example : error = ![0, 0, 0, 0, 0, 1, 0] := by
  native_decide

-- Step 3: the received word is codeword + error.
--         Only bit 5 is flipped (0→1).
def received : Fin 7 → ZMod 2 := codeword + error
example : received = ![1, 1, 0, 0, 1, 1, 1] := by
  native_decide

-- Step 4: the syndrome of the received word tells us which bit is wrong.
--         Here the syndrome is ![0, 1, 0], which is column 5 of H.
example : syndrome received = ![0, 1, 0] := by
  native_decide

-- Step 5: decode flips that bit back, recovering the codeword.
example : decode received = ![1, 1, 0, 0] := by
  native_decide

-- It works for any message and any single-bit error.
example : decode (encode ![1, 0, 1, 1] + errorVec 2) = ![1, 0, 1, 1] := by
  native_decide

end Hamming
