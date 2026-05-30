# Octra PVAC-HFHE — Formalization Roadmap

A layered plan for understanding and formalizing Octra's **PVAC-HFHE**
("publicly verifiable arithmetic computations with hypergraph-based homomorphic
encryption") in Lean. Reference C++ PoC: <https://github.com/octra-labs/pvac_hfhe_cpp>.

> **Status legend:** ✓ done · ◐ partial · ▢ stub/todo

## What the system actually is (and why hypergraphs, not just Paillier)

Paillier is **additively** homomorphic and rests on **factoring** (not
post-quantum). Octra's scheme needs three things Paillier can't give:

1. **Full arithmetic** — `ct_add`, `ct_sub`, **`ct_mul`** → arbitrary circuits (FHE).
2. **A post-quantum hardness assumption** — *binary parity with noise* (**LPN**) /
   **syndrome decoding**, not factoring.
3. **Tunable, provable hardness** — a **random k-uniform hypergraph** builds the
   syndrome (parity-check) structure; random-hypergraph **threshold** and
   **fractional-colorability** results (MIPT) place the decoding instance in the
   hard regime.

So the hypergraph is the **hardness substrate**, not a data structure. Paillier
([Crypto/Paillier.lean](Crypto/Paillier.lean)) is kept as a *warmup* that teaches
the discipline we reuse everywhere: **prove correctness as algebra, axiomatize
hardness, state security as a reduction.**

Arithmetic is over the Mersenne prime field 𝔽_p, **p = 2¹²⁷ − 1**.

## The five layers (bottom-up)

```
  PVAC: publicly verifiable proofs                         ← Phase 5
  ─────────────────────────────────────────────
  Logic gates / circuits on ciphertexts                    ← Phase 4 (started)
  ─────────────────────────────────────────────
  HFHE: enc/dec, ct_add/sub/mul, correctness + noise       ← Phase 3   (keystone)
  ─────────────────────────────────────────────
  ARITHMETIC TRACK              │ HARDNESS TRACK
  𝔽_p (p=2¹²⁷−1), Paillier ✓   │ LPN / syndrome decoding   ← Phase 2
  ─────────────────────────────────────────────
                                  linear codes / parity     ← Phase 1b
  ─────────────────────────────────────────────
  random k-uniform hypergraphs: incidence, syndrome map,    ← Phase 1
  thresholds, fractional colorability  (Hypergraphs/Basic ✓)
```

The two middle tracks are **independent** until they meet at Phase 3 — work them
in either order or in parallel.

## File hierarchy

```
Hypergraphs/
  Basic.lean          ✓ structure, incidence relation
  LogicGates.lean     ✓ boolean gates
  Random.lean         ▢ random k-uniform model: edge prob, H(n,m,k)
  Incidence.lean      ◐ incidence matrix M ∈ 𝔽_q^{m×n}; bridge to codes
  Threshold.lean      ▢ threshold / fractional-chromatic STATEMENTS (MIPT)

Coding/                NEW — coding theory (the hardness substrate)
  LinearCode.lean     ◐ parity-check matrix, syndrome σ = H·x, Hamming weight
  Syndrome.lean       ▢ syndrome map from a hypergraph; syndrome-decoding problem
  LPN.lean            ▢ Learning Parity with Noise: distribution + hardness AXIOM

Crypto/
  Rsa.lean            ✓ additive warmup / Euler discipline
  Paillier.lean       ✓ additive HE warmup (algebra proven, kernel deferred)
  Field127.lean       ◐ 𝔽_p, p = 2¹²⁷−1 (Mersenne) field + lemmas
  HFHE/                NEW — the scheme
    Defs.lean         ▢ keygen / encrypt / decrypt over the syndrome structure
    Noise.lean        ▢ noise measure + the "budget" invariant
    Correctness.lean  ▢ Dec(Enc m) = m  under a noise bound
    Homomorphism.lean ▢ ct_add / ct_sub / ct_mul correctness
    Security.lean     ▢ IND-CPA ⟸ LPN  (a reduction, conditional theorem)
  PVAC/                NEW — verifiability (last)
    Statement.lean    ▢ what "y = f(cts)" claims; soundness/completeness specs
    Verify.lean       ▢ the verifier + its correctness
```

## Phases

### Phase 0 — Pin the spec (do first)
Read the C++; write `Crypto/HFHE/SPEC.md` answering: secret key? public key? how
does `encrypt` mix plaintext with a hypergraph syndrome? what does `ct_mul` do to
noise (relinearization/bootstrapping)? where does 𝔽_p sit vs the binary parity
noise? Every Phase-3 Lean signature follows from these answers — don't formalize a
guess.

### Phase 1 — Hypergraph foundation
- **Learn:** incidence matrix; random k-uniform models H(n,p)/H(n,m,k); threshold
  phenomena; fractional chromatic number (MIPT: Shabanov, Raigorodskii, …).
- **Build:** `Incidence.lean` (incidence matrix + syndrome map — **keystone #1**);
  `Random.lean`, `Threshold.lean` (state threshold theorems, cite/axiomatize).
- **Mathlib:** `LinearAlgebra.Matrix`, `Combinatorics.*`, `Probability.*`.

### Phase 1b / 2 — Coding + LPN (hardness track)
- **Learn:** linear codes, parity-check `H`, syndrome `σ = H·x`; syndrome decoding
  (NP-hard / hard on random instances); LPN and its duality with syndrome decoding.
- **Build:** `LinearCode.lean` (syndrome, weight, linearity); `Syndrome.lean`
  (`H := incidence` — hypergraph *becomes* the code); `LPN.lean` (`axiom LPN_hard`).
- **Mathlib:** `Matrix.mulVec`, `ZMod`, `LinearAlgebra.*`.

### Phase 1a — 𝔽_p + Paillier (arithmetic track, parallel)
- **Build:** `Field127.lean` (`Fact (Nat.Prime (2¹²⁷−1))` via Lucas–Lehmer, field
  set-up). `Paillier.lean` ✓ already done — the homomorphism-discipline reference.

### Phase 3 — The HFHE scheme (tracks meet — keystone)
Reuse the Paillier discipline. Build in order:
1. `Defs.lean` — `KeyPair`, `encrypt pk m noise`, `decrypt sk c` (noise explicit, no RNG).
2. `Noise.lean` — noise measure + budget invariant `noise(ct) < β`.
3. `Correctness.lean` — `decrypt sk (encrypt pk m e) = m` when `noise e < β` (**keystone #2**).
4. `Homomorphism.lean` — `Dec(c₁∘c₂) = m₁∘m₂` for ∘∈{+,−,×}; `ct_mul` grows noise (**keystone #3**).
5. `Security.lean` — `LPN_hard → IND_CPA` (**keystone #4**, a reduction).

### Phase 4 — Circuits / logic gates on ciphertexts
Reframe [LogicGates.lean](Hypergraphs/LogicGates.lean): `ct_add`=XOR, `ct_mul`=AND ⇒
functional completeness. Prove each gate's truth-table semantics *under
encryption* with a **depth bound** from the noise budget. Corollary of Phase 3.

### Phase 5 — PVAC (publicly verifiable), last
`PVAC/Statement.lean` (specs as `Prop`), `PVAC/Verify.lean` (verifier +
soundness/completeness). Most spec-dependent; do once the scheme is solid.

## The five keystone theorems (the joints)

| # | Theorem | Joins | Target |
|---|---------|-------|--------|
| 1 | `incidence` is a parity-check matrix (syndrome linear) | Hypergraph → Coding | **proven** |
| 2 | `decrypt (encrypt m e) = m` (noise `< β`) | 𝔽_p + Syndrome → Scheme | **proven** (algebra) |
| 3 | `Dec(c₁∘c₂) = m₁∘m₂`, ∘∈{+,−,×} | Scheme → Circuits | **proven** (+ noise bound) |
| 4 | `LPN_hard → IND_CPA` | LPN → Scheme | **conditional** (reduction) |
| 5 | random `H` at MIPT params ⟹ decoding hard | Threshold → LPN | **axiom/cited** |

**Discipline:** correctness ⇒ fully proved; hardness ⇒ axiomatized + cited;
security ⇒ a reduction to the axioms. This is how cryptography is formalized.

## Recommended first three steps
1. Phase 0: write `Crypto/HFHE/SPEC.md` from the C++.
2. Phase 1: flesh `Hypergraphs/Incidence.lean` (keystone #1) — small, builds on `Basic`.
3. Phase 1a: flesh `Crypto/Field127.lean` — independent, unblocks Phase-3 arithmetic.
