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
  Incidence.lean      ✓ incidence matrix M ∈ 𝔽_q^{m×n}; bridge to codes (keystone #1)
  Threshold.lean      ▢ threshold / fractional-chromatic STATEMENTS (MIPT)

Coding/                NEW — coding theory (the hardness substrate)
  LinearCode.lean     ◐ parity-check matrix, syndrome σ = H·x, Hamming weight
  Syndrome.lean       ◐ syndrome map from a hypergraph; syndrome-decoding problem
  LPN.lean            ◐ Learning Parity with Noise: distribution + hardness AXIOM

Crypto/
  Rsa.lean            ✓ additive warmup / Euler discipline
  Paillier.lean       ✓ additive HE warmup (algebra proven, kernel deferred)
  Field127.lean       ✓ 𝔽_p, p = 2¹²⁷−1 (Mersenne), prime via Lucas–Lehmer
  HFHE/                NEW — the scheme  (SPEC.md = ground truth, from the C++)
    SPEC.md           ✓ extracted construction (Phase 0 done)
    Defs.lean         ◐ Cipher DAG, decrypt (abstract mask R), encrypt1, cAdd
    Noise.lean        ▢ edge-count / σ-density growth (NOT a correctness budget)
    Correctness.lean  ✓ decrypt_correct (EXACT, keystone #2) + encrypt1_correct
    Homomorphism.lean ▢ ct_add / ct_sub / ct_mul correctness (exact)
    Security.lean     ▢ IND-CPA ⟸ LPN  (a reduction, conditional theorem)
  PVAC/                NEW — verifiability (last)
    Statement.lean    ▢ what "y = f(cts)" claims; binding/soundness specs
    Verify.lean       ▢ the verifier (recompute SHA-256 commit) + its correctness
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
> Now grounded in [Crypto/HFHE/SPEC.md](Crypto/HFHE/SPEC.md) (extracted from the C++).
> Key correction: **decryption is an EXACT identity over 𝔽_p — there is NO decryption
> noise budget.** The ciphertext is a DAG of layers+edges; the secret is a per-layer
> nonzero mask `R` (LPN-derived). Build in order:
1. `Defs.lean` — `Cipher` as a DAG `{L : Layer[], E : Edge[], c0}`; `encrypt`, and
   `decrypt sk c = c0 + Σ ±w·g^idx·R⁻¹`. Mask `R` abstract: `R l ≠ 0`, `R(prod a b)=R a·R b`.
2. `Noise.lean` — NOT a correctness budget (there is none). Tracks edge-count / σ-density
   growth for homomorphic evaluation (`edge_budget`, recrypt). Repurposed.
3. `Correctness.lean` — `decrypt sk (encrypt pk m) = m` as an **exact** algebraic
   telescoping identity (**keystone #2**) — like Paillier but with `=`, not `≡`.
4. `Homomorphism.lean` — `Dec(c₁∘c₂) = m₁∘m₂` for ∘∈{+,−,×}: add = edge-list append,
   mul = `(a0+gA)(b0+gB)` with PROD masks `R_pa·R_pb` (**keystone #3**). Exact.
5. `Security.lean` — `LPN_hard → IND_CPA` (**keystone #4**, a reduction): LPN hides `R`.

### Phase 4 — Circuits / logic gates on ciphertexts
Reframe [LogicGates.lean](Hypergraphs/LogicGates.lean): `ct_add`/`ct_mul` ⇒ functional
completeness. Prove each gate's semantics *under encryption*. Evaluation is bounded by the
edge-budget / σ-density (not a decryption-noise bound). Corollary of Phase 3.

### Phase 5 — PVAC (publicly verifiable), last
`PVAC/Statement.lean` (specs as `Prop`), `PVAC/Verify.lean` (verifier +
soundness/completeness). Most spec-dependent; do once the scheme is solid.

## The five keystone theorems (the joints)

| # | Theorem | Joins | Status |
|---|---------|-------|--------|
| 1 | `incidence` is a parity-check matrix (syndrome linear) | Hypergraph → Coding | ✓ **proven** (`Hypergraphs/Incidence.lean`) |
| 2 | `decrypt (encrypt m) = m` (EXACT, no β) | 𝔽_p + mask R → Scheme | ✓ **proven** (`Crypto/HFHE/Correctness.lean`) |
| 3 | `Dec(c₁∘c₂) = m₁∘m₂`, ∘∈{+,−,×} | Scheme → Circuits | ▢ next — provable (exact); add easy first |
| 4 | `LPN_hard → IND_CPA` | LPN → Scheme | ▢ scaffold (a reduction) |
| 5 | random `H` at MIPT params ⟹ decoding hard | Threshold → LPN | ▢ axiom/cited (MIPT) |

**Discipline:** correctness ⇒ fully proved; hardness ⇒ axiomatized + cited;
security ⇒ a reduction to the axioms. This is how cryptography is formalized.

## Progress & next steps

**Done:** Phase 0 (`SPEC.md` from the C++) · keystone #1 (`Incidence`) · `Field127`
(prime via Lucas–Lehmer) · keystone #2 (`Correctness.decrypt_correct`, exact, plus
`encrypt1_correct` unconditional) · `Coding/*` semi-fleshed.

**Next (any order):**
1. **Keystone #3, additive half:** `Homomorphism.lean` — `decrypt (cAdd a b) =
   decrypt a + decrypt b` (a `List.sum_append` proof, closeable now).
2. **Discharge the `decrypt_correct` kernel:** model `synth` (K=8 signal split
   `Σ sign·coef·g^idx = v − Σδ` + noise tuples) to prove the `kernel` hypothesis,
   making correctness unconditional for the *real* encryption.
3. **`ct_mul`:** the `(a0+gA)(b0+gB)` expansion with `R(prod a b) = R a · R b`.
