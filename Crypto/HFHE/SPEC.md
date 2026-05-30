# HFHE — Spec (extracted from `pvac_hfhe_cpp`, v0.1.0, 2024-09-03)

Reverse-engineered from `pvac_hfhe_cpp/include/pvac/`. References are `file:line`
in that tree. This **replaces the Phase-0 questionnaire** — it is the ground truth
for the Lean types in `Defs.lean` and the keystone theorems.

> ⚠ The scheme is **not** a textbook LWE/LPN "noisy" FHE. Decryption is an **exact
> algebraic identity over 𝔽_p**; the "noise" cancels identically and LPN only hides
> the secret mask. This changes the whole formalization plan — see §10.

## 0. The one identity everything serves

A ciphertext is a DAG of *layers* and *edges*. Decryption computes, per slot `j`:

```
v[j]  =  c0[j]  +  Σ_{edges e}  sign(e.ch) · e.w[j] · g^{e.idx} · R[e.layer_id][j]⁻¹
```
(`decrypt.hpp:62-72`). Encryption arranges the edges so this telescopes back to the
message `v`. `g^{idx}` are public carrier constants; `R[layer]` is a secret PRF mask.
**No discrete log, no rounding, no inequality.**

## 1. Spaces & objects

| object | type | meaning |
|---|---|---|
| `Fp` | 𝔽_p, **p = 2¹²⁷−1** | `{lo,hi}` 127-bit; `fp_inv` = `a^(p−2)` confirms p (`field.hpp`) |
| carrier `g` | order-**B=337** subgroup of 𝔽_p^× | `powg_B[i] = g^i`, `i∈[0,337)` (`keygen.hpp:90-95`); *positional*, **not** a DLP (`types.hpp:38-40`) |
| plaintext `v` | `Fp` (vector of `slots`, default S=8) | additive field element(s) |
| `Edge` | `{layer_id, idx∈[0,B), ch:sign, w:Fp[S], s:BitVec}` | a term `±w·g^idx`; `s` is a decoy syndrome (`types.hpp:108-114`) |
| `Layer` | `{rule:BASE\|PROD, seed, pa, pb}` | DAG node; PROD = product of two layers (`types.hpp:100-106`) |
| `Cipher` | `{L:Layer[], E:Edge[], c0:Fp[S], slots}` | `types.hpp:116-121` |

## 2. Keygen (`crypto/keygen.hpp`)

- **Secret key** `SecKey = {prf_k: u64[4], lpn_s_bits}`:
  - `prf_k` — 256-bit PRF master key, 4 CSPRNG words (`keygen.hpp:51-53`).
  - `lpn_s_bits` — the **LPN secret `s ∈ 𝔽₂^{lpn_n}`**, `lpn_n=4096`, **dense uniform** (not fixed weight) (`keygen.hpp:124-135`).
- **Public key** `PubKey = {prm, canon_tag, H, ubk, H_digest, omega_B, powg_B}`:
  - `canon_tag` — public seed; deterministically generates `H` and `ubk` (`keygen.hpp:45`).
  - `H` — sparse **parity-check matrix**, m=8192 rows × n=16384 cols, **each column weight `h_col_wt=192`** (`matrix.hpp:191-216`). Each column = a 192-subset of the 8192 row-"vertices" → **a 192-uniform hyperedge**; 16384 of them. This is the hypergraph.
  - `ubk` — public permutation of the 8192 bit-positions (Fisher–Yates from `canon_tag`) (`matrix.hpp:95-164`).
  - `H_digest` — SHA-256 binding of `H` (`matrix.hpp:218-250`).
  - `powg_B[i]=g^i`, `omega_B` a generator of the order-337 subgroup (`keygen.hpp:90-122`).

## 3. Encrypt (`ops/encrypt.hpp`, `core::synth` :559-602)

Message `v ∈ Fp^S`. Build a single **BASE** layer with fresh seed and mask `R` (§5):
1. **Noise aggregate** `agg = Σ_i δ_i`, with `δ_i ∈ Fp^S` pseudorandom tuples (`delta::Set::make` :311-320). Budget: `cap = noise_entropy_bits + depth_slope·depth` bits (`:200-213`).
2. **Signal split** `va = v − agg` (`:572`). `K=8` *signal edges* with random positions `g^{pos}`, random coeffs/signs, **last coeff solved** so `Σ sign·coef·g^{pos} = va` (`:352-372`). Edge weight `w = coef · R` (`:580-582`).
3. **Noise edges** (`N2`/`N3` tuples) each split one `δ_t` across 2–3 carrier positions so `Σ sign·r·g^{idx} = δ_t` (`:388-436`); `w = R · r` (`:441-451`).
4. Merge edges per `(layer,idx,sign)`, shuffle. **`c0 = 0`** (`:598`).

Signal edges sum to `v−agg`; noise tuples sum to `agg`; total `= v`. **Public-value
encryption blinds additively**: `Enc(v) = Enc(v+m) ⊞ Enc(−m)` (`:732-738`).

## 4. The secret mask R (LPN) (`crypto/lpn.hpp`, `crypto/toeplitz.hpp`)

`R[j]` is a per-slot **nonzero** field element; `R = r1·r2·r3` (`lpn.hpp:263-268`),
each `r_i` =
1. AES-CTR PRG keyed by `prf_k` (+ `H_digest`) →
2. **LPN syndrome** `ybits = A·s ⊕ e`, `t=16384` rows, `e ~ Bernoulli(τ=1/8)` (`lpn.hpp:194-233`) →
3. **Toeplitz extractor** 𝔽₂^t → 𝔽_{2¹²⁷}≅𝔽_p (`toeplitz.hpp:259-267`) →
4. `hash_to_fp_nonzero` (`lpn.hpp:25-37`).

The LPN error `e` makes `R` pseudorandom; it is recomputed identically at decrypt and
cancels via `R·R⁻¹=1`. (Separately, each edge's decoy `s` = `σ = (⊕_{c∈cols}H[:,c]) ⊕ e`,
fixed weight `x_col_wt=128` cols + `err_wt=128` errors — `matrix.hpp:267-303`; **decode-irrelevant**.)

## 5. Decrypt (`ops/decrypt.hpp`, `dec_values` :46-75) — EXACT

1. Per layer recover `R` (`layer_R_cached` :13-44): **BASE** → `prf_R_slots(pk,sk,seed)`
   (recompute §4); **PROD** → `R = R[pa]·R[pb]`. Set `Rinv = R⁻¹`.
2. `acc = c0`; for each edge/slot: `acc[j] += sign(e.ch)·e.w[j]·g^{e.idx}·Rinv[e.layer_id][j]` (`:69-71`).
3. Output `acc` (`dec_value` = slot 0).

**Correctness condition:** only that every `R[j] ≠ 0` (guaranteed by `hash_to_fp_nonzero`)
and the PROD-DAG is acyclic (`:25-28`). **No probabilistic noise bound.**

## 6. Homomorphic ops (`ops/arithmetic.hpp`)

- **Add** `ct_add` (`:165-188`): concatenate `E` and `L` (rebasing B's layer indices by
  `off=|A.L|`), `c0 = A.c0 + B.c0`. Edges union; no new layer.
- **Sub/Neg/Scale** (`:152-191`): `ct_sub = ct_add(A, ct_neg B)`; `ct_scale` multiplies
  every `e.w` and `c0[j]` by a scalar.
- **Mul** `ct_mul` (`:194-225`): split each into `c0` + g-part; expand
  `(a0+gA)(b0+gB)`. The `gA·gB` term emits one **PROD layer per parent pair** (mask
  `R_pa·R_pb`), repacked into `S=8` fresh edges per layer (`:55-148`); cross terms
  `a0·gB`, `b0·gA` scale-and-append; `c0 = a0·b0`. **No relinearization.** Edge count grows
  ~quadratically; bounded by `edge_budget=1.2M` (`guard_budget`→compact), noise budget
  `120 + 16·depth` bits. No explicit depth cap.
- **Square** `ct_square` (`:227-255`): triangular (off-diagonals doubled).

## 7. Recrypt (`ops/recrypt.hpp`) — density refresh, not classic bootstrap

`ct_recrypt` (`:26-41`): while σ-density off ½, up to 8× add a random `zero_pool`
encryption of 0 and permute every edge's `s` by `ubk` (`:32-33`), then compact. Refreshes
the decoy-selector density toward ½; does **not** reduce DAG depth. (Note: `enc_one` and
`recrypt_lo/hi/rounds` params are declared but unused — code hardcodes 0.495/0.505, 8 rounds.)

## 8. PVAC commit (`ops/commit.hpp`) — binding hash, not a SNARK

`commit_ct` (`:12-97`): a deterministic **SHA-256** over `Dom::COMMIT` ∥ `pk.H_digest` ∥
`canon_tag` ∥ all layers ∥ `c0` ∥ all edges (`layer_id, idx, ch, w[], s`). Public
verifiability = anyone with `(pk, C)` recomputes the same 32 bytes. No zero-knowledge.

## 9. Where the hypergraph & LPN hardness live

- **Hypergraph** = the sparse parity-check `H` (192-uniform, 16384 hyperedges over 8192
  vertices), public, from `canon_tag`. MIPT threshold theory (`refs/*.pdf`) sets the
  weights so the associated decoding is hard.
- **LPN** (dense secret `s∈𝔽₂^{4096}`, τ=1/8) hides the mask `R`. Security ≈ 200-bit
  classical / 100-bit quantum (`types.hpp:54-61`). Confidentiality only — *not* correctness.

## 10. Implications for the Lean formalization (REVISED)

The exactness changes the roadmap (`octra.md`) substantially:

- **Keystone #2 (correctness) becomes an EXACT identity — no noise budget.** Model
  `R : Layer → Fp^S` abstractly (any nonzero mask) and prove the telescoping
  `Σ sign·w·g^idx·R⁻¹ = v` purely algebraically — closely analogous to Paillier's
  `decrypt_correct`, and *easier* (no `≡`, just `=` in 𝔽_p). This is the first target.
- **`Noise.lean` is repurposed:** there is no decryption noise budget. "Budget" here is
  the *edge-count / σ-density* growth governing homomorphic evaluation (edge_budget,
  recrypt), not correctness. Rename/retarget accordingly.
- **`Ciphertext` is a DAG**, not a vector: `structure Cipher where (L : List Layer)
  (E : List Edge) (c0 : Fin slots → Fp)`. Decryption is a fold over `E` with a per-layer
  mask map. The mask `R` should be an abstract parameter satisfying `R ≠ 0` (and
  `R(PROD a b) = R a * R b`); the LPN/PRF derivation is a separate (axiomatized) layer.
- **Homomorphism (keystone #3)**: `add` = list-append correctness (`decrypt` distributes
  over `++` and `c0` add); `mul` = the `(a0+gA)(b0+gB)` expansion with PROD masks
  multiplying. Both are exact identities — provable.
- **Security (keystone #4)**: IND-CPA reduces to LPN hiding `R` (the mask is the only
  secret-dependent quantity); the decoy `s` and `H` decoding feed the assumption.
- **PVAC**: commitment binding/determinism, not a proof system — `Verify` is
  "recompute the hash and compare", with collision-resistance as the assumption.

## 11. C++ → math → Lean type

| C++ | math | planned Lean |
|---|---|---|
| `Fp` | 𝔽_p, p=2¹²⁷−1 | `Octra.Field127.F` ✓ |
| `powg_B[i]` | `g^i`, g order 337 | `def carrier (i : Fin 337) : F` |
| `Edge{idx,ch,w}` | term `±w·g^idx` | `structure Edge where (idx : Fin 337) (sign : Bool) (w : Fin S → F)` |
| `Layer{rule,pa,pb}` | BASE / PROD a b | `inductive Layer \| base \| prod (a b : ℕ)` |
| `Cipher{L,E,c0}` | the DAG | `structure Cipher where (L)(E)(c0)` |
| `R[layer]` | nonzero mask, `R(prod)=Ra·Rb` | `R : ℕ → (Fin S → F)`, hyp `R l j ≠ 0` |
| `dec_values` | `c0 + Σ ±w·g^idx·R⁻¹` | `def decrypt (sk) (c) : Fin S → F` |
| `ct_add/ct_mul` | exact homomorphisms | `theorem add_correct / mul_correct` |
| `commit_ct` | SHA-256 binding | `def commit / verify` (Phase 5) |
