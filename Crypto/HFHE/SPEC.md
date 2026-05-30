# HFHE — Spec extraction (Phase 0)

Fill this in from the C++ PoC (<https://github.com/octra-labs/pvac_hfhe_cpp>) and
the attachments **before** writing any types in `Crypto/HFHE/Defs.lean`. Every
Phase-3 Lean signature follows from the answers here.

## Questions to answer

1. **Keys**
   - What is the **secret key** (the trapdoor)? A vector `s ∈ 𝔽_p^n`? A permutation?
   - What is the **public key**? The parity-check matrix `H` (= hypergraph
     incidence)? Plus what else?

2. **Encryption** `encrypt(pk, m, noise) → ct`
   - How is the plaintext `m ∈ 𝔽_p` embedded — scaled by a constant, placed in a
     designated coordinate, …?
   - How is the **hypergraph syndrome** mixed in? `ct = H·r + encode(m) + e`?
   - What exactly is the **noise** `e` (distribution, weight bound)? It becomes an
     explicit argument in Lean.

3. **Decryption** `decrypt(sk, ct) → m`
   - How does the trapdoor strip the mask? Inner product with `s`? Solving a
     small system?
   - What is the **noise bound β** below which decryption is exact?

4. **Homomorphic ops** `ct_add`, `ct_sub`, `ct_mul`
   - Are add/sub just coordinatewise `+`/`−`?
   - What is `ct_mul` concretely — tensor + **relinearization**? Is there
     **bootstrapping**? This determines whether there is a fixed multiplication
     **depth limit**.
   - Exact **noise growth** law for each op (→ `Homomorphism.lean`).

5. **Field placement**
   - Where does `𝔽_p` (p = 2¹²⁷−1) sit vs. the **binary** parity noise? Is the
     code over `𝔽_p` or `𝔽_2` with `𝔽_p` only for the payload arithmetic?

6. **Parameters**
   - Concrete `(n, m, k)` for the random k-uniform hypergraph.
   - The density `c = m/n` and which MIPT threshold result justifies it (→
     `Threshold.lean`, keystone #5).

## Output

A table `C++ symbol → math object → Lean type`, then port it into
`Crypto/HFHE/Defs.lean`.
