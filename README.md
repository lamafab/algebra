# Algebra & Cryptography

A collection of [Lean 4](https://lean-lang.org/) files written as a personal study of modern algebra and its applications to cryptography. Built on top of [Mathlib](https://github.com/leanprover-community/mathlib4).

> **Status:** heavily work in progress. Expect gaps, rough edges, and frequent rewrites; files will be added, restructured, and refined over time as the study progresses.

## Layout

- [Algebra](Algebra/): core algebraic structures
  - [Group](Algebra/Group/)
    - [Cyclic](Algebra/Group/Cyclic.lean): cyclic groups and their connection to ℤ/nℤ
  - [Ring](Algebra/Ring/)
    - [Polynomials](Algebra/Ring/Polynomials.lean): polynomial rings, working over 𝔽₃[X]
    - [Ideals](Algebra/Ring/Ideals.lean): ideals, kernels, quotients, and the prime/maximal hierarchy
  - [Field](Algebra/Field/)
    - [Galois](Algebra/Field/Galois.lean): finite fields GF(pⁿ) and their structure
    - [QuadraticResidues](Algebra/Field/QuadraticResidues.lean): squares in 𝔽ₚ, Euler's criterion, and the Legendre symbol
- [Crypto](Crypto/): cryptographic schemes built on the above
  - [DiffieHellman](Crypto/DiffieHellman.lean): key exchange in a cyclic group
  - [Rsa](Crypto/Rsa.lean): RSA correctness from Bézout and Euler's theorem
  - [EllipticCurves](Crypto/EllipticCurves.lean): Weierstrass curves over finite fields
  - [Paillier](Crypto/Paillier.lean): additively homomorphic encryption — decryption correctness proven as algebra, the Carmichael kernel deferred
  - [Field127](Crypto/Field127.lean): the field 𝔽_p with p = 2¹²⁷−1, proven prime via Lucas–Lehmer
  - [HFHE](Crypto/HFHE/) / [PVAC](Crypto/PVAC/): the Octra PVAC-HFHE formalization (see below)
- [Hypergraphs](Hypergraphs/): combinatorial structures generalising graphs
  - [Basic](Hypergraphs/Basic.lean): hypergraphs as (V, E), with incidence, degree, adjacency, rank, and uniformity
  - [LogicGates](Hypergraphs/LogicGates.lean): logic gates on hyperedges as Boolean-algebra operations (AND, OR, NOT, NAND, NOR, XOR, XNOR)
  - [Incidence](Hypergraphs/Incidence.lean): the incidence matrix as a parity-check matrix — the bridge to coding theory
  - [Random](Hypergraphs/Random.lean) / [Threshold](Hypergraphs/Threshold.lean): random k-uniform model and MIPT threshold statements
- [Coding](Coding/): linear codes — the hardness substrate
  - [LinearCode](Coding/LinearCode.lean): parity-check matrices, syndromes, the syndrome-decoding problem
  - [Syndrome](Coding/Syndrome.lean): the hypergraph syndrome map *is* a linear code
  - [LPN](Coding/LPN.lean): the Learning-Parity-with-Noise hardness assumption

## Octra PVAC-HFHE

An in-progress formalization of [Octra's hypergraph-based homomorphic encryption](https://github.com/octra-labs/pvac_hfhe_cpp): additively+multiplicatively homomorphic, secured by LPN/syndrome decoding over a random hypergraph rather than factoring. See [octra.md](octra.md) for the layered roadmap and [Crypto/HFHE/SPEC.md](Crypto/HFHE/SPEC.md) for the construction extracted from the C++. Decryption is an **exact** identity over 𝔽_p (proven in [Correctness](Crypto/HFHE/Correctness.lean)); LPN only hides the secret mask.

## Build

```sh
lake build                       # the whole package
lake env lean Path/To/File.lean  # type-check a single file
```

The Mathlib revision is pinned in [lakefile.toml](lakefile.toml).

![Structures](assets/structures.png)
