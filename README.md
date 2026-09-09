# Algebra & Cryptography

A collection of [Lean 4](https://lean-lang.org/) files written as a personal study of modern algebra and its applications to cryptography. Built on top of [Mathlib](https://github.com/leanprover-community/mathlib4).

> **Status:** heavily work in progress. Expect gaps, rough edges, and frequent rewrites; files will be added, restructured, and refined over time as the study progresses.

## Layout

- [Algebra](Algebra/): core algebraic structures
  - [Code](Algebra/Code/)
    - [Hamming](Algebra/Code/Hamming.lean): the [7,4,3] Hamming code; generator and parity-check matrices, codewords, syndrome decoding, single-error correction, and a worked example
    - [Hypergraph](Algebra/Code/Hypergraph.lean): hypergraph incidence matrix as a parity-check matrix, k-uniformity, minimum distance, unique syndrome decoding theorem, and the Hamming [7,4,3] code as a 4-uniform hypergraph
    - [ReedSolomonReedMuller](Algebra/Code/ReedSolomonReedMuller.lean): Reed-Solomon codes (univariate polynomial evaluation over GF(2ᵏ), injectivity bound) and Reed-Muller codes (multivariate polynomial evaluation on the boolean hypercube, with RM(1,2) example)
  - [Group](Algebra/Group/)
    - [Cyclic](Algebra/Group/Cyclic.lean): cyclic groups and their connection to ℤ/nℤ
  - [Ring](Algebra/Ring/)
    - [Polynomials](Algebra/Ring/Polynomials.lean): polynomial rings, working over 𝔽₃[X]
    - [RootsInterpolation](Algebra/Ring/RootsInterpolation.lean): the roots bound (Schwartz–Zippel), interpolation, and vanishing polynomials
    - [Multiplicity](Algebra/Ring/Multiplicity.lean): multiplicity of a root, the degree budget counted with multiplicity, the derivative test for repeated roots, and the characteristic-2 collapse (X − 1)²ʳ = X²ʳ − 1
    - [Ideals](Algebra/Ring/Ideals.lean): ideals, kernels, quotients, and the prime/maximal hierarchy
    - [Multilinear](Algebra/Ring/Multilinear.lean): multivariate polynomials, the multivariate Schwartz–Zippel bound, and the multilinear extension (MLE) of boolean functions over 𝔽₂
  - [Field](Algebra/Field/)
    - [Galois](Algebra/Field/Galois.lean): finite fields GF(pⁿ) and their structure
    - [Characteristic](Algebra/Field/Characteristic.lean): the characteristic of a field; why it is prime, char-2 facts (x = −x, translation involutions), the freshman's dream, and the squaring dichotomy (2-to-1 odd vs 1-to-1 char 2)
    - [QuadraticResidues](Algebra/Field/QuadraticResidues.lean): squares in 𝔽ₚ, Euler's criterion, and the Legendre symbol
    - [RootsOfUnity](Algebra/Field/RootsOfUnity.lean): roots of unity in finite fields, primitive roots, and the connection to cyclic subgroups
    - [BinaryFields](Algebra/Field/BinaryFields.lean): GF(2) and GF(2ⁿ), boolean gates as polynomials, Freshman's dream, Frobenius, and trace map
- [Crypto](Crypto/): cryptographic schemes built on the above
  - [DiffieHellman](Crypto/DiffieHellman.lean): key exchange in a cyclic group
  - [Rsa](Crypto/Rsa.lean): RSA correctness from Bézout and Euler's theorem
  - [EllipticCurves](Crypto/EllipticCurves.lean): Weierstrass curves over finite fields
  - [Paillier](Crypto/Paillier.lean): additively homomorphic encryption, decryption correctness proven as algebra
  - [McEliece](Crypto/McEliece.lean): code-based encryption; scrambling by S·G·P, decryption correctness from a decoder hypothesis, and a fully executable [7,4,3] Hamming code instance
  - [ZK](Crypto/ZK/)
    - [Schnorr](Crypto/ZK/Schnorr.lean): sigma protocol for knowledge of a discrete log; completeness, special soundness, and honest-verifier zero-knowledge
    - [Sumcheck](Crypto/ZK/Sumcheck.lean): the sumcheck protocol on the boolean hypercube; the soundness per round is read off the multivariate Schwartz–Zippel bound
    - [BinaryFRI](Crypto/ZK/BinaryFRI.lean): proximity testing over binary fields; additive folding via q(x) = x² + β·x, and Merkle paths with verified openings
    - [Binius](Crypto/ZK/Binius.lean): the full binary-field argument for a boolean circuit, end to end on an AND gate; MLE → sumcheck → binary FRI → Merkle, with the soundness budget
- [Examples](Examples/): end-to-end runs that wire the pieces above together
  - [BiniusToy](Examples/BiniusToy.lean): one AND-gate evaluation carried through the whole Binius pipeline: the arithmetized claim, the Merkle commitment, the sumcheck reduction to a single point, and the final opening check

## Build

```sh
lake build
```

The Mathlib revision is pinned in [lakefile.toml](lakefile.toml).

![Structures](assets/structures.png)
