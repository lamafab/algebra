---
name: lean-algebra-crypto
description: >
  Work in this Lean 4 + Mathlib study repo (algebra, cryptography, hypergraphs,
  and the Octra PVAC-HFHE formalization). Use when adding or editing `.lean`
  files here, verifying they compile, matching the pedagogical house style, or
  extending the HFHE roadmap. Covers the non-obvious build workflow (no
  `lean_lib` target → `lake env lean`, stale-olean traps) and the
  crypto-formalization discipline (prove correctness, axiomatize hardness).
---

# Lean Algebra & Cryptography repo — agent guide

A personal Lean 4 study of modern algebra and its cryptographic applications,
built on Mathlib. Files are **pedagogical**: heavy prose, worked examples, and
cross-references — they teach, not just prove. Match that register.

## Orientation (read these first)

- [README.md](../../../README.md) — the map of the repo.
- [octra.md](../../../octra.md) — the **PVAC-HFHE formalization roadmap**: five
  layers, two tracks, file hierarchy, five keystone theorems, six phases.
- [todo.txt](../../../todo.txt) — the algebraic-structures coverage grid.
- Toolchain: `leanprover/lean4:v4.30.0-rc1`, Mathlib pinned in
  [lakefile.toml](../../../lakefile.toml). `autoImplicit = false`.

Directory meaning:
- `Algebra/` — core structures (`Group/`, `Ring/`, `Field/`). Foundations.
- `Crypto/` — schemes on top (`Rsa`, `DiffieHellman`, `EllipticCurves`,
  `Paillier`, `Field127`, and the `HFHE/` + `PVAC/` Octra scaffold).
- `Hypergraphs/` — `Basic`, `LogicGates`, `Incidence` (bridge to coding), plus
  `Random`/`Threshold` stubs.
- `Coding/` — linear codes / syndrome decoding / LPN (HFHE hardness substrate).

## Build & verify — IMPORTANT, non-standard

There is **no `lean_lib` in the lakefile**, so `lake build SomeModule` fails with
`unknown target`. Verify a single file by type-checking it directly:

```sh
lake env lean Path/To/File.lean        # typecheck; exit 0 = compiles, prints errors otherwise
```

**Local imports resolve via compiled oleans** under
`.lake/build/lib/lean/<Module>.olean`. Two consequences:

1. **Stale-olean trap (you WILL hit this).** If you add a `def`/`theorem` to a
   file (say `Hypergraphs/Basic.lean`) but its `.olean` is older than the source,
   any *importing* file sees the OLD interface — symptom: a real definition is
   reported as an `invalid field` / `unknown identifier`. Fix by rebuilding the
   dependency's olean:
   ```sh
   lake env lean -o .lake/build/lib/lean/Hypergraphs/Basic.olean Hypergraphs/Basic.lean
   ```
   Check staleness with `ls -la` on the `.lean` vs the `.olean`.
2. **New local modules need oleans before dependents compile.** Build in
   dependency order, emitting each olean:
   ```sh
   build() { local m="$1" s="$2"; local o=".lake/build/lib/lean/${m//.//}.olean"
     mkdir -p "$(dirname "$o")"
     lake env lean -o "$o" "$s" && echo "OK $m" || echo "FAIL $m"; }
   build Hypergraphs.Incidence Hypergraphs/Incidence.lean
   build Coding.LinearCode     Coding/LinearCode.lean
   # …topological order…
   ```

Mathlib oleans are prebuilt, so `import Mathlib.*` is "free"; only *local* imports
need this dance. (Tip you may offer the user: adding a `[[lean_lib]]` stanza to
`lakefile.toml` would make `lake build` work normally.)

## House style — match it

- **Banner headers** delimit files and sections:
  ```lean
  -- ============================================================================
  -- Section N: Title
  -- ============================================================================
  ```
- **Prose-first.** Open each file/section with a comment explaining the *idea*
  (often with ASCII math, e.g. `e_{and}(H) = e₁(H) ∩ e₂(H)`), then the code.
- **Concrete `example`s as tests**, closed by `decide` / `native_decide` /
  `norm_num` — these double as executable sanity checks. Include them.
- **`notation` for pet objects**: `notation "𝔽₃" => ZMod 3`.
- **Prime fields**: `instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩`.
- **Unicode is idiomatic** in math positions (`𝔽ₚ`, `≡`, `∩`, `⊆`, subscripts).
  BUT never in identifiers — see pitfalls.
- **Cross-reference sibling files** in comments ("Cyclic.lean and Galois.lean are
  the prerequisites").
- File references in chat use markdown links, not backticks:
  `[Basic.lean:79](Hypergraphs/Basic.lean#L79)`.

## Proof idioms used here

- `decide` — small finite/decidable goals (`Fintype.card (ZMod 4) = 4`).
- `native_decide` — heavier concrete computation (e.g. running encrypt/decrypt in
  `ZMod n²`). Compiles to native code; keep exponents/moduli reasonable. Prefer
  `ZMod`-typed computation over ℕ so values reduce instead of exploding (`2^3233`
  as a ℕ literal is fatal; in `ZMod nn` it's fine).
- `norm_num` — numeric facts, primality (`Nat.Prime 7`), and the Lucas–Lehmer
  residue. A Mersenne prime `p = 2^k − 1`:
  ```lean
  theorem p_prime : Nat.Prime (2^127 - 1) :=
    lucas_lehmer_sufficiency _ (by simp) (by norm_num)   -- mersenne 127
  ```
- `ext`, `simp only [defs, mem_lemmas]`, then `tauto` — the standard recipe for
  Finset-set-equality goals (see [LogicGates.lean](../../../Hypergraphs/LogicGates.lean)).
- `linear_combination` / `ring` — polynomial-identity goals over ℤ/rings (see
  [Paillier.lean](../../../Crypto/Paillier.lean) `decrypt_correct`).
- `Int.modEq_iff_dvd` to turn `a ≡ b [ZMOD n]` into a divisibility, then provide
  the witness.

### `ZMod n` (a TYPE) vs `[ZMOD n]` (a relation)
- `ZMod n` is the *type* ℤ/nℤ — values are reduced; use it to **compute**.
- `a ≡ b [ZMOD n]` is `Int.ModEq n a b`, a *proposition* about un-reduced ℤ; use
  it to **prove**, especially when an operation (like Paillier's `L(x)=(x-1)/n`
  integer division) isn't defined inside `ZMod n`. Bridge:
  `ZMod.intCast_eq_intCast_iff`.

## Crypto-formalization discipline (the repo's spine)

Every scheme follows the same split — apply it to any new crypto work:
- **Correctness ⇒ prove fully** (it's algebra). E.g. `Rsa.rsa_correctness`,
  `Paillier.decrypt_correct`.
- **Hardness ⇒ axiomatize + cite** (no one proves these). E.g.
  `Coding.lpn_hard`, the Carmichael kernel `sorry` in Paillier, the MIPT
  threshold `axiom` in `Hypergraphs/Threshold.lean`.
- **Security ⇒ a reduction** (conditional theorem `Assumption → Secure`), never
  unconditional.

When deferring, make it loud and well-typed: a `sorry` with a comment explaining
what's deferred, or a named `axiom`. Don't fake a proof.

## Common pitfalls (hit this session)

- **`λ` cannot appear in identifiers** — `cλ` fails to parse (`λ` = lambda token).
  Use `cl`, `clam`, etc. Unicode subscripts like `e₁`, `m₂` are fine.
- **Stale olean ⇒ phantom "invalid field"** — see Build section. The definition is
  there; the olean isn't. Rebuild it before trusting the error.
- **`mulVec_smul` needs commutativity** — `M *ᵥ (c • x) = c • (M *ᵥ x)` is false
  over a noncommutative semiring. Require `CommSemiring` (the code field 𝔽_q is
  commutative) or prove via `funext`/`Finset.mul_sum`/`ring`.
- **Unused section variables warn** — if a `variable [DecidableEq n]` isn't used by
  a theorem, Lean lints it. Drop it from `variable` or `omit … in` *before* the
  doc-comment (omit-after-doccomment doesn't parse).
- **`native_decide` blow-ups** — compute in `ZMod`, not ℕ, so powers reduce.

## Adding a new file (checklist)

1. Pick the right directory (foundation → `Algebra/`, scheme → `Crypto/`,
   combinatorics → `Hypergraphs/`, codes → `Coding/`).
2. Imports: the specific Mathlib modules you need + `import Mathlib.Tactic`, then
   any local deps (`import Hypergraphs.Basic`).
3. Open with a banner + prose explaining the idea.
4. Sectioned defs/theorems, each with a comment; add concrete `example` tests.
5. Verify: `lake env lean Your/File.lean` (rebuild dependency oleans first if you
   touched them).
6. If other files will import it, emit its olean (`-o …`).

## The Octra HFHE work specifically

- Read [octra.md](../../../octra.md) and [Crypto/HFHE/SPEC.md](../../../Crypto/HFHE/SPEC.md).
- Status: `Hypergraphs/Incidence.lean` (keystone #1) and `Crypto/Field127.lean`
  are **proven**; `Coding/*` are semi-fleshed; `Crypto/HFHE/*` and `Crypto/PVAC/*`
  are **typed-out comment scaffolds awaiting the spec** — do NOT invent the
  construction; fill `SPEC.md` from the C++ PoC first, then write `HFHE/Defs.lean`.
- `Paillier.lean` is the **discipline reference** for HFHE correctness: model the
  scheme deterministically (noise/randomness as explicit args), prove correctness
  as algebra under a noise bound, defer the number-theoretic kernel.

## Scope / safety

This is authorized cryptographic *study and formalization* — proving schemes
correct, not attacking systems. Stay in that lane.
