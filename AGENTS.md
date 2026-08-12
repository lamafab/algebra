# Agent instructions for the algebra Lean repository

## Repository layout

The repository has two top-level source directories:

- `Algebra/`: core algebraic structures arranged by algebraic hierarchy:
  - `Algebra/Code/`: error-correcting codes (e.g. Hamming)
  - `Algebra/Group/`: group theory (e.g. cyclic groups)
  - `Algebra/Ring/`: ring theory (polynomials, roots/interpolation, ideals)
  - `Algebra/Field/`: field theory (finite fields, quadratic residues, roots of unity)
- `Crypto/`: cryptographic schemes that build on the algebraic foundations:
  - Top-level files for each scheme (e.g. DiffieHellman, Rsa)
  - `Crypto/ZK/`: zero-knowledge protocols (e.g. Schnorr)

Each file is self-contained and imports only Mathlib or other files in this repo as needed. When adding a new file, place it in the directory that matches its algebraic category and update the README layout section.

## Clarifications stay in chat

When asked for a clarification or explanation, answer in chat only. Do not write it into Lean files, and do not expand a file's comments to cover it, unless the user separately asks for a file edit.

**Why:** Clarifications are specific to the user's own current understanding. The Lean files are written for an outside reader and must stay neutral and self-contained; absorbing personal Q&A bloats them and skews the level of explanation towards one reader.

Only touch a `.lean` file when the user explicitly asks for it (e.g. "add this to the file", or a `TODO` in the file they point at). When they do ask, write the compact neutral version rather than the conversational one (see comment style below).

## Lean comment style

Comments in Lean files must be compact and simple:

- No em dashes (`—`). Use a semicolon, comma, colon, or a new sentence.
- No ALL-CAPS words, unless the emphasis is genuinely justified (a term being defined, or a point of real importance). Do not use caps as routine emphasis.

**Why:** The repo is a published study resource; the prose should read as calm, neutral exposition rather than energetic narration.

Prefer short declarative sentences over long ones joined by dashes. Reach for a term in backticks or plain lowercase instead of capitalising it. Keep explanatory comment blocks tight; if an explanation is growing long, that is a signal it belongs in chat instead.

## Olean rebuild after interface change

`lake env lean <file>.lean` type-checks a file but does **NOT** write/install its `.olean`. Downstream files load oleans from `.lake/build/lib/lean/<ModulePath>.olean`. So when you change a shared structure or other public interface, every file that transitively imports it has a now-stale olean, and re-running `lake env lean` on a downstream file silently loads the OLD interface (symptoms: "unknown identifier", "invalid field `toX`", cascading `sorry`/`native_decide` failures that don't match the source).

Fix: regenerate the affected oleans **in topological (import) order** with explicit `-o`:

```
lake env lean -o .lake/build/lib/lean/<ModulePath>.olean <path>/<File>.lean
# …then each downstream file in dependency order, ending with the leaf files.
```

A clean build prints no output (errors go to stderr+stdout; empty == success). IDE/LSP diagnostics lag behind these manual rebuilds, so during such a change trust the command-line `lake env lean` result, not the inline diagnostics.