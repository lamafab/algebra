# Hardness, Security, and the Limits of the Formalization

What can and cannot be *proven* about Octra PVAC-HFHE, and why keystones #4 and #5
are a different universe from #1–#3. Companion to [octra.md](octra.md) and
[Crypto/HFHE/SPEC.md](Crypto/HFHE/SPEC.md).

## The three-layer discipline (how formal crypto actually works)

| layer | example here | what you do |
|---|---|---|
| **correctness** | `decrypt (encrypt m) = m` | **prove it** (exact algebra) |
| **hardness assumption** | LPN / syndrome decoding is hard | **axiomatize + cite** — you *cannot* prove these |
| **security** | IND-CPA of the scheme | **a reduction**: `assumption → secure` (conditional theorem) |

This is the EasyCrypt/CryptHOL standard: real formal-crypto proofs (TLS, MEE-CBC, …)
**never prove their assumptions**; they prove reductions *to* standard assumptions
and treat the assumptions as axioms. Our split already matches this.

## Keystone #4 — `LPN_hard → IND-CPA` (the security reduction)

A genuine *proof* (a reduction), not a conjecture — but brutal in Lean:

1. **Game-based & probabilistic.** IND-CPA is a game with a probabilistic
   adversary; "advantage" is a difference of probabilities; you prove
   `Adv_scheme ≤ Adv_LPN + negligible` via a sequence of *game hops*. The
   δ-blinding and σ-decoy indistinguishability arguments must be cashed out as
   inequalities here.
2. **Lean has no mature crypto-reduction framework.** Mathlib has probability
   (`PMF`, `ProbabilityTheory`) but **no IND-CPA game, no PPT-adversary model, no
   negligibility calculus, no game-hop tactic.** That machinery exists in *other*
   systems — EasyCrypt, CryptHOL (Isabelle), FCF/SSProve (Coq) — each years of
   foundational work. In Lean you'd build/port it first.
3. **The reduction may not exist on paper.** Octra is bounty/challenge-driven, not
   reduction-backed. If no tight "break ⟹ solve standard LPN" exists, #4 is
   *research* (discover the reduction first) — and if it fails to hold, that
   discovery is a *break*.

**Realistic target:** define the game + advantage *abstractly*; prove the reduction
**skeleton** modulo a handful of explicitly-stated indistinguishability lemmas
(`axiom`/`sorry`). Machine-check the *shape* of the argument (where most real-world
breaks hide); leave the probabilistic leaves assumed. Don't build all of CryptHOL.

## Keystone #5 — random `H` ⟹ decoding hard (the hardness assumption)

**Not provable, by definition.** Average-case hardness is a *conjecture* (like
`P ≠ NP`); "it's hard" *is* the assumption. Finish line = **state precisely + cite
MIPT + `axiom`.** That is the intended end state of `Hypergraphs/Threshold.lean`,
not a cop-out. Two separable pieces:

- **Average-case syndrome-decoding hardness** → conjecture → axiom. (The
  *worst-case* NP-hardness of decoding is a real theorem — Berlekamp–McEliece–van
  Tilborg, 1978 — but worst-case ≠ average-case, and crypto needs average-case.)
- **MIPT threshold combinatorics** (sharp thresholds / fractional chromatic number
  of random k-uniform hypergraphs) → *real theorems*, but **research-grade** to
  formalize (second-moment method, sharp-threshold machinery, container/entropy
  methods — multi-month specialist projects). And they only **justify the
  parameter choice**; they do *not* deliver security by themselves.

## Effort map

| keystone | verdict |
|---|---|
| #2 correctness | ✓ done — exact algebra |
| #3 homomorphism | provable, days–weeks (mul is the work) |
| #4 security | months + a framework Lean lacks + maybe upstream research |
| #5 hardness | inherently an `axiom`; (optional, brutal) threshold combinatorics for *parameters only* |

## Security-maturity caveat (keep this in mind)

The formalization proves **correctness**, which was never the doubtful part.
"Revolutionary if true" rests entirely on **security**, which is *unestablished*:

- **Design category risk.** Exact / noise-free *fully* homomorphic encryption is
  historically the most dangerous FHE design space — exactness gives attackers
  clean algebra; many such schemes have been proposed and broken. (Mainstream FHE
  keeps noise *because the noise is where the proven hardness lives*.)
- **No established reduction.** Security is a *bespoke* LPN-over-random-hypergraph
  assumption with no public tight reduction to standard LPN (keystone #4 unproven).
- **Maturity signals.** v0.1.0 self-described "PoC"; bounty/challenge-driven
  (`bounty*_data/`, `tests/bounty_r2_attack.cpp` — note the round-2 attack);
  code smells the read surfaced (declared-but-unused security params
  `recrypt_lo/hi/rounds`; the σ role uncommented `//(?)`; a modulo-bias off-by-one).

**Correctness (proven) ≠ security (unvetted).** Extraordinary claims need
extraordinary cryptanalysis, and that has not visibly happened.
