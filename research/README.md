# Research workspace

This directory separates current proof status, dated research checkpoints,
and archived material. Authorized pruning preserves retired Lean sources
under `archive/legacy-lean/` after checking that active imports do not use
them; old planning documents live under `archive/planning/`.

The current reading order is [TARGET_BRIDGE.md](TARGET_BRIDGE.md),
`GAP_MAP.md`, `CLAIM_LEDGER.md`, then the single manuscript.
The [object bench](bench/README.md) holds valid but currently non-spine
diagnostics for reconsideration; it is distinct from deprecated provenance
in `archive/` and publication candidates in `queue/`.
`working/0017-proof-spine-and-archive.md` records which supporting
calculations are used and which geometric steps remain unconstructed. Older
checkpoints document their own dates, not competing current proof plans.

## Workflow

1. Put exploratory material in `inbox/`.
2. Develop one precise claim at a time in `working/`.
3. Keep the current endpoint factorization in `GAP_MAP.md`, record every
   mathematical claim in `CLAIM_LEDGER.md`, and record every external input
   in `SOURCE_LEDGER.md`.
4. Run the checks in `RELEASE_CHECKLIST.md`.
5. Copy a frozen release candidate into `queue/` only after both the formal
   statement and the prose statement have been checked.

Historical source that is no longer part of the active, self-contained Lean
library is retained under `archive/`. Archived modules are provenance
snapshots, not build targets or current theorem claims.

The single active manuscript is [`../paper/main.tex`](../paper/main.tex),
producing [`../paper/main.pdf`](../paper/main.pdf). The former Paper I and
Paper II sources and PDFs are preserved in
[`archive/manuscripts/`](archive/manuscripts/) as historical snapshots,
outside the release build requirements.

The queue is for publication candidates, not for brainstorming. A queued
item must say whether it is:

- an unconditional theorem proved by the Lean source;
- a theorem conditional on explicitly named hypotheses; or
- a formalization report about known mathematics.

No item may be described as a result on the Hodge conjecture unless its
statement actually produces an algebraic cycle for a separately specified
Hodge class without assuming the required realization or algebraicity.
