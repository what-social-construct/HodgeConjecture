# Research workspace

This directory is a non-destructive staging area for research notes derived
from the Lean development. Nothing in `HodgeConjecture/` is moved or deleted
by this workflow.

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

The queue is for publication candidates, not for brainstorming. A queued
item must say whether it is:

- an unconditional theorem proved by the Lean source;
- a theorem conditional on explicitly named hypotheses; or
- a formalization report about known mathematics.

No item may be described as a result on the Hodge conjecture unless its
statement actually produces an algebraic cycle for a separately specified
Hodge class without assuming the required realization or algebraicity.
