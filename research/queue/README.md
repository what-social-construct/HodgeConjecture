# Publication queue

This directory holds frozen candidates awaiting author metadata, venue
formatting, and submission. A file belongs here only when:

- its headline claim is reproduced exactly in `../CLAIM_LEDGER.md`;
- unconditional and conditional results are visually separated;
- all external inputs have exact citations in `../SOURCE_LEDGER.md`;
- `lake build` succeeds from the pinned dependency graph;
- the source contains no `sorry`, `admit`, or project-level `axiom`;
- a human mathematical review has been recorded; and
- novelty language is calibrated against the literature search.

Queue status: empty. The single canonical draft is `../../paper/main.tex`,
producing `../../paper/main.pdf`; its
structural plan remains in `../working/` while human source matching,
mathematical review, and novelty checks are completed.

The former Paper I/Paper II sources and PDFs are archived in
`../archive/manuscripts/` and are not queue candidates or active build targets.

The Palomar fixed-ring package also remains in `../working/`: its Lean
Challenge/Solution pair builds, but the required toolchain migration,
licence and human metadata, Comparator/NanoDa run, research-interest case,
and human mathematical review are not yet complete.
