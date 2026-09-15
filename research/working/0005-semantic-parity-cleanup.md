# Semantic parity, pruning, and notation queue

Status: AUTOMATED PARITY PASS COMPLETE; HUMAN RELEASE GATES OPEN.

Opened: 2026-09-11.

This queue keeps three representations synchronized:

```text
Lean declaration  <->  mathematical object  <->  TeX notation
```

It is an implementation-maintenance document, not a theorem or publication
claim.  A declaration receives an independent TeX symbol only when it denotes
an independent mathematical object.  Compatibility wrappers, conversion
theorems, and implementation lemmas are marked **prose only**; inventing a
second symbol for them would conceal rather than cure semantic duplication.

The single active manuscript is `paper/main.tex`, producing `paper/main.pdf`.
The former Paper I/Paper II sources and PDFs are preserved in
`research/archive/manuscripts/` and are excluded from release build gates.

## Dispositions

- **CANONICAL**: the unique active representation of a mathematical object.
- **REFINEMENT**: genuinely adds data or a stronger property to a canonical
  object.
- **ADAPTER**: changes representation without adding a mathematical premise.
- **COMPAT**: a public wrapper retained temporarily while callers migrate.
- **LEGACY**: a superseded branch excluded from the active umbrella imports.
- **RESEARCH**: retained outside the release proof path.
- **BENCH**: a valid object set aside for possible reuse, without active
  library exports or a role in the intended target sketch.
- **DEFERRED**: cleanup depends on an unfinished mathematical endpoint.

## Cleanup queue

| ID | Object or overlap | Disposition | Required action | Status |
| --- | --- | --- | --- | --- |
| SP0 | Active declaration and import inventory | CANONICAL | Distinguish semantic callers from verification and prose references. | DONE |
| SP1 | Two definitions of the idempotence defect `q * q - q` | CANONICALIZE | Put the ring-generic definition and its map/zero lemmas in one low-level module; make closure defects a specialization. | DONE |
| SP2 | Two proofs that collision tensor multiplication is surjective | CANONICALIZE | Keep one theorem in the collision algebra layer and use it in affine geometry and the different. | DONE |
| SP3 | Two copies of graph/diagonal/shear linear algebra | CANONICALIZE | Extract the generic Tate-block calculation below both boundary and realization; define the marked block by specialization. | DONE |
| SP4 | `NoCodimensionOneRamification` versus emptiness of `RamifiedCodimensionOnePoint` | ADAPTER | Prove one canonical equivalence and make both geometric routes target only one presentation. | DONE |
| SP5 | Diagram-only map wrappers and disconnected conjugate ring map | PRUNE/CONNECT | Remove unused wrappers or make the scheme leg visibly use the canonical ring map. | DONE |
| SP6 | Historical commutative selector-realization lane | LEGACY | Remove it from active umbrella imports while retaining its source for compatibility and provenance. | DONE |
| SP7 | One-boundary extension structures versus singleton-family specializations | COMPAT | Prefer the family structures with `PUnit`; retain the local carrier and theorem names as lossless adapters for public compatibility. | DONE |
| SP8 | Broad abstract `NormalizationPurity`/global-triviality prototype | RESEARCH | Remove the module from the active boundary umbrella and release verification; retain it as an explicitly conditional prototype. | DONE |
| SP9 | Global-Dedekind and pre-localization prime-inertia wrappers | DEFERRED | Retire after the unconditional fixed-prime-inertia endpoint replaces their remaining premise. | BLOCKED ON FIXED-INERTIA THEOREM |
| SP10 | `research/inbox/PrimeInertiaScratch.lean` duplicates promoted declarations | RESEARCH | Move the scratch file to the archive; do not delete its provenance. | DONE |
| SP11 | Redundant direct imports | PRUNE | Remove accidental fixed-ring dependency edges; retain direct imports for APIs actually used and umbrella imports as deliberate export lists. | DONE |
| SP12 | Canonical TeX notation | CANONICAL | Give every retained semantic object below exactly one notation and use it consistently in the canonical manuscript. | REGISTRY DONE; HUMAN SEMANTIC AUDIT OPEN |
| SP13 | Claim/manuscript/build parity | RELEASE GATE | Update ledgers and manuscript, run full Lean/TeX builds, proof-gap scans, and diff checks. | AUTOMATED CHECKS DONE; HUMAN GATES OPEN |
| SP14 | `LiftWitness` targets defined from their own compactified action | COMPAT | Exclude the tautological self-action wrappers from the active claim and verification spine; use `PrescribedChowProjectorLift` for independently specified targets. | DONE |
| SP15 | Full sheet-algebra presentation versus the actual Galois graph map | PRUNE/REFINE | Keep `A_H →ₐ Γ_η` only as an optional stronger interface; remove the linear coset-average map from the active umbrella and do not use either as the Galois bridge. | DONE |
| SP16 | Projector homomorphism hidden behind a selector equation | CANONICALIZE | Use the universal one-idempotent algebra, expose the restriction and realization equalities as equalities of algebra-homomorphism composites, and prove the full representation law equivalent to the selector square. | DONE |

## Canonical semantic object and TeX registry

### Construction and input checkpoints (SP17--SP53)

| ID | Object or overlap | Disposition | Required action | Status |
| --- | --- | --- | --- | --- |
| SP17 | Action comparison unnecessarily requires ambient restriction to commutative sheets | CANONICALIZE | Extract `MarkedProjectorActionComparison`; retain extension-based comparisons as lossless specializations; prove the full-matrix obstruction and instantiate the new core. | DONE; FULL BUILD AND VERIFICATION PASS |
| SP18 | Geometric point span, free span class, matrix coefficient, and Chow class | CONNECT / KEEP DISTINCT | Construct the split-span coefficient realization on actual geometric classes; retain the free source, its matrix image, and genuine Chow as distinct objects. | COEFFICIENT BRIDGE PROVED; CHOW IN SP22; BETTI IN SP23 |
| SP19 | Vanishing relations versus the full kernel; free source versus additive quotient | IDENTIFY / KEEP DISTINCT | Generate a two-sided ideal by finite point decompositions, prove it is the full realization kernel, and construct the quotient-to-matrix algebra equivalence. Keep actual Chow-correspondence and Betti comparison separate. | EXACT ADDITIVE QUOTIENT PROVED; CHOW IN SP22; BETTI IN SP23 |
| SP20 | Point labels versus actual integral closed subschemes and their dimension | IDENTIFY | Classify actual integral closed immersions and ideal-sheaf subschemes as reduced rational points; prove every closed subscheme has dimension at most zero. Use these actual generators in the subsequent cycle construction. | CLASSIFICATION AND NO-CURVES THEOREM PROVED |
| SP21 | Actual zero-cycles, rational equivalence, and additive Chow groups | CONSTRUCT / IDENTIFY | Form cycles on the actual integral subschemes; index principal-divisor data by actual integral curves and function-field units; prove the indexing type empty and the generated relations zero; identify the resulting Chow group with point coefficients and prove the integral-to-rational scalar-extension comparison. The correspondence-algebra comparison is recorded separately in SP22. | CYCLE AND CHOW GROUPS PROVED; FULL BUILD AND VERIFICATION PASS |
| SP22 | Actual products, multiplicities, Chow composition/algebra/action, and the span quotient | CONSTRUCT / IDENTIFY | Identify actual image and inverse-image subschemes and their degree/length multiplicities; construct the cycle/Chow operations; prove the geometric composition and action matrix laws; retain geometric multiplication when packaging the Chow algebra and identify it with the existing additive span quotient. | PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS |
| SP23 | Actual complex points, singular degree-zero cohomology, cycle classes, and cohomological action | CONSTRUCT / COMPARE | Give actual complex-algebra points their evaluation-induced topology and prove discreteness; form genuine singular cocycles using actual face maps; construct the point-normalized cycle-class equivalence and its operation/action compatibilities. Keep actual Chow, singular cohomology, and their coordinate modules distinct; record the independent Hodge/Tate-block comparison in SP24. | PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS |
| SP24 | Independent finite Hodge data, actual point-plus-scheme block, graph encoding, and lower-left detection | CONSTRUCT / INSTANTIATE | Form the actual tensor complexification and canonical conjugation; specify and verify the effective degree-zero bigrading, then define rational Hodge classes by inverse image. On the actual scheme coproduct, encode by point-pair addition plus column pushforward and decode by column pullback. Prove their actual Betti realization laws and instantiate the Hodge/graph/Palomar targets. | PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS |
| SP25 | Actual split torsor, multiplicative residual Chow map, diagonal source embedding, and marked action comparison | CONSTRUCT / COMPARE | Realize the marked ideal by actual point cycles, then cycle class; build the regular torsor and homogeneous intermediate cover. Implement the constant-marked coordinate change by an invertible actual Chow shear inside the fixed target action. Keep the raw point projector, its conjugate, and the canonical negative fundamental class distinct; formalize the multiplicative obstruction to arbitrary class coverage. | PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS |
| SP26 | Selected literature conclusions versus their full source theorems and geometric applications | CANONICALIZE / SEPARATE | Move the fixed-inertia record without duplicating it; expose actual finite étale extension data and separate automorphism-restriction bijectivity; package rational-linear Chow exactness and prove conditional raw-lift/boundary-defect consequences. Keep source instantiation, multiplication compatibility, defect vanishing, graph/action comparison, and coverage distinct. Preserve the Mathlib-only submission statements. | CONDITIONAL CONSEQUENCES PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS |
| SP27 | Standalone matrix diagnostic versus the intended target and actual finite Chow coordinates | BENCH / CLARIFY | Preserve the diagnostic unchanged in `research/bench/`; remove active exports, verification entries, and manuscript proposition. Keep used finite Chow matrix constructions. Record the genuine target, C/D equivalence, minimal marked detection route, and exact geometric gaps in `research/TARGET_BRIDGE.md` and the single manuscript. | DONE; FULL BUILD, 98 AXIOM REPORTS, DEPENDENCY AUDIT, BENCH CHECK, AND SINGLE-PDF BUILD PASS |
| SP28 | Core Chow detection, chosen extension projector, and reverse Galois coverage | PLACE / KEEP DISTINCT | Put Chow detection in the core comparison and reuse it in the Galois specialization. Keep idempotence/surjectivity on the chosen-projector branch and replacement on the reverse coverage arrow. Preserve the supplied extension data. | DONE; ORIGINAL 101-REPORT CHECKPOINT PASSED; AUXILIARY MATERIAL SUBSEQUENTLY BENCHED IN SP29 |
| SP29 | One chosen algebraic projector in the active proof spine | BENCH / SIMPLIFY | Preserve the unused auxiliary helper and its tests on the bench; remove its active Lean, manuscript, claim, and notation references. Keep the chosen projector, cycle detection, C/D target equivalence, and the named Galois replacement premise. Normalize the extension notation and the universal-map codomain. | DONE; FULL BUILD, 100 AXIOM REPORTS, TWO CHOSEN-PROJECTOR REGRESSIONS, BENCH CHECK, DEPENDENCY AUDIT, AND SINGLE-PDF BUILD PASS |
| SP30 | Graph span versus actual closed graph subscheme and its open restriction | CONSTRUCT / KEEP DISTINCT | Construct the graph morphism and kernel ideal, identify its subscheme under separatedness, and prove the actual Cartesian restriction square and ideal-sheaf comap equality for a supplied finite étale extension. Keep Chow classes and convolution comparison as the next checkpoint. | PROVED; FULL BUILD, 114 AXIOM REPORTS, FIVE GRAPH REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP31 | Canonical finite cycles, integral graph generators, and open restriction | GENERALIZE / CONNECT | Reuse one actual integral-subscheme cycle type in the split and general cases; prove nonempty/empty open restriction, identity/composition, graph integrality/dimension, and the weighted graph-cycle restriction square. Keep the cycle maps linear and ungraded until geometric Chow composition and its grading are constructed. | PROVED; FULL BUILD, 129 AXIOM REPORTS, SIX CYCLE REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP32 | Actual graph-intersection scheme versus formal span composition and cycle products | CONSTRUCT / KEEP DISTINCT | Prove the sum-of-comaps intersection, its source isomorphism, and the isomorphic first/last projection onto the composite graph. Compute integral fundamental multiplicity as ambient generic-stalk length. Retain the Chow intersection-product and proper-pushforward comparison as separate obligations. | PROVED; FULL BUILD, 139 AXIOM REPORTS, SEVEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP33 | Closed-support cycle pushforward and relative graph-slice pull–push | CONSTRUCT / CONNECT | Use actual ideal images and generic residue degree one; construct functorial closed-immersion pushforward, the actual graph slice and its pair isomorphism, and their cycle pull–push/outer-image formulas. Move the generic degree proof out of the split example without duplication. Keep relative selection, general cycle products, and absolute Chow convolution distinct. | PROVED; FULL BUILD, 158 AXIOM REPORTS, NINE REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP34 | Relative/absolute products and their actual graph-cycle operations | CONSTRUCT / COMPARE | Construct the closed pair/triple inclusions for a separated structural base and injective deck forgetting. Identify graph/intersection image cycles, weighted graph assembly, and full finite-cycle right-pullback/slice-pull–push squares. Reuse canonical cycle maps via isomorphism transport; keep principal-divisor descent and arbitrary intersection products separate. | PROVED; FULL BUILD, 176 AXIOM REPORTS, TEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP35 | Actual signed local divisor coefficients and isomorphism transport | CONSTRUCT / COMPARE | Reuse the length-defined fraction-field order; prove finite local lengths, signed laws and ring/field transport. Construct actual generic-point function-field transport and one-dimensional-stalk point equivalences, then prove local coefficient invariance. Keep closed support identification, finite support, grading and divisor assembly separate. | PROVED; FULL BUILD, 200 AXIOM REPORTS, ELEVEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP36 | Actual reduced point closures, prime supports and coefficient transport | CONSTRUCT / IDENTIFY | Prove points equivalent to the existing integral ideal-sheaf subschemes; identify chain codimension with ambient stalk dimension. Restrict to prime divisors, prove transport is the existing ideal image and reuse the local order on supports. Keep finite support, grading and divisor assembly separate. | PROVED; FULL BUILD, 227 AXIOM REPORTS, THIRTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP37 | Local finiteness of actual prime supports and quasi-compact finite coefficients | PROVE / CONNECT | Bound affine nonzero coefficients by finite height-one numerator/denominator loci; construct the actual fraction and unit-germ comparison. Pass from generic points to closed-support families and use quasi-compactness for finite support. Keep finite-cycle assembly and Chow grading separate. | PROVED; FULL BUILD, 239 AXIOM REPORTS, FIFTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP38 | Actual finite principal-divisor cycles and their geometric isomorphism laws | ASSEMBLE / CONNECT | Embed the proved finite prime coefficients into the existing integral cycle module; prove exact coefficients/support and product/inverse/quotient laws; bundle the homomorphism. Prove actual support reindexing and compatibility with existing pushforward/open restriction through isomorphisms. Keep grading and Chow relations separate. | PROVED; FULL BUILD, 259 AXIOM REPORTS, SEVENTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP39 | Explicit dimension functions, homogeneous cycle degrees and principal-divisor images | CONSTRUCT / GRADE | Retain both dimension-function conditions; prove prime support degree drop and actual closed-immersion restriction. Use supported submodules of the existing cycles and prove principal-divisor homogeneity, including ambient closed images. Keep geometric dimension-function instantiation and genuine relations separate. | PROVED; FULL BUILD, 281 AXIOM REPORTS, SIXTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP40 | Genuine principal relations, finite-sum source parity and closed-pushforward quotient descent | GENERATE / DESCEND | Use actual degree-\(n+1\) carriers and their actual function fields on Noetherian schemes with explicit dimension function. Prove carrier-family finite/local-finite parity and the unweighted finite-sum criterion. Transport generators through actual closed images, derive quotient pushforward and isomorphism equivalence using the existing cycle maps. | PROVED; FULL BUILD, 321 AXIOM REPORTS, TWENTY-TWO REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP41 | Actual support dimensions, finite-type dimension bounds and a canonical low-dimensional grading | IDENTIFY / INSTANTIATE | Identify actual carrier dimension with point height. Prove finite dimension for finite-type algebras and schemes over a field. Construct the canonical dimension function under dimension at most one, identify its carrier degrees, and instantiate it on the actual affine line. Keep the general finite-type one-step law and target codimension conversion open. | PROVED; FULL BUILD, 361 AXIOM REPORTS, TWENTY-TWO REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP42 | Strict transcendence-degree drop, exact affine dimension and actual carrier comparison | PROVE / IDENTIFY | Prove proper domain quotient drop and actual integral chain lifting. Combine the prime-chain upper bound with Noether normalization's lower bound to identify finite-type domain dimension with fraction-field transcendence degree. Connect prime quotients and actual residue fields to existing reduced carriers. Keep uniform chains, the immediate-specialization unit step and general scheme grading open. | PROVED; FULL BUILD, 386 AXIOM REPORTS, TWENTY-THREE REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP43 | Polynomial maximal height and actual closed-point local dimension | PROVE / IDENTIFY | Construct actual prime extension and its strict step below a maximal ideal. Combine Jacobson contraction with SP42's independent upper bound to prove every polynomial maximal ideal has height n and identify actual localization/stalk dimension and scheme-point coheight. Keep general finite-type-domain maximal-local comparison, uniform chains and unit-step grading separate. | PROVED; FULL BUILD, 398 AXIOM REPORTS, SIXTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP44 | Normal-base going down and finite-type-domain maximal-local dimensions | PROVE / CONNECT | Construct ideal-controlled annihilators, prove the monic coefficient comparison and normal-base cancellation, and construct primes below the selected terminal prime. Reuse the existing height bound to compare normalization heights and actual maximal-local/stalk dimensions. Keep saturated-chain uniformity and the higher-dimensional unit-step grading separate. | PROVED; FULL BUILD, 413 AXIOM REPORTS, NINETEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP45 | Actual residue-normalization localization and its maximal extended prime | CONSTRUCT / CONNECT | Lift the actual quotient normalization, localize at its nonzero polynomial denominators, and construct the compatible finite-type fraction-field algebra. Prove maximality, exact contraction and preserved height, then reuse SP44 for the domain generic-fiber transcendence-degree endpoint. | PROVED; FULL BUILD, 437 AXIOM REPORTS, NINETEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP46 | Original-field prime dimension formula for finite-type domains | PROVE / CONNECT | Prove actual localization preserves full cardinal transcendence degree, use the compatible polynomial fraction-field tower, and combine SP45 with quotient normalization. Retain the domain condition and actual quotient, residue-field and prime-localization carriers. | PROVED; FULL BUILD, 446 AXIOM REPORTS, FOURTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP47 | Consecutive-prime quotient and residue-field unit drop | PROVE / CONNECT | Transport the actual prime interval into B/p, prove height one of the image of q, and apply SP46 with the actual double-quotient algebra equivalence. Keep the ambient algebra arbitrary and the cover relation in the prime spectrum. | PROVED; FULL BUILD, 452 AXIOM REPORTS, ELEVEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP48 | Actual affine dimension functions and geometric support degrees | CONSTRUCT / IDENTIFY | Reuse the prime/scheme order reversal and SP47 to prove both dimension-function laws on literal Spec A. Extract the finite-type sections algebra from an actual affine structural morphism and transport through X.isoSpec. Identify support degrees and fundamental-cycle membership with carrier dimension. | PROVED; FULL BUILD, 464 AXIOM REPORTS, NINETEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP49 | Structural base actions and actual affine residue-field algebra comparison | CONSTRUCT / COMPARE | Define the action independently by structural pullback and evaluation. Prove actual residue-map base compatibility, open-immersion algebra equivalence and the stalk-induced affine comparison on constants. Identify full residue-degree cardinals and the existing literal-spectrum dimension value. | PROVED; FULL BUILD, 480 AXIOM REPORTS, NINETEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP50 | Structural residue-degree values on arbitrary affine schemes | IDENTIFY / COMPARE | Extract the actual finite-type sections algebra and retain its structural-map equality. Use the canonical affine isomorphism and SP49's base-compatible residue map to prove finiteness and identify the existing dimension value, then compare values under affine open immersions. Reuse the exposed point-height isomorphism theorem. | PROVED; FULL BUILD, 484 AXIOM REPORTS, THIRTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP51 | Pointwise residue degrees and affine-chart value agreement | PROVE / COMPARE | Use one actual affine-cover preimage to prove finite structural residue degree on a general locally finite-type scheme. Compare each existing affine-chart value with its ambient residue degree, and compare two chart values at equal actual ambient images. | PROVED; FULL BUILD, 487 AXIOM REPORTS, TEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP52 | Global structural residue-degree dimension function | CONSTRUCT / COMPARE | Put specialization pairs in a common actual affine open, transfer strictness and the cover law, and construct the global function. Prove nonnegativity, equality with the existing affine object and value compatibility under arbitrary open immersions. Keep global height/carrier dimension and target codimension comparison separate. | PROVED; FULL BUILD, 493 AXIOM REPORTS, FOURTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP53 | Global point height and actual integral-carrier dimension | IDENTIFY / COMPARE | Bound height above by nonnegative strict grading and below by one actual affine chart. Identify the global function with finite height and actual point-closure dimension; derive carrier-degree and fundamental-cycle criteria and qualified open-height invariance. Keep integral codimension conversion separate. | PROVED; FULL BUILD, 500 AXIOM REPORTS, FOURTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |

SP18 validation: full Lean build, declaration/axiom verification, single-PDF
build, and independent mathematical/parity review passed. Detailed scope and
verification are recorded in `0008-split-span-cycle-realization.md`.
SP19 construction and scope are recorded in
`0009-split-span-additive-quotient.md`; the generators are finite indexed
decompositions, not a separately proved binary-only presentation.
SP19 validation: full Lean build, declaration/axiom checks, the empty-endpoint
test, independent review, and the single-PDF build passed.
SP20 construction and next cycle-group step are recorded in
`0010-split-integral-subschemes.md`.
SP20 validation: full build, direct algebra-companion build, declaration/axiom
checks, empty-ambient and no-curves tests, independent review, and single-PDF
build all passed.
SP21 construction and the next product/pull--push comparison are recorded in
`0011-split-zero-cycles.md`. Its verification record is maintained there.
SP22 construction and verification are recorded in
`0012-split-chow-composition.md`.
SP22 validation: full build, declaration/axiom checks, generic-point degree,
diagonal-flatness and proper-projection tests, empty-scheme and composition-order
regressions, independent mathematical/parity review, and the single-PDF build
and visual check all passed.
SP23 construction, exact source matching, and completed verification are recorded
in `0013-split-betti-cycle-class.md`.
SP23 validation: full build, declaration/axiom checks, empty-point/cohomology,
actual cocycle, empty/variable-fiber transfer, and point-action regressions,
independent mathematical/parity review, and the single-PDF build and visual
check all passed.
SP24 construction and the source-to-geometric degree-zero match are recorded
in `0014-split-hodge-tate-block.md`. Full build, integrated verification,
declaration/axiom checks, empty-label/orientation/universal-square regressions,
independent mathematical/parity review, and the single-PDF build and visual
check all passed.
SP25 construction, source convention, and verification status are recorded
in `0015-split-galois-marked-comparison.md`. Direct and full builds,
integrated verification, 24 standard-only axiom reports, nonnormal-subgroup
and empty-complement regressions, sign/orientation/full-action/Palomar checks,
source/parity review, and the single-PDF build and visual review all pass.

SP26 design, exact source obligations, and completed verification are recorded
in `0016-source-input-packages.md`. The new Prop classes are selected local
premises, not a blanket literature assumption or proofs of complete Stacks
theorems. Existing consumers retain their own explicit hypotheses.
Full build (3028 jobs), integrated verification without warnings, the
99-report standard-axiom allowlist audit (22 new reports), no-automatic-instance
and nonzero-boundary-defect regressions, unchanged submission-wrapper checks,
source/parity review, and the single-PDF build and visual review pass.

SP30 validation (2026-09-14): full Lean build (3029 jobs; only the two
existing `Challenge` warnings), integrated verification without warnings or
errors, and all 114 axiom reports pass the standard-three allowlist. The
14 new reports and five graph regressions cover the actual diagonal,
existing graph-span orientation, closed-subscheme identification, restriction
without a deck-extension premise, and the explicitly conditional action lift.
The six proof-dependency assertions, independent mathematical review, and
single-PDF build (32 pages, clean final log) pass; the title/abstract and graph
proposition pages were visually checked. No new literature input or projector
was added. The next step remains the actual Chow-cycle interface in
`../TARGET_BRIDGE.md` §6.

SP31 validation (2026-09-14): all four new leaf modules and the split
specialization build pass, followed by the full 3033-job build (only the two
existing `Challenge` warnings). Integrated verification passes without
warnings or errors; all 129 reports use only the permitted three axioms.
The 15 new reports and six regressions check canonical split types and point
generators, empty-open restriction, composition order, signed coefficients,
and graph restriction without a deck-extension premise. The six existing
proof-dependency assertions, independent mathematical/source review, and
the 33-page single-PDF build pass; the title/abstract and cycle-definition
and proposition pages were visually inspected. No new source hypothesis,
projector, Chow quotient, or cycle multiplication was introduced.

SP32 validation (2026-09-14): both new leaf modules and the full 3035-job
build pass, with only the two existing `Challenge` warnings. Integrated
verification passes without warnings or errors; all 139 axiom reports use
only `propext`, `Classical.choice`, and `Quot.sound`. The ten new reports
and seven regressions check noncommutative composition order, both units,
the separated-only image theorem, properness of the support projection,
intersection integrality/dimension, actual ambient-stalk multiplicity, and
the degree-one residue map of the constructed isomorphism. The latter
reuses the existing generic theorem rather than duplicating it. All six
proof-dependency assertions and the independent mathematical/parity review
pass. The single PDF builds to 34 pages with a clean final log; title,
cycle/multiplicity, and composition-proposition pages were visually checked.
Submission wrappers and dependency pins are unchanged. No new source input,
projector, cycle product, or rational-equivalence relation was introduced.

SP33 validation (2026-09-14): all five new leaf modules, the updated
split-point compatibility adapter and its realization consumers, and the
full 3040-job build pass. Only the two existing `Challenge` warnings remain.
Integrated verification passes without warnings or errors, and all 158
axiom reports use only the permitted three axioms. The 19 new reports and
nine regressions cover closed pushforward identity/composition, signed
coefficients, actual slice inverse image, étale openness without finiteness,
absence of an assumed integral pair product, right-multiplication order,
supportwise outer image without ambient properness, and weighted graph
assembly. All six proof-dependency assertions and the independent
mathematical/parity review pass. The 35-page single PDF has a clean final
log; the new pushforward paragraph, Proposition 6.6, and status pages were
visually inspected. Submission wrappers and dependency pins are unchanged.
No new source hypothesis, projector, Chow quotient, or ambient cycle product
was introduced.

SP34 validation (2026-09-14): all five new leaf modules and the full
3045-job build pass, with only the two existing `Challenge` warnings.
Integrated verification passes without warnings or errors; all 176 axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
18 new reports and ten regressions cover minimal separated-base hypotheses,
retained automorphism order, signed graph pushforward, actual intersection
cycles, both full-cycle comparison squares, arbitrary rational graph sums,
the literal `Spec k` target, and absence of an inferred étale composite.
All six proof-dependency assertions and two supporting reports pass.
Independent mathematical and Lean/TeX/ledger parity reviews pass. The
single PDF builds to 37 pages with a clean final log; Proposition 6.7 and
the surrounding proof/status pages were visually inspected. Submission
wrappers and dependency pins are unchanged, and the diff check is clean.
No new source hypothesis, projector, quotient, or cycle product was added.

SP35 validation (2026-09-14): all five new leaf modules and the full
3074-job Lean build pass; only the two existing `Challenge` warnings remain.
Integrated verification passes without warnings or errors. All 200 axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
24 new reports and eleven regressions cover actual quotient-length
transport, product/inverse signs, vanishing on base-ring units, the actual
field/stalk square, point transport without integral/Noetherian assumptions,
the affine height-one constructor, coefficient invariance without normality
or DVR assumptions, and its application to the existing closed
support-to-image isomorphism. The computed integer-ring example proves
orders of `2` and `1/2` equal to `1` and `−1`, without a normalization
premise. All six proof-dependency assertions and two supporting reports
pass. Independent mathematical/source/parity review passes. The 38-page
single PDF builds with a clean final log; Proposition 6.8 and its surrounding
proof/status pages were visually inspected. Submission wrappers and
dependency pins are unchanged, and the diff check passes. No new source
hypothesis, projector, valuation inequality, divisor cycle, or relation
package was introduced. SP36 supplies the subsequent closed support
identification, SP37 supplies finite support, and SP38 assembles the
finite divisor cycle.

SP36 validation (2026-09-14): the three new leaf modules and the full
3077-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with all 100 examples and
no warnings or errors. All 227 selected axiom reports were checked against
the allowlist: only `propext`, `Classical.choice`, and `Quot.sound` occur.
The complete inventory check combines the integrated output with an
imported-declaration-only capture; the locally declared verification
regression is checked in its original integrated context. The 27 new
reports, six declaration checks and thirteen new regressions cover actual
point closures with no ambient assumptions,
both inverse identifications, genuine chain codimension, the affine
height-one support, signed existing-cycle pushforward, actual image ideals,
reuse of the existing order, field/support variance and inverse signs,
supportwise rather than global properness, transport naturality, and the
empty scheme. All six proof-dependency assertions and two supporting
reports pass. Independent mathematical/source/parity review passes. The
single PDF builds to 39 pages with a clean final log; Proposition 6.9 and
the adjacent module map were visually inspected. Submission wrappers and
dependency pins are unchanged, and the diff check passes. No new axiom,
source hypothesis, cycle module, projector, principal-divisor cycle, or
relation package was added. SP37 supplies the subsequent local finiteness
and quasi-compact finite-support step; SP38 supplies finite ungraded
divisor assembly. SP39 adds homogeneous degrees for an explicit dimension
function; its geometric instantiation and Chow relations remain separate.

SP37 validation (2026-09-14): all three new leaf modules and the full
3080-job Lean build pass; only the two existing `Challenge` warnings
remain. Integrated `research/Verification.lean` passes with all 115
examples. All 239 axiom reports were captured in their original integrated
context and checked against the allowlist; only `propext`,
`Classical.choice`, and `Quot.sound` occur, with no warnings or errors.
The twelve new reports, six declaration checks and fifteen new regressions
cover domain-only minimality, arbitrary-dimensional Noetherian finiteness,
actual affine fractions without Noetherianity, stalk compatibility, unit
germs without ambient integrality, the coefficient-zero implication
without normality or DVRs, affine and closed-support local finiteness
without compactness, empty affine charts, quasi-compact global support,
automatic compactness for globally Noetherian schemes, inverse signs,
empty support for one, and cancellation-compatible product support.
All six proof-dependency assertions and two supporting reports pass.
Independent mathematical/source/parity review passes. The single PDF
builds to 40 pages with a clean final log; Proposition 6.10 and the adjacent
module/status map were visually inspected. Submission wrappers and
dependency pins are unchanged, and the diff check passes. No new axiom,
source hypothesis, coefficient function, cycle module, projector,
principal-divisor cycle or relation package was introduced in SP37.
SP38 supplies finite ungraded principal-divisor assembly and its
product/isomorphism laws; dimension-function grading and
rational-equivalence descent follow.

SP38 validation (2026-09-14): both new leaf modules, the extended
isomorphism-transport module, and the full 3082-job Lean build pass.
Only the two existing `Challenge` warnings remain in the full build.
Integrated `research/Verification.lean` passes with all 132 examples and
no warnings or errors. All 259 selected axiom reports were captured in
their original integrated context and checked against both the exact
declaration inventory and the allowlist; only `propext`,
`Classical.choice`, and `Quot.sound` occur. The twenty new reports,
seven declaration checks and seventeen new regressions cover actual
prime and nonprime coefficients, exact support, the coefficientwise zero
criterion, signed product/inverse/quotient laws and cancellation, the
bundled homomorphism, actual inverse support images, arbitrary-semiring
coefficient transport without ambient integrality or Noetherianity,
both principal-divisor variances, and the existing closed support-to-image
isomorphism. The final regression derives the image hypotheses and checks
that neither global closedness nor properness of the ambient morphism is
available. All six proof-dependency assertions and two supporting reports
pass. Independent mathematical/source/parity review passes. The single
PDF builds to 41 pages with a clean final log; Proposition 6.11 and the
adjacent proof, module map and status pages were visually inspected.
Submission wrappers and dependency pins are unchanged, and the diff
check passes. No new axiom, source hypothesis, projector, cycle module,
dimension-function grading or relation package is introduced. The new
principal divisor is an element of the existing cycle module. Compatible
grading for an explicit dimension function is supplied in SP39; its
geometric instantiation and genuine rational-equivalence descent remain.

SP39 validation (2026-09-14): all four new leaf modules and the full
3086-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with all 148 examples and
no warnings or errors. All 281 axiom reports were captured in their
original integrated context and compared against the complete declaration
inventory and the allowlist; only `propext`, `Classical.choice`, and
`Quot.sound` occur. The twenty-two new reports, eight declaration checks
and sixteen new regressions cover both dimension-function conditions,
prime immediate specialization and degree drop without Noetherianity,
actual closed restriction with identity/composition and support-image
degree compatibility, supported submodules of the original cycle type,
distinct degrees, trivial coefficients and the nontrivial-coefficient
fundamental-cycle converse, principal homogeneity, and ambient closed
carrier images without ambient integrality, Noetherianity or compactness.
The regression suite constructs the constant-zero dimension function and
an actual point on the spectrum of a field, and also checks the image
degree formula when only the support composite is closed. All six
proof-dependency assertions and two supporting reports pass. Independent
mathematical/source/parity review passes. The single PDF builds to 42
pages with a clean final log; Proposition 6.12 and the adjacent proof,
module map and status pages were visually inspected. Submission wrappers
and dependency pins are unchanged; the diff check passes. No new axiom,
projector, free cycle type, relation package or Chow quotient is introduced.
The dimension function is explicit data satisfying its standard two
conditions, not a postulated universal existence theorem. The next
construction is genuine relation generation and quotient descent, with
geometric dimension-function instantiation kept separate.

SP40 validation (2026-09-14): all five new leaf modules and the full
3091-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with all 170 examples and
no warnings or errors. All 321 selected axiom reports were captured in
their original integrated context and compared with the exact declaration
inventory: no missing, unexpected or duplicate reports, and only `propext`,
`Classical.choice`, and `Quot.sound` occur. The forty new reports, ten
declaration checks and twenty-two new regressions also pass independently.
They cover derived closed-carrier finiteness; literal ambient principal
cycles and multiplicative laws; local-finite carrier families; homogeneous
generators and negative function powers; the unweighted finite-list
criterion; genuine rational equivalence and quotient equality/kernel;
representative surjectivity; actual closed-image carriers and generator
transport; proved submodule preservation; canonical restricted-degree
quotient pushforward with identity/composition; and quotient isomorphisms
whose inverse cycle map is the existing open restriction. In particular,
an infinitely repeated nonempty carrier with zero principal cycle is
proved not locally finite as a carrier family. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical and manuscript/source/parity audits pass. The single PDF
builds to 44 pages with a clean final log; Proposition 6.13, its proof,
adjacent module/status pages and the updated theorem-map page were
visually inspected. Submission wrappers and dependency pins are unchanged;
the diff check passes. No new axiom, source-input package, cycle module
or projector is introduced. The new integral quotient is constructed from
actual relations, and their preservation is proved rather than assumed.
The intended geometric dimension function and grading, general rational
coefficient comparison, arbitrary open/proper/flat/Gysin descent, Chow
convolution and target realization remain separate constructions.

SP41 validation (2026-09-15): all five new leaf modules and the full
3099-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with all 192 examples and
no warnings or errors. All 361 selected axiom reports were captured in
their original integrated context and compared with the exact declaration
inventory: no missing, unexpected or duplicate reports. The recursive
`polynomialDimensionBound` definition has no axioms; the other 360 reports
use only `propext`, `Classical.choice`, and `Quot.sound`. The forty new
reports, eight declaration checks and twenty-two new regressions also
pass independently. They cover actual carrier dimension and point height;
finite polynomial-presentation bounds, including trivial quotients;
finite-dimensional finite-type schemes via their structural morphisms and
finite affine covers; both proved dimension-function laws in dimension at
most one; actual carrier degrees and coefficient-one cycle membership;
the existing Chow quotient with that constructed grading; and the actual
affine line with generic degree one and origin degree zero. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical/source/parity review passes. The single PDF builds to 46 pages
with a clean final log; Proposition 6.14, its proof and the adjacent
module/status pages were visually inspected. Submission wrappers and dependency pins are
unchanged; the diff check passes. No new axiom, source-input package, cycle
module or projector is introduced. This completes the first geometric-
grading subcheckpoint: finite-type finite-dimensionality is general, but
the constructed dimension function is currently restricted to dimension
at most one. The higher-dimensional immediate-specialization unit-step
law, transcendence-degree comparison, pure-dimensional codimension
conversion, general rational coefficient extension, Chow operations and
target realization remain separate constructions.

SP42 validation (2026-09-15): all five new leaf modules and the full
3106-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with all 215 examples and
no warnings or errors. All 386 selected axiom reports were captured in
their original integrated context and compared with the exact declaration
inventory: no missing, unexpected or duplicate reports. The existing
`polynomialDimensionBound` definition has no axioms; the other 385 reports
use only `propext`, `Classical.choice`, and `Quot.sound`. All twenty-five
new public theorems, eight declaration checks and twenty-three new
regressions pass independently as well. These include the actual evaluation
map k[T] to k; proper prime quotients with no ambient domain assumption;
actual length-preserving integral prime-chain lifts; finite field
extensions; the noninjective integral map to the unit-ideal quotient;
actual polynomial normalization and its separate hypotheses; the sharp
finite-type domain and fraction-field dimension equalities; actual affine
three-space of dimension three; and actual prime-localization residue
fields and reduced carriers, including every existing integral closed
carrier via its ambient generic point. The six primary proof-dependency
assertions and two supporting reports pass. Independent mathematical,
type-order and manuscript/source/parity audits pass. The single PDF builds
to 47 pages with a clean final log; Proposition 6.15, its proof, adjacent
module/status pages and the updated theorem-map page were visually
inspected. Submission wrappers and dependency pins are unchanged; the diff
check passes. No new axiom, source-input package, cycle module, Chow quotient
or projector is introduced. The dimension equalities and strict drop are
proved, not supplied. Uniform maximal chains, maximal-local dimension,
the higher-dimensional immediate-specialization unit step, scheme-chart
transport, general grading and the remaining target constructions stay open.

SP43 validation (2026-09-15): all three new leaf modules and the full
3109-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 506 declaration checks
and all 231 examples, without warnings or errors. All 398 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports, and no unpermitted axioms. The existing `polynomialDimensionBound`
definition is axiom-free; the other 397 reports use only `propext`,
`Classical.choice`, and `Quot.sound`. An independent focused run checks
all twelve new public declarations, six declaration checks and sixteen
regressions, including arbitrary coefficient rings for prime extension,
absence of Jacobson/domain requirements for the strict step, arbitrary
field characteristic, zero variables, actual three-variable maximal
ideals and the evaluation-kernel point, actual localizations and stalks,
and scheme height zero versus coheight n at closed points. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical and source/manuscript parity audits pass; the induction's
upper bound is independent of the new maximal-height result. The single
PDF builds to 48 pages with a clean final log. Proposition 6.16 and its
proof, the updated module/status pages and theorem-map row were visually
inspected. Submission wrappers, dependency pins and bibliography are
unchanged; diff checks pass. No new axiom, input package, cycle type,
Chow quotient or projector is introduced. The next algebraic checkpoint
is normal-base going down for the actual integral domain extension from
Noether normalization, reusing the existing generic height comparison.
Polynomial-base normality is already available. General finite-type-domain
maximal-local equality, uniform chains, the higher-dimensional unit-step
law and target realization remain subsequent proof obligations.

SP44 validation (2026-09-15): all five new leaf modules and the full
3114-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 521 declaration checks
and all 250 examples, without warnings or errors. All 413 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports and no unpermitted axioms. The existing `polynomialDimensionBound`
is axiom-free; the other 412 reports use only `propext`, `Classical.choice`,
and `Quot.sound`. The independent SP44 replay covers all fifteen new public
theorems, fifteen checks and nineteen regressions. These include
ideal-controlled annihilators without domain, Noetherian or global
module-finiteness assumptions; prime-coefficient descent over arbitrary
coefficient rings; normal-base going down without target normality or
finiteness; weak-order prime lifting and a finite chain ending at the
prescribed terminal prime; the generic height comparison without domain
hypotheses; an actual normalization without a finite-type premise on the
upper domain; the full finite-type-domain maximal-local and actual-stalk
endpoints without normality or characteristic-zero premises; scheme
coheight versus closed-point height zero; polynomial and zero-variable
consistency; and the actual integral noninjective evaluation map k[T] to k,
for which going down is proved to fail. The six primary proof-dependency
assertions and two supporting reports pass. Independent mathematical,
source and manuscript/parity audits pass. The single PDF builds to 49 pages
with a clean final log; Proposition 6.17, its proof, module/status pages and
theorem-map row were visually inspected. The exact normal-base source
00H8 is cited, and the existing 00P0 citation now covers the maximal-local
conclusion as well. Submission wrappers and dependency pins are unchanged;
diff checks pass. No new axiom, literature-input package, global going-down
instance, cycle type, Chow quotient or projector is introduced. The next
bounded construction is the actual residue-normalization localization
described in the gap map, before the arbitrary-prime dimension formula and
higher-dimensional immediate-specialization unit-step law.

SP45 validation (2026-09-15): all four new leaf modules and the full
3118-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 545 declaration checks
and all 269 examples, without warnings or errors. All 437 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports and no unpermitted axioms. The existing `polynomialDimensionBound`
is axiom-free; `genericFiber_isScalarTower_base` uses only `propext` and
`Quot.sound`; the other 435 reports use only `propext`, `Classical.choice`
and `Quot.sound`. The independent SP45 replay checks all 24 new public
declarations and nineteen regressions. These cover the exact quotient lift
without primality or domain assumptions, zero variables, denominator
disjointness, the canonical fraction-ring algebra and compatible scalar
towers, finite type without domain assumptions, domain and injection
conclusions, contraction and full height without integrality, maximality
without ambient domain or Noetherian assumptions, the actual non-domain
example \(K\times K\), constructed normalization/localization existence,
and the domain-only transcendence-degree consumer without normality or
characteristic-zero assumptions. The six primary proof-dependency
assertions and two supporting reports pass. Independent mathematical,
source and manuscript/parity reviews pass. The single PDF builds to 50
pages with a clean final log; Proposition 6.18 and its proof, the updated
module/status page and theorem-map row were visually inspected. The exact
quotient-localization and integral-domain-over-field sources 00CT and 00GS
are cited, without adding source axioms. Submission wrappers and dependency
pins are unchanged; diff checks pass. No replacement localization carrier,
global algebra instance, input package, cycle space, Chow quotient or
projector is introduced. The next bounded algebraic checkpoint is the
actual localization/tower transcendence-degree comparison over the original
field for a finite-type domain, before the consecutive-prime unit step and
scheme/target grading.

SP46 validation (2026-09-15): both new leaf modules and the full 3120-job
Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 554 declaration checks
and all 283 examples, without warnings or errors. All 446 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports and no unpermitted axioms. The existing `polynomialDimensionBound`
is axiom-free; the existing `genericFiber_isScalarTower_base` uses only
`propext` and `Quot.sound`; the other 444 reports use only `propext`,
`Classical.choice` and `Quot.sound`. The independent SP46 replay checks
all nine new public declarations and fourteen regressions. These include
actual localization invariance across independent universes without finite
type, a genuinely infinite transcendence-degree example, the canonical
polynomial generic-fiber sum without an integrality premise, all six
prime/height/residue/localization interfaces, zero and maximal prime
consistency, an actual positive-height nonmaximal prime in \(k[X][Y]\),
and the zero-variable case. The six primary proof-dependency assertions
and two supporting reports pass. Independent mathematical, scalar/universe,
source and manuscript/parity reviews pass. The single PDF builds to 51
pages with a clean final log; Proposition 6.19 and its proof, the updated
module/status pages and theorem-map row were visually inspected. The exact
030H tower source and the domain specialization of 00P1 are cited without
source axioms or a claim to the source's broader reducible statement.
Submission wrappers and dependency pins are unchanged; diff checks pass.
No new carrier, residue-field model, global algebra instance, input package,
cycle space, Chow quotient or projector is introduced. The next bounded
checkpoint uses the actual quotient spectrum of \(B/p\) to prove the
consecutive-prime unit drop, with the cover relation in `PrimeSpectrum B`,
not the full ideal lattice. Scheme-chart transport and general target
grading remain subsequent proof obligations.

SP47 validation (2026-09-15): both new leaf modules and the full 3122-job
Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 560 declaration checks
and all 294 examples, without warnings or errors. All 452 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports and no unpermitted axioms. The existing `polynomialDimensionBound`
is axiom-free; the existing `genericFiber_isScalarTower_base` uses only
`propext` and `Quot.sound`; the other 450 reports use only `propext`,
`Classical.choice` and `Quot.sound`. The independent SP47 replay checks
all six new public declarations and eleven regressions. These cover actual
quotient primality and contraction without ambient domain or Noetherian
assumptions, transport of a prime-spectrum cover, prime and ordinary height
one, all three unit-drop interfaces and their strict direction. A concrete
cover in the reducible algebra \(k[T]\times k\) satisfies the unit law;
the actual intermediate ideal \((T^2)\) separately confirms that the
prime cover \((0)\subsetneq(T)\) need not be a cover in the full ideal
lattice. The six primary proof-dependency assertions and two supporting
reports pass. Independent mathematical, source and manuscript/parity
reviews pass. The single PDF builds to 52 pages with a clean final log;
Proposition 6.20 and its proof, the updated module/status pages and the
theorem-map row were visually inspected. The existing 0A21 citation is
reused for its affine unit-drop statement, without source axioms or an
ambient stalk-dimension increment claim on arbitrary reducible algebras.
Submission wrappers, dependency pins and bibliography are unchanged; diff
checks pass. No replacement carrier, global algebra instance, input package,
cycle space, Chow quotient or projector is introduced. The next bounded
checkpoint packages the proved laws as an actual affine `DimensionFunction`
using the existing prime/scheme order reversal. General scheme-chart and
residue-field transport, target codimension grading and realization remain
subsequent proof obligations.

SP48 validation (2026-09-15): both new leaf modules and the full 3124-job
Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 572 declaration checks
and all 313 examples, without warnings or errors. All 464 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate
reports and no unpermitted axioms. The existing `polynomialDimensionBound`
is axiom-free; the existing `genericFiber_isScalarTower_base` uses only
`propext` and `Quot.sound`; the other 462 reports use only `propext`,
`Classical.choice` and `Quot.sound`. The independent SP48 replay, with
exactly the original four verification imports, checks all eleven new
public declarations and the reused, newly public `specPointOrderIso`.
Its nineteen regressions cover actual order reversal, strictness and
the unit step, literal prime-residue-field values and finite point heights,
both carrier-degree and fundamental-cycle criteria, the empty spectrum of
the zero algebra, a reducible product algebra, generic and arbitrary closed
points of polynomial spectra in every dimension, and agreement with the
existing low-dimensional construction. Structural-affine tests require no
preinstalled sections algebra and compare the two constructors' intrinsic
values. Separate actual-isomorphism height and affine-source audits pass.
The six primary proof-dependency assertions and two supporting reports pass.
Independent mathematical, source and cross-document parity reviews pass.
The single PDF builds to 53 pages with a clean final log; Proposition 6.21
and its proof, the updated module/status pages and the theorem-map row were
visually inspected. The existing 02I9 and 0A21 citations are reused without
source axioms. Submission wrappers, dependency pins and bibliography are
unchanged; diff checks pass. The existing point-order comparison, dimension
function, support objects and homogeneous cycle module are reused; no new
source input package, global algebra instance, Chow quotient or projector
is introduced. The next bounded checkpoint is the structural-field action
on actual scheme residue fields and its compatible affine algebra
equivalence. Open-chart compatibility, global dimension-function assembly,
target codimension grading and realization remain subsequent obligations.

SP49 validation (2026-09-15): all three new leaf modules and the full
3127-job Lean build pass, with only the two existing `Challenge` warnings.
Integrated `research/Verification.lean` passes with 588 declaration checks
and all 332 examples, without warnings or errors. All 480 selected axiom
reports were captured in the original integrated context and compared with
the exact declaration inventory: no missing, unexpected or duplicate reports
and no unpermitted axioms. The existing `polynomialDimensionBound` is
axiom-free; the existing `genericFiber_isScalarTower_base` uses only
`propext` and `Quot.sound`; the other 478 reports use only `propext`,
`Classical.choice` and `Quot.sound`. The independent SP49 replay retains
exactly the original four verification imports and checks all sixteen new
public declarations and nineteen regressions. These cover the literal
structural base action, actual residue-map compatibility, identity and
composition, open-immersion equivalences and their inverses, the affine
stalk-induced comparison on constants, the nonreduced algebra
`ZMod 4` over the integers, and the empty spectrum of `PUnit`. Full-cardinal
comparison is tested without finite-type assumptions, including the actual
scheme residue field at the zero prime of a polynomial algebra on countably
many variables, whose transcendence degree is `aleph0`. The finite-type
regressions check finiteness and the existing literal-spectrum dimension
value without a domain hypothesis. A separate affine-leaf audit passes
with four axiom reports and six regressions. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical, source and cross-document parity reviews pass.
The single PDF builds to 55 pages with a clean final log; Proposition 6.22
and its proof, the updated module/status pages and the theorem-map row were
visually inspected. The 01HB and 01HV citations are added for the actual
scheme residue-field and affine-stalk definitions and comparisons; the
existing 0A21 citation is reused. Scalar compatibility is proved directly,
not supplied as a source axiom. Submission wrappers and dependency pins
are unchanged; diff checks pass. The structural action is defined
independently of the affine equivalence and installed only locally; no
global algebra instance, source input package, replacement carrier, Chow
quotient or projector is introduced. The next bounded checkpoint compares
the existing dimension function on an arbitrary affine structural scheme
with its actual residue-field degree. Overlapping-chart comparisons,
global dimension-function assembly, target codimension grading and
realization remain subsequent obligations.

SP50 validation (2026-09-15): both affected leaf modules and the full
3128-job Lean build pass, with only the two existing `Challenge` warnings.
The final integrated `research/Verification.lean` run passes with 592
declaration checks and all 345 examples, without warnings or errors.
All 484 selected axiom reports were captured in the original integrated
context and compared with the exact declaration inventory: no missing,
unexpected or duplicate reports and no unpermitted axioms. The existing
`polynomialDimensionBound` is axiom-free; the existing
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 482 reports use only `propext`, `Classical.choice` and
`Quot.sound`. The independent focused replay retains exactly the original
four verification imports and checks the three new public endpoints and
the reused, newly public `point_height_iso`. All thirteen new regressions
pass: arbitrary scheme-isomorphism height, absence of preinstalled sections
and residue algebras or integrality/reducedness/characteristic-zero inputs,
the affine-X degree formula, agreement with the literal-spectrum function,
actual `isoSpec` compatibility on constants, affine open maps and actual
open-subscheme inclusions and composition, the empty spectrum, a product
algebra and the dual-number quotient, the existing support-degree criterion
and low-dimensional grading parity. A separate four-report, six-regression
audit also passes; it checks exact cardinal recovery from `toNat` using
the proved finiteness and confirms that neither finite type nor module
finiteness of the residue field is supplied. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical, structural-action and cross-document parity reviews pass.
The single PDF builds to 55 pages with a clean final log; Proposition 6.23
and its proof, the updated module/status pages and the theorem-map row
were visually inspected. Existing 0A21 and 01HV sources are rechecked and
reused without source axioms. Submission wrappers, dependency pins and
bibliography are unchanged; diff checks pass. The existing dimension
function, structural algebra and point-height isomorphism theorem are
reused; no global algebra instance, input package, duplicate order or
residue carrier, cycle module, Chow quotient or projector is introduced.
The next bounded checkpoint is pointwise residue-degree finiteness and
affine-chart value comparison in a general locally finite-type ambient
scheme. Common-chart order and cover-law transfer, global grading,
target codimension conversion and realization remain subsequent obligations.

SP51 validation (2026-09-15): the new leaf module and the full 3129-job
Lean build pass, with only the two existing `Challenge` warnings.
The final integrated `research/Verification.lean` run passes with 595
declaration checks and all 355 examples, without warnings or errors.
All 487 selected axiom reports were captured in the original integrated
context and compared with the exact declaration inventory: no missing,
unexpected or duplicate reports and no unpermitted axioms. The existing
`polynomialDimensionBound` is axiom-free; the existing
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 485 reports use only `propext`, `Classical.choice` and
`Quot.sound`. The independent focused replay retains exactly the original
four verification imports and checks all three new public endpoints and
ten regressions. These cover the absence of ambient affine, compact,
Noetherian, integral or preinstalled-algebra premises; exact cardinal
recovery from the proved finite degree; the actual ambient residue-degree
comparison; canonical affine-cover maps and exact preimages; two chart
maps with equal images; actual affine open subsets at a common point;
identity-chart parity; the empty scheme; and an affine-line example
showing that the equal-image condition cannot simply be omitted.
An independent scratch diagnostic constructs the actual countable
coproduct of copies of `Spec k`, proves its structural map locally of
finite type, proves that its source is neither quasi-compact nor affine,
and applies the new pointwise theorem. Its two examples pass, and all four
selected axiom reports (the three public endpoints and the noncompactness
proof) contain only the standard three axioms. This independent diagnostic
is separate from the integrated example count. The six primary
proof-dependency assertions and two supporting reports pass. Independent
mathematical, structural-action and cross-document parity reviews pass.
The single PDF builds to 56 pages with a clean final log; Proposition 6.24
and its proof, the updated module/status pages and the theorem-map row
were visually inspected. The existing 0A21 source is rechecked and reused
without a source axiom. Submission wrappers, dependency pins and
bibliography are unchanged; diff checks pass. No new global algebra
instance, input package, residue carrier, point order, dimension-function
object, cycle module, Chow quotient or projector is introduced. The next
bounded checkpoint transfers specialization and cover relations into a
common actual affine chart and uses the proved value comparison to
construct the global dimension function. Target codimension conversion
and further realization remain separate obligations.

SP52 validation (2026-09-15): the new leaf module and the full 3130-job
Lean build pass, with only the two existing `Challenge` warnings.
The six primary proof-dependency assertions and two supporting reports
pass. An independent leaf-only replay checks all six public endpoints
and eight regressions without diagnostics; all six axiom reports contain
exactly `propext`, `Classical.choice` and `Quot.sound`. The replay includes
the actual open-scheme order comparison and the common-chart cover
reflection, both dimension-function laws, whole-object affine equality
and nonaffine open-value compatibility. Separate checked scratch lemmas
support the next checkpoint's upper height bound and actual chart-to-
ambient height monotonicity; the global height equality itself is not
part of SP52. Independent mathematical and cross-document parity reviews
pass. The single PDF builds to 56 pages with a clean final log;
Proposition 6.25 and its proof on page 27, the module/status pages 30--31
and the theorem-map row on page 49 were visually inspected. The existing
02I9 and 0A21 sources are rechecked and reused without source axioms.
Submission wrappers, dependency pins and bibliography are unchanged;
diff checks pass. The exact-original-four-import replay passes all six
public endpoint checks and fourteen new regressions without diagnostics;
its six axiom reports contain exactly the standard three. These cover
the absence of affine, compact, Noetherian, integral and preinstalled-
algebra premises; literal structural evaluation; both dimension laws and
geometric specialization orientation; nonnegativity; whole-object affine
and literal-spectrum parity; arbitrary open immersions and actual open
subsets; integration with existing support degree and prime-divisor
degree drop; the empty scheme; and the actual countable coproduct of
copies of `Spec k`, with its structural morphism locally of finite type
and its noncompactness and nonaffineness proved.
The final integrated `research/Verification.lean` run passes all 601
declaration checks and 369 examples without warnings or errors. All 493
axiom reports were captured and matched against the exact declaration
inventory: no missing, unexpected or duplicate reports and no unpermitted
axioms. The existing `polynomialDimensionBound` remains axiom-free;
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 491 reports use only the standard three. The original four
imports and all earlier verification content are preserved.
No new global algebra instance, input package, point order, residue
carrier, cycle module, Chow quotient or projector is introduced. The
new global value of the existing `DimensionFunction` structure is proved
equal to the existing affine construction when the scheme is affine.
The next bounded checkpoint is global point-height and carrier-dimension
identification; target codimension conversion and further realization
remain separate.

SP53 validation (2026-09-15): the leaf module and final full 3131-job
Lean build pass, with only the two existing `Challenge` warnings.
The six primary proof-dependency assertions and two supporting reports
pass. The independent leaf audit checks seven public axiom reports and
eight regressions without diagnostics; every new endpoint uses exactly
`propext`, `Classical.choice` and `Quot.sound`. The exact-original-four-
import replay passes seven checks and fourteen regressions, including
scope guards against affine, compact, Noetherian, integral and
preinstalled-algebra assumptions; full extended height and closure
dimension; carrier-degree and cycle-homogeneity criteria; negative
degrees and trivial coefficients; qualified open-height invariance;
the empty scheme; and the actual noncompact countable coproduct with
pointwise finite heights. Earlier verification content and imports are
unchanged. Independent mathematical and cross-document reviews pass.
The single PDF builds to 57 pages with a clean final log. Proposition
6.26 and its proof on pages 27--28, module/status pages 31--32 and the
theorem-map row on page 50 were visually inspected. Existing sources
0A21, 02QO and 02QM are rechecked in their exact field-base scope, with
no source axiom or bibliography change. Submission wrappers and
dependency pins are unchanged; diff checks pass. The final integrated
`research/Verification.lean` run passes all 608 declaration checks and
383 examples without warnings or errors. All 500 selected axiom reports
were captured and compared with the exact declaration inventory, with
no missing, unexpected or duplicate reports and no unpermitted axioms.
The existing `polynomialDimensionBound` is axiom-free;
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 498 reports use exactly the standard three.
The checkpoint introduces no new grading, carrier, scalar action,
cycle module, Chow quotient or projector. The next bounded theorem is
finite chain codimension plus support degree equals generic degree for
actual integral schemes, before the intended target reindexing.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `SplitPointGeometry.scheme` | finite split scheme | $Z_I=\operatorname{Spec}(k^I)$ |
| `SplitPointGeometry.pointInclusion` | selected component inclusion | $s_i:\operatorname{Spec}k\to Z_I$ |
| `SplitPointGeometry.IntegralClosedSubscheme` | actual ideal-sheaf data whose associated closed subscheme is integral | $\operatorname{IntSub}(Z_I)$ |
| `SplitPointGeometry.pointIdealSheaf` / `pointIntegralSubscheme` | ideal sheaf of the reduced point component, and its canonical integral subscheme | $\mathcal I(s_i)$ / $[s_i]\in\operatorname{IntSub}(Z_I)$ |
| `SplitPointGeometry.labelEquivIntegralClosedSubscheme` | exact identification of labels with integral closed subschemes | $I\xrightarrow{\sim}\operatorname{IntSub}(Z_I)$ |
| `SplitZeroCycles.Cycles` | finitely supported coefficients on actual integral closed subschemes | $Z_0(Z_I;R)=\bigoplus_{W\in\operatorname{IntSub}(Z_I)}R[W]$ |
| `SplitZeroCycles.pointCycle` | fundamental cycle of the actual reduced point subscheme | $[s_i]\in Z_0(Z_I;R)$ |
| `SplitZeroCycles.coordinates` | coefficients indexed by the classified point subschemes | $Z_0(Z_I;R)\xrightarrow{\sim}R^I$ |
| `SplitZeroCycles.IntegralCurve` / `PrincipalDivisorData` | actual dimension-one integral closed subschemes, paired with units in their actual scheme function fields; proved empty | $(W,f)$ with $\dim W=1$ and $f\in k(W)^\times$ |
| `SplitZeroCycles.principalDivisor` | the unique ambient principal-divisor cycle assignment on the empty geometric indexing type | $(W,f)\mapsto(\iota_W)_*\operatorname{div}_W(f)$ |
| `SplitZeroCycles.relations` | submodule generated by principal-divisor cycles, proved zero | $\operatorname{Rat}_0(Z_I;R)$ |
| `SplitZeroCycles.RationallyEquivalent` | difference lies in the relation submodule; proved equivalent to equality | $z\sim_{\mathrm{rat}}w$ |
| `SplitZeroCycles.Chow` / `classMap` | quotient of the actual cycle module by rational equivalence, and its class map | $\mathrm{CH}_0(Z_I;R)=Z_0/\operatorname{Rat}_0$, $z\mapsto\overline z$ |
| `SplitZeroCycles.chowEquivCycles` / `chowCoordinates` | quotient-by-zero and point-coordinate linear equivalences | $\mathrm{CH}_0(Z_I;R)\xrightarrow{\sim}Z_0(Z_I;R)\xrightarrow{\sim}R^I$ |
| `SplitZeroCycles.rationalize` | integral-to-rational coefficient extension on actual cycles | $Z_0(Z_I;\mathbf Z)\hookrightarrow Z_0(Z_I;\mathbf Q)$ |
| `SplitZeroCycles.rationalizationEquiv` | rational cycle coefficients are scalar extension of the integral module | $\mathbf Q\otimes_{\mathbf Z}Z_0(Z_I;\mathbf Z)\xrightarrow{\sim}Z_0(Z_I;\mathbf Q)$ |
| `SplitZeroCycles.chowRationalize` | coefficient extension induced on the Chow quotient, proved injective | $\mathrm{CH}_0(Z_I;\mathbf Z)\hookrightarrow\mathrm{CH}_0(Z_I;\mathbf Q)$ |
| `SplitZeroCycles.chowRationalizationEquiv` | canonical rational scalar extension of the integral Chow group, preserving point generators | $\mathbf Q\otimes_{\mathbf Z}\mathrm{CH}_0(Z_I;\mathbf Z)\xrightarrow{\sim}\mathrm{CH}_0(Z_I;\mathbf Q)$ |
| `SplitPointGeometry.imageIntegralSubscheme` / `imageIntegralSubschemeMap` | actual scheme-theoretic image and restricted point map | $f(W)$ / $W\to f(W)$ |
| `SplitPointGeometry.productIso` / `pointFiberIso` | actual product and inverse-image comparisons respecting their maps | $Z_{I\times J}\simeq Z_I\times_kZ_J$ / $Z_{f^{-1}(i)}\simeq f^{-1}(s_i)$ |
| `SplitPointGeometry.pointIdealSheaf_comap_mapOfFunction` | equality of the actual inverse-image ideal sheaf | $f^*\mathcal I(s_i)=\mathcal I(f^{-1}(s_i))$; theorem only |
| `SplitPointGeometry.pointStalkIso` / `stalkMap_length_of_isOpenImmersion` / `residueFieldMap_finrank_of_isIso` | actual stalk identifications and degree/multiplicity-one computations | $\mathcal O_{Z_I,s_i}\simeq k$, $m=1$, $[\kappa(s):\kappa(f(s))]=1$; proof adapters |
| `SplitZeroCycles.pushforward` / `chowPushforward` | proper pushforward, on cycles and their quotient | $f_*$ |
| `SplitZeroCycles.pullback` / `chowPullback` | flat pullback, on cycles and their quotient | $f^*$ |
| `SplitZeroCycles.externalProduct` / `chowExternalProduct` | external product on actual product points | $z\times w$ |
| `SplitZeroCycles.intersection` / `chowIntersection` | diagonal pullback of external product | $z\cdot w=\Delta^*(z\times w)$ |
| `SplitZeroCycles.pointFiberMultiplicity` / `imageDegree` | actual fiber ambient-stalk length and point-image residue-field degree, both proved one | $m_x(f^{-1}(s_i))$ / $\deg(W/f(W))$ |
| `SplitZeroCycles.fiberCycle` | fundamental cycle of the actual point fiber, initially weighted by its actual local lengths | $[f^{-1}(s_i)]_0$; identified with $f^*[s_i]$ |
| `SplitChowCorrespondence.Correspondence` | rational Chow cycles on the actual product, in its proved split presentation | $\operatorname{Corr}^0(Z_I,Z_J)=\mathrm{CH}_0(Z_I\times_k Z_J;\mathbf Q)$ |
| `SplitChowCorrespondence.comp` | geometric pull--intersection--push composition | $b\circ a=(p_{13})_*(p_{12}^*a\cdot p_{23}^*b)$ |
| `SplitChowCorrespondence.matrixCoordinates` | point-pair coordinates, with outputs in rows | $\kappa_{JI}:\operatorname{Corr}^0(Z_I,Z_J)\xrightarrow{\sim}M_{J\times I}(\mathbf Q)$ |
| `SplitChowCorrespondence.EndAlgebra` | the existing Chow endomorphisms with actual geometric composition and diagonal unit | $\Gamma_I^{\mathrm{CH}}=\operatorname{Corr}^0(Z_I,Z_I)$ |
| `SplitChowCorrespondence.matrixAlgEquiv` | endomorphism coordinates upgraded to an algebra equivalence by the proved composition law | $\kappa_{II}:\Gamma_I^{\mathrm{CH}}\xrightarrow{\sim}M_I(\mathbf Q)$; same coordinate map |
| `SplitChowCorrespondence.spanQuotientEquiv` | generator-compatible algebra equivalence from the additive span quotient to the actual Chow algebra | $\Psi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}^{\mathrm{add}}\xrightarrow{\sim}\Gamma_I^{\mathrm{CH}}$, with $\kappa_{II}\circ\Psi_{\mathrm{sp}}=\overline\chi_{\mathrm{sp}}$ |
| `SplitChowCorrespondence.action` | actual Chow correspondence action on zero-cycle Chow classes | $c_*z=(p_2)_*(c\cdot p_1^*z)$ |
| `SplitChowCorrespondence.ofSplitSpan` | proper pushforward of an actual finite split carrier's fundamental cycle along the pair map, proved to equal the image of its additive span class | $(\ell,r)_*[Z_S]_0=\sum_s[(\ell(s),r(s))]$; no second realization map |
| `SplitComplexPoints.Point` | actual complex-algebra points with the regular-function evaluation topology | $X_I=Z_I(\mathbf C)=\operatorname{Hom}_{\mathbf C\text{-alg}}(\mathbf C^I,\mathbf C)$ |
| `SplitComplexPoints.evalPoint` / `labelHomeomorph` | actual evaluation point / proved homeomorphism from the discrete labels | $\operatorname{ev}_i$ / $I\xrightarrow{\sim}X_I$ |
| `SplitComplexPoints.schemeMorphism` / `mapContinuous` / `productHomeomorph` | actual over-base scheme point, continuous functorial point map, and projection-compatible product adapter | no independent symbols; use the existing point and projection maps |
| `SingularDegreeZero.Simplex` | actual continuous singular simplex | $S_n(X)=C(\Delta^n,X)$ |
| `SingularDegreeZero.ZeroCochain` / `OneCochain` / `coboundary` | actual singular cochains and two-face differential | $C^0(X;\mathbf Q)$ / $C^1(X;\mathbf Q)$ / $\delta^0$ |
| `SingularDegreeZero.H0` / `SplitBetti.Cohomology` | unreduced degree-zero singular cohomology, then its actual complex-point specialization | $H^0_{\mathrm B}(X;\mathbf Q)=\ker\delta^0$ / $H^0_{\mathrm B}(X_I;\mathbf Q)$ |
| `SingularDegreeZero.eval` / `equivFunctions` / `SplitBetti.coordinates` | actual-point evaluation and its discrete-space/label coordinate equivalences | $u\mapsto(x\mapsto u(x))$ / $u\mapsto(u_i)_{i\in I}$; no new realization symbol |
| `SplitBetti.cycleClass` | point-normalized cycle-class map, proved a linear equivalence | $\operatorname{cl}_I:\mathrm{CH}_0(Z_I;\mathbf Q)\xrightarrow{\sim}H^0_{\mathrm B}(X_I;\mathbf Q)$ |
| `SingularDegreeZero.cup` / `pullback` / `transfer` | degree-zero singular cup, actual continuous-map pullback, and actual-fiber finite transfer | $\smile$ / $f^*$ / $f_*$, with the cohomological domain displayed |
| `SplitBetti.cycleClass_pointCycle` | characteristic cocycle normalization of the actual point class | $\operatorname{cl}_I([s_i])=\delta_i$ |
| `SingularDegreeZero.ZeroSimplexLift` / `transfer_simplex_eq_sum_lifts` | actual singular zero-simplex lifts and the proved source-matching transfer formula | $\{\tau:f\circ\tau=\sigma\}$; no second transfer operation |
| `SplitBetti.action` | actual cohomological pull--cup--transfer correspondence action | $c_{\mathrm B,*}u=(p_2)_*(\operatorname{cl}(c)\smile p_1^*u)$ |
| `SplitBetti.realization` / `correspondenceAction` | rational algebra representation of the actual Chow convolution algebra / packaging in the existing action interface | $\rho_{\mathrm B,I}:\Gamma_I^{\mathrm{CH}}\to\operatorname{End}_{\mathbf Q}(H^0_{\mathrm B}(X_I;\mathbf Q))$; same action |
| `SplitHodgeStructure.Complexification` / `complexCoordinates` | actual tensor complexification of singular degree-zero cohomology / its computed complex point coordinates | $H_I=H^0_{\mathrm B}(X_I;\mathbf Q)$, $H_{I,\mathbf C}=\mathbf C\otimes_{\mathbf Q}H_I\cong\mathbf C^I$ |
| `SplitHodgeStructure.rationalEmbedding` / `conjugation` | canonical rational embedding / conjugation induced from the rational structure | $\iota_I(u)=1\otimes u$ / $\overline{c\otimes u}=\bar c\otimes u$ |
| `SplitHodgeStructure.bigrading` | explicitly specified effective degree-zero Hodge pieces, with directness, exhaustion, and conjugation proved | $H_I^{p,q}$; all of $H_{I,\mathbf C}$ at $(0,0)$, zero otherwise |
| `SplitHodgeStructure.rationalHodgeClasses` | rational preimage of the complex Hodge piece, independently of cycles | $H_{I,\mathrm{Hdg}}=\iota_I^{-1}(H_I^{0,0})$ |
| `SplitHodgeStructure.complexifyMap` / `IsHodgeMorphism` | genuine scalar extension of a rational map / preservation of all complex bigrading pieces | $f_{\mathbf C}=1\otimes f$ / prose predicate |
| `SplitChowTateBlock.optionSchemeIso` | actual coproduct with the distinguished point, respecting both inclusions | $I^+=\{*\}\amalg I$, $Z_{I^+}\cong\operatorname{Spec}\mathbf C\amalg Z_I$ |
| `SplitChowTateBlock.encode` | affine Chow graph construction from actual column pushforward and a fixed point-pair class | $\operatorname{enc}_I(z)=[(*,*)]+j_*z$, $j(i)=(*,i)$ |
| `SplitChowTateBlock.decode` | actual flat column pullback, linear and defined on every correspondence | $\operatorname{dec}_I(c)=j^*c$ |
| `SplitBettiTateBlock.blockCoordinates` | fixed actual cohomology decomposition into distinguished point and complement | $\tau_I:H^0_{\mathrm B}(X_{I^+};\mathbf Q)\xrightarrow{\sim}\mathbf Q(0)\oplus H_I$ |
| `SplitBettiTateBlock.realization` / `coordinateChange` | the existing actual Betti action in fixed coproduct coordinates / conjugation adapter | $\rho_I^+(c)=\tau_I\rho_{\mathrm B,I^+}(c)\tau_I^{-1}$ |
| `SplitBettiTateBlock.hodgeModel` | actual finite codimension-zero Chow/Betti model with independent Hodge subspace | $\mathscr H_I^0=(\mathrm{CH}_0(Z_I;\mathbf Q),H_I,H_{I,\mathrm{Hdg}},\operatorname{cl}_I)$ |
| `SplitBettiTateBlock.construction` / `detection` / `hodgeCompatibility` | instances of the existing graph interfaces using the actual geometric block and Hodge structure | use $\operatorname{enc}_I$, $\operatorname{dec}_I$, and the existing graph criterion; no duplicate objects |
| `SplitBettiTateBlock.IsBlockHodgeMorphism` | Hodge-morphism predicate transported through the fixed actual Betti block decomposition | prose predicate on $\mathbf Q(0)\oplus H_I$ |
| `SplitBettiTateBlock.graphProjectorLift` | encoded Chow representative of the independently specified graph operator | $\Pi_\alpha=\operatorname{enc}_I(\operatorname{cl}_I^{-1}\alpha)$, $\rho_I^+(\Pi_\alpha)=P_\alpha$ |
| `SplitGaloisSheets.regularAction` / `regularCollisionDecomposition` | actual regular split torsor action and graph-sheet collision identity | $G\curvearrowright Z_G$, $\coprod_{a\in G}Z_G\cong Z_G\times_{\operatorname{Spec}\mathbf C}Z_G$ |
| `SplitGaloisSheets.quotientMap` | actual finite étale homogeneous intermediate cover, with no normality hypothesis | $Z_G\to Z_S$, $S=G/D$, $g\mapsto gD$ |
| `SplitGaloisResidual.Complement` / `sheetEquiv` | complementary marked sheets and their point-plus-complement labeling | $I=S\setminus\{s_0\}$, $I^+\cong S$ |
| `SplitGaloisResidual.residualCoordinates` | restriction with zero-extension inverse; auxiliary coordinates of the existing ideal | $E_D\xrightarrow{\sim}\mathbf Q^I$; no new residual object |
| `SplitGaloisResidual.residualCycles` / `residualChow` / `residualChowEquiv` | actual weighted point-cycle construction and its class, upgraded by its proved inverse | $\lambda_D(x)=\sum_{i\in I}x(i)[i]$ for the Chow map; distinguish its cycle representative in prose |
| `SplitGaloisResidual.fundamentalClass` | actual fundamental point-sum of the complement | $[Z_I]=\sum_{i\in I}[i]$ |
| `SplitGaloisMarkedComparison.residualRealization` | cycle class after the geometric residual Chow equivalence | $\theta_D=\operatorname{cl}_I\lambda_D$ |
| `SplitGaloisMarkedComparison.generatedChowClass` / `generatedClass` | independently generated Chow and Betti target classes | $z_D=\lambda_D(a_D)=-[Z_I]$, $\alpha_D=\theta_D(a_D)=-\operatorname{cl}_I[Z_I]$ |
| `SplitChowDiagonal.diagonalAlgHom` | actual diagonal pushforward embedding of point functions into correspondence convolution | $\delta_I:\mathbf Q^I\hookrightarrow\Gamma_I^{\mathrm{CH}}$ |
| `SplitChowTateBlock.column` | shared actual column pushforward used by both affine encoding and shear | $N_z=j_*z$; no second graph encoding |
| `SplitChowShear.pointProjector` | raw marked-point Chow projector in the fixed block | $e_*=[(*,*)]$ |
| `SplitChowShear.shear` / `shearUnit` | diagonal plus actual column, with its constructed two-sided inverse | $\mathcal U_z=1+N_z$, $\mathcal U_z^{-1}=\mathcal U_{-z}$ |
| `SplitBettiTateBlock.realization_shear` | existing actual Chow action sends the geometric unit to the linear shear | $\rho_I^+(\mathcal U_z)=U_{\operatorname{cl}_I(z)}$; distinguish Chow $\mathcal U_z$ from linear $U_\alpha$ |
| `SplitGaloisMarkedComparison.sheetSchemeIso` / `sheetReindex` | actual scheme reindexing and its algebra map on rational sheet functions | $Z_{I^+}\cong Z_S$ and reindexing; no new geometric cover |
| `SplitGaloisMarkedComparison.sheetCohomology` / `sourceToBlock` | actual cycle class of a weighted sheet cycle / its realized constant-unit coordinates | sheet-cycle class in prose; $\Theta_DT_D$ for the block map, not a new realization action |
| `SplitGaloisMarkedComparison.sourceToBlock_eq_realization_shear` | the marked source coordinates are the action of the actual Chow shear on the full sheet class | $\Theta_DT_D(f)=\rho_I^+(\mathcal U_{z_D})\tau_I(\operatorname{cl}(\sum_s f(s)[s]))$ |
| `SplitGaloisMarkedComparison.markedEmbedding` | injective actual sheet-to-Chow algebra map, diagonal pushforward followed by fixed geometric conjugation | $\delta_D^{\mathrm{mk}}=\operatorname{Ad}(\mathcal U_{z_D})\circ\delta_{I^+}\circ\operatorname{reindex}$ |
| `SplitGaloisMarkedComparison.markedEmbedding_action` | full sheet multiplication acts through the actual marked Chow embedding | $\rho_I^+(\delta_D^{\mathrm{mk}}(f))\Theta_DT_D(g)=\Theta_DT_D(fg)$; the selector square is its marked specialization |
| `SplitGaloisMarkedComparison.markedProjector` | actual image of the selector and Chow conjugate of the raw marked point | $\Pi_D=\delta_D^{\mathrm{mk}}(q_D)=\mathcal U_{z_D}e_*\mathcal U_{-z_D}=\operatorname{enc}_I(z_D)$ |
| `SplitGaloisMarkedComparison.comparison` | instantiated restriction-free comparison under the unchanged fixed Tate-block action | $\mathscr R_{\Pi_D}$, using $\Theta_D=\operatorname{id}_{\mathbf Q}\oplus\theta_D$ and existing $\rho_I^+$ |
| `SplitGaloisMarkedComparison.projectorLift` / `palomarTargetSquare` | the chosen idempotent and its independently specified graph target | $\rho_I^+\circ\varphi_{\Pi_D}=\varphi_{P_{\alpha_D}}$; no new target object |
| `MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_surjective` | exact rigidity of a surjective multiplicative residual realization | $\alpha=-1$ in the target algebra; a theorem, not a coverage hypothesis |
| `SplitPointGeometry.existsUnique_pointIso_of_isIntegral` | unique point label and scheme isomorphism respecting an integral closed immersion | $e:X\xrightarrow{\sim}\operatorname{Spec}k$, $s_i\circ e=f$ |
| `SplitPointGeometry.topologicalKrullDim_le_zero_of_isClosedImmersion` / `topologicalKrullDim_eq_zero_of_isClosedImmersion` | dimension bound for actual closed subschemes, equality if nonempty | $\dim X\leq 0$ / $\dim X=0$ |
| `SplitFieldQuotient.evalQuotientEquiv` | quotient by a coordinate prime is the base field | $\mathfrak m_i=\ker(\operatorname{ev}_i)$, $k^I/\mathfrak m_i\cong_k k$ |
| `SplitPointGeometry.pointSpan` | actual point-supported diagonal span | $Z_I\xleftarrow{s_i}\operatorname{Spec}k\xrightarrow{s_i}Z_I$ |
| `SplitPointGeometry.pointProjector` | its free finite-étale span basis class | $\pi_i$ |
| `SplitPointCorrespondence.ZeroCycles` | earlier finite rational coefficient module, now the point-coordinate presentation of actual scheme Chow | $\mathbf Q^I$, $I=\{0,1\}$ |
| `SplitPointCorrespondence.Correspondence` | finite coefficient convolution algebra | $\Gamma_I=M_2(\mathbf Q)$ |
| `SplitPointCorrespondence.firstPointProjector` | point matrix unit | $\Pi=E_{00}$ |
| `SplitPointCorrespondence.markedSource` | marked two-component source | $A=\mathbf Q\times\mathbf Q$, $\epsilon(a,b)=a$, $q=(1,0)$ |
| `SplitPointCorrespondence.residualEvaluation` | second-coordinate map on the residual ideal | $\theta(0,b)=b$ |
| `SplitPointCorrespondence.constantCoordinates` | constant-unit coordinates | $T(a,b)=(a,b-a)$ |
| `SplitPointCorrespondence.pointRealization` / `realization` | ordinary / conjugated matrix action | $C\mapsto C(-)$ / $\rho(C)=TCT^{-1}$ |
| `SplitPointCorrespondence.markedComparison` / `projectorLift` | explicit instances of the canonical comparison / lift | specialization only; no independent symbol |
| `SplitPointGeometry.mapOfFunction` / `span` | scheme map and span induced by finite indexing functions | $Z_S\to Z_I$ / $Z_I\xleftarrow{\ell}Z_S\xrightarrow{r}Z_I$ |
| `labelEquivScheme` / `labelEquivOfIso` | intrinsic-point and relabelling equivalences used for descent | prose only; presentation adapters |
| `Fiber` / `fiberIso` / `span_comp_iso` | finite matching pairs compute the actual scheme pullback | $\{(s,t):r(s)=\ell'(t)\}$ / $Z_S\times_{Z_J}Z_T$ |
| `span_sum_iso` | sum-indexed span is the actual scheme coproduct | $P\sqcup Q$; no second coproduct object |
| `span_pointDecomposition_iso` | split span is the actual indexed coproduct of its point-pair spans | $[S,\ell,r]\cong\coprod_{s\in S}[\{*\},\ell(s),r(s)]$ at the scheme-span level |
| `SplitSpanRealization.Presentation` | finite split presentation of an existing geometric class | witness only; no independent object symbol |
| `SplitSpanRealization.classSubmonoid` / `SplitClass` | split-presentable submonoid of actual finite-étale span classes | $\mathcal S_{\mathrm{sp}}(Z_I/k)$ |
| `SplitSpanRealization.FreeAlgebra` | free rational linearization of that submonoid, before coproduct relations | $\mathcal C_{\mathrm{sp}}(Z_I/k)$ |
| `SplitSpanRealization.toFiniteEtaleFreeAlgebra` | injective source algebra inclusion | $j_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\hookrightarrow\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}$ |
| `classMatrixHom` / `SplitSpanRealization.realization` | point-count assignment and its rational algebra extension; surjective, proved noninjective by the empty-span witness | $\chi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\twoheadrightarrow M_I(\mathbf Q)$ |
| `SplitSpanRealization.decompositionDefect` | finite point-decomposition difference in the free algebra | $d_{S,\ell,r}=[S,\ell,r]-\sum_s[\{*\},\ell(s),r(s)]$ |
| `SplitSpanRealization.additiveRelations` | two-sided ideal generated by those differences, proved equal to the realization kernel | $J_{\mathrm{sp}}=\langle d_{S,\ell,r}\rangle=\ker\chi_{\mathrm{sp}}$ |
| `SplitSpanRealization.AdditiveQuotient` | quotient of the free source by finite point-decomposition relations, now algebra-isomorphic to the actual Chow endomorphisms | $\mathcal C_{\mathrm{sp}}^{\mathrm{add}}=\mathcal C_{\mathrm{sp}}/J_{\mathrm{sp}}$ |
| `SplitSpanRealization.quotientRealization` / `quotientRealizationEquiv` | induced matrix map, proved to be an algebra isomorphism | $\overline\chi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}^{\mathrm{add}}\xrightarrow{\sim}M_I(\mathbf Q)$ |
| `SplitSpanRealization.pointNormalForm` | linear normal-form map used in the kernel proof; not an algebra-homomorphism section of the free realization | proof adapter only; no independent notation |
| `GeometricSplitPoints.projector` | split-source point projector whose ambient image is the original point span | $\pi_0^{\mathrm{sp}}$, with $j_{\mathrm{sp}}(\pi_0^{\mathrm{sp}})=\pi_0$ |
| `GeometricSplitPoints.coefficientRealization` | existing coefficient action composed with the new geometric-source map | $\rho\circ\chi_{\mathrm{sp}}$ |
| `GeometricSplitPoints.markedComparison` / `projectorLift` / `palomarTargetSquare` | canonical comparison/lift/square specialized to the actual source | no new notation; $(\rho\circ\chi_{\mathrm{sp}})\circ\varphi_{\pi_0^{\mathrm{sp}}}=\varphi_{P_{-1}}$ |
| `GeometricSplitPoints.additiveCoefficientRealization` / `additivePalomarTargetSquare` | the existing coefficient action and target square descended through the proved additive quotient | induced action only; no duplicate marked-comparison object or independent notation |

### Fields, normalizations, and boundary geometry

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| base ring parameter | affine base | $B$ |
| fraction field parameter | fraction field of the base | $K=\operatorname{Frac}(B)$ |
| marked intermediate field | selected finite extension | $L/K$ |
| normal-closure field | supplied normal closure | $N/K$ |
| `NormalClosureData` | marked normal-closure datum | $\mathcal N=(K,L,N,\iota)$ |
| `NormalClosureData.isGalois` | Galois structure derived from the same finite normal-closure datum over a perfect base | $\operatorname{Gal}_{\mathcal N}:\operatorname{IsGalois}(N/K)$ |
| `NormalClosureData.galoisGroup` | normal-closure Galois group | $G=\operatorname{Gal}(N/K)$ |
| `intermediateFixingSubgroup` | stabilizer of the marked copy of $L$ | $H=\operatorname{Gal}(N/\iota(L))$ |
| `NormalClosureData.normalClosureTensorToGenericSheets` / `normalClosureTensorGenericSheetsEquiv` | normal-closure base-change splitting into marked sheets | $\sigma_{\mathcal N}:N\otimes_KL\to N^{G/H}$, an equivalence over a perfect $K$ |
| `NormalClosureData.normalClosureBaseSheetAugmentation` | evaluation at the marked base sheet | $\epsilon_H^N:N^{G/H}\to N$ |
| `NormalClosureData.normalClosureTensorDiagonal` | marked tensor-diagonal algebra map | $\delta_\iota:N\otimes_KL\to N$, $x\otimes y\mapsto x\iota(y)$ |
| `normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets` / `normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv` | multiplicative source square, followed by its perfect-field equivalence restatement | $\epsilon_H^N\circ\sigma_{\mathcal N}=\delta_\iota$ |
| `IntermediateNormalizationRing` | integral closure of $B$ in $L$ | $\widetilde B_L=\operatorname{IntCl}_B(L)$ |
| `NormalClosureNormalizationRing` | integral closure of $B$ in $N$ | $\widetilde B_N=\operatorname{IntCl}_B(N)$ |
| `intermediateNormalization` | marked normalization scheme | $Y_L=\operatorname{Spec}(\widetilde B_L)$ |
| `normalClosureNormalization` | common normal-closure normalization | $Y_N=\operatorname{Spec}(\widetilde B_N)$ |
| `NormalizedCover` | finite normalization with marked visible open | $\mathcal C=(U\mathbin{\lhook\joinrel\longrightarrow}Y_L,\mathcal N)$ |
| `Diagram` | valuation/center normalization diagram | $\mathscr D$ |
| `conjugateNormalClosureEmbeddingOverBase` | conjugate marked embedding | $\iota_g:L\hookrightarrow N$ |
| `conjugateNormalClosureToIntermediateNormalization` | conjugate normalization leg | $c_g:Y_N\to Y_L$ |
| `Diagram.boundary` | deleted boundary in $Y_L$ | $\partial U=Y_L\setminus U$ |
| `pulledBackConjugateBoundary` | boundary pulled to the common normalization | $\partial_g=c_g^{-1}(\partial U)$ |
| `pulledBackConjugateBoundaryIdeal` | radical ideal of $\partial_g$ | $J_g=I(\partial_g)$ |
| `fixedLocusIdeal` | ideal generated by inertia differences | $J_{\mathrm{fix}}(I)=(\sigma(t)-t)_{\sigma\in I,t\in\widetilde B_N}$ |
| `movingBoundaryIdeal` | sum of boundaries of sheets moved by $I$ | $J_{\mathrm{mov}}(I)=\sum_{I\nleq gHg^{-1}}J_g$ |
| `fixedMovingBoundaryIdeal` | combined fixed--moving ideal | $J_{\mathrm{fm}}(I)=J_{\mathrm{fix}}(I)+J_{\mathrm{mov}}(I)$ |
| `ConjugateBoundarySeparation` | height-one avoidance condition | $\operatorname{Sep}_{\partial}(\mathcal C)$ |
| `RamifiedCodimensionOnePoint` | ramified height-one locus as a type | $\operatorname{Ram}^{(1)}(Y_N/B)$ |
| `NoCodimensionOneRamification` | empty height-one ramification locus | $\operatorname{Ram}^{(1)}(Y_N/B)=\varnothing$ |
| `ConjugateCenterRealization` | identification of centers with $c_g$ | $\operatorname{Ctr}(\mathscr D)$ |
| `ConjugateRamificationRealization` | equality of relative and geometric indices | $\operatorname{RamCmp}(\mathscr D)$ |
| `ConjugateBoundaryData` | the preceding two independent comparisons | $\mathscr B_{\mathscr D}=(\operatorname{Ctr},\operatorname{RamCmp})$ |

### Inertia, sheets, and extension objects

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `valuationAt E` | centered valuation ring at a ramified point | $V_E$ |
| `inertiaGroupAt` | valuation inertia subgroup | $I_E\leq G$ |
| `primeInertiaSubgroup` | stabilizer kernel on the residue ring | $I_Q^{\mathrm{pr}}\leq G$ |
| `GaloisSheets H` | marked sheet set | $\Sigma_H=G/H$ |
| `GenericSheetAlgebra k H` | pointwise sheet algebra | $F_k(H)=k^{G/H}$, with $A_H:=F_{\mathbf Q}(H)$ |
| `genericSheetSelector k H A` | characteristic function of selected sheets | $q_A=\mathbf 1_A$ |
| marked base-sheet selector | characteristic function of the base coset | $q_H=\mathbf 1_{\{H\}}$ |
| `InertiaSaturated I H A` | $I$-stable selected sheet set | $\operatorname{Sat}_I(A)$, equivalently $I\cdot A=A$ |
| `GlobalSheetSelectorExtension` | actual global selector extensions | $\operatorname{Ext}^{\mathrm{sel}}_{\partial}(q_A)$ |
| `GaloisProjectorExtensionPurity` | selector gluing equivalence | $\operatorname{Pur}^{\mathrm{sel}}_{\partial}$ |
| subgroup average | rational group-algebra idempotent | $e_H=|H|^{-1}\sum_{h\in H}[h]$ |
| `subgroupAveragingProjector` | generic graph-correspondence image of the average | $\pi_H^\eta=\gamma_\eta(e_H)$ |
| `FiniteEtaleFreeAlgebra pX` | free finite-etale span algebra | $\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}(X/T)$ |
| generic rational correspondence algebra | generic convolution algebra | $\Gamma_\eta$ |
| compactified rational correspondence algebra | target convolution algebra | $\overline\Gamma$ |
| restriction algebra map | generic restriction | $r:\overline\Gamma\to\Gamma_\eta$ |
| `AlgebraProjectorClosure` | raw closure witnesses for $e_\eta$ | $\operatorname{Cl}_r(e_\eta)$ |
| `projectorIdempotenceDefect` | multiplicative idempotence defect | $\operatorname{Def}(\Pi)=\Pi^2-\Pi$ |
| `ZeroDefectWitness` | raw closures with vanishing defect | $\operatorname{Cl}_r^0(e_\eta)$ |
| `AlgebraProjectorExtension` | compactified idempotent extensions | $\operatorname{Ext}_r(e_\eta)$ |
| `AlgebraProjectorExtension.genericIdempotentMap` | universal presentation of the generic idempotent | $\varphi_{e_\eta}:\mathcal U\to\Gamma_\eta$ |
| `AlgebraProjectorExtension.compactifiedIdempotentMap` | universal presentation of a compactified idempotent | $\varphi_\Pi:\mathcal U\to\overline\Gamma$ |
| `restriction_comp_compactifiedIdempotentMap` | universal compactification square | $r\circ\varphi_\Pi=\varphi_{e_\eta}$ |
| `CompactifiedSubgroupProjectorExtension` | all-boundary extensions of $e_H$ | $\operatorname{Ext}_{\partial,r}(e_H)$ |
| `CompactifiedDeckGraphComparison` | generic/compactified graph square | $\mathscr G_r$ |

### Actual closed graphs and restriction (SP30)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `SchemeCorrespondence.graphMorphism p σ` | actual graph morphism, with the same ordered legs as the existing graph span | $g_\sigma=(\operatorname{id},\sigma):Y\to Y\times_UY$ |
| `SchemeCorrespondence.graphIdeal p σ` | kernel ideal of the graph morphism; defines the closed graph when $p$ is separated | $\mathcal I_\sigma$ |
| `(graphIdeal p σ).subscheme` / `graphSubschemeIso p σ` | actual closed graph and its source identification, not a cycle class | $\operatorname{Gr}(\sigma)$ / $Y\simeq\operatorname{Gr}(\sigma)$ |
| `graphMorphism_isClosedImmersion` / `graphMorphism_isProper` | proved properties of the graph morphism under separatedness | prose only; no extra source input |
| `FiniteEtaleExtension.inclusion` / `pairInclusion` | actual inclusion of the cover and induced open inclusion of relative products | $\iota:Y\hookrightarrow\bar Y$ / $\iota^{(2)}:Y\times_UY\hookrightarrow\bar Y\times_S\bar Y$ |
| `pairInclusion_isOpenImmersion` / `graph_restriction_commutes` / `graphRestriction_isPullback` | open immersion and actual Cartesian graph restriction square | prose only; no duplicate comparison package |
| `graphIdeal_restriction` | scheme-theoretic inverse-image equality for an already extended automorphism | $\mathcal I_{\operatorname{res}_E\sigma}=(\iota^{(2)})^*\mathcal I_\sigma$ |
| `graphIdeal_liftDeckAction` | specialization to a prescribed original action under the explicit deck-extension hypothesis | same ideal equality; theorem only |

The graph span, its closed-subscheme realization, and any later Chow class
remain distinct types. The new construction has no new projector or
literature premise. Its base $S$ is auxiliary, not the ultimate Hodge target.
Here $(-)^*$ on ideals means scheme-theoretic inverse image, not yet a map
of Chow groups.

### Finite cycles and integral graph assembly (SP31)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `SchemeCycles.IntegralClosedSubscheme W` | actual integral ideal-sheaf subschemes; the split type is its definitional specialization | $\operatorname{IntSub}(W)$ |
| `SchemeCycles.Cycles W R` | finite, ungraded cycles; no rational-equivalence quotient | $Z_{\mathrm{fin}}(W;R)=\bigoplus_{Z\in\operatorname{IntSub}(W)}R[Z]$ |
| `SchemeCycles.fundamentalCycle R Z` | coefficient-one integral generator | $[Z]$ |
| `openRestrictionSubschemeMap` / `openRestrictionSubscheme` | actual open map on inverse-image supports and nonempty integral support | $v^{-1}Z\to Z$ / $v^{-1}Z$ |
| `openRestrictionGenerator` / `openRestriction` | empty-aware generator restriction and its linear extension | $v^*_{\mathrm{cyc}}[Z]$ / $v^*_{\mathrm{cyc}}:Z_{\mathrm{fin}}(W;R)\to_R Z_{\mathrm{fin}}(V;R)$ |
| `openRestriction_id` / `openRestriction_comp` | functoriality of the same open restriction | prose only; no extra comparison object |
| `graphIntegralSubscheme` / `graphCycle` | the existing closed graph as an integral support, then its cycle generator | $\operatorname{Gr}(\sigma)$ / $[\operatorname{Gr}(\sigma)]$ |
| `graphIdeal_topologicalKrullDim` | graph dimension transported through its actual source isomorphism | $\dim\operatorname{Gr}(\sigma)=\dim Y$; theorem only |
| `graphCycleLinearMap p` | rational linear assembly of actual integral graph cycles | $\zeta_p:\mathbf Q[\operatorname{Aut}_U(Y)]\to_{\mathbf Q}Z_{\mathrm{fin}}(Y\times_UY;\mathbf Q)$ |
| `FiniteEtaleExtension.original_isIntegral` | integrality inherited by the nonempty open original cover | prose only; derived property, not a new source premise |
| `graphCycle_restriction` / `graphCycleLinearMap_restriction` | generator compatibility and weighted cycle restriction square | $(\iota^{(2)})^*_{\mathrm{cyc}}\circ\zeta_{\bar p}=\zeta_p\circ\mathbf Q[\operatorname{res}_E]$ |

The new $\zeta_p$ is not the existing free-span algebra map $\gamma$ or a
Chow realization. Its codomain has no newly imposed product. The split
zero-cycle notation remains $Z_0(Z_I;R)$ because every split integral
support already has proved dimension zero. General open restriction
introduces no assertion that absolute dimension is unchanged.

### Scheme-theoretic graph composition and integral multiplicity (SP32)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `tripleProduct p` | actual relative triple product, with matching middle coordinates | $T=(Y\times_S Y)\times_Y(Y\times_S Y)$ |
| `tripleProductP12`, `tripleProductP23`, `tripleProductP13` | coordinate-pair projections | $p_{12},p_{23},p_{13}$ |
| `graphCompositionMorphism p σ τ` | source parameterization, with $\tau$ acting first | $h_{\sigma,\tau}(y)=(y,\tau y,\sigma(\tau y))$ |
| `graphIntersectionIdeal p σ τ` | sum of inverse-image graph ideals, not their intersection as ideals | $\mathcal J_{\sigma,\tau}=p_{12}^*\mathcal I_\tau+p_{23}^*\mathcal I_\sigma$ |
| `(graphIntersectionIdeal p σ τ).subscheme` | actual scheme-theoretic intersection of the two pulled-back closed graphs | $Z_{\sigma,\tau}=V(\mathcal J_{\sigma,\tau})$ |
| `graphIntersectionIso` | source identifies with that intersection | $Y\simeq Z_{\sigma,\tau}$; no extra object notation |
| `graphCompositionIso` | first/last projection identifies intersection with composite graph | $Z_{\sigma,\tau}\simeq\operatorname{Gr}(\sigma\tau)$ |
| `graphIntersectionIdeal_map_p13` | exact scheme-theoretic image ideal | $\operatorname{Im}_{\mathrm{sch}}(Z_{\sigma,\tau}\to Y\times_S Y)=\operatorname{Gr}(\sigma\tau)$ |
| `genericStalk_length_of_isClosedImmersion` / `integralSubscheme_genericStalk_length` | fundamental multiplicity for an integral closed support, with actual ambient scalars | $\operatorname{length}_{\mathcal O_{W,i(\eta_Z)}}\mathcal O_{Z,\eta_Z}=1$ |

No second projector, graph cycle type, or assumed convolution operation is
introduced. `graphMulIsom` remains the span comparison; the new theorem
identifies actual ideal-sheaf subschemes. Ideal `map` means the kernel ideal
of the composite inclusion, not a cycle pushforward. Ambient length one
does not yet identify a Chow intersection product.

### Closed-support images and graph-slice cycle maps (SP33)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `SchemeCycles.closedImageSubscheme f Z` | actual ideal image of a support whose composite into the target is a closed immersion | $f(Z)$ |
| `closedImageSubschemeIso` / `closedImageSubschemeIso_genericPoint` | support-to-image isomorphism, preserving the generic point | $Z\simeq f(Z)$; no extra object notation |
| `SchemeCycles.residueFieldMap_finrank_of_isIso` | canonical generic degree-one proof; old split name is an adapter | $[\kappa(\eta_Z):\kappa(\eta_{f(Z)})]=1$ in the support-image application |
| `closedImageCycle` | degree-one pushforward of a single admissible support | $f_{*,Z}[Z]$ |
| `closedImmersionPushforward` | linear pushforward along a globally closed immersion | $f_{*,\mathrm{cyc}}$ |
| `graphSliceMorphism p τ` | closed graph slice with free first and last coordinates | $s_\tau(y,z)=(y,\tau y,z)$ |
| `graphSlicePairMap p τ` | actual pair isomorphism, changing the input coordinate | $u_\tau=p_{23}s_\tau=(\tau,\mathrm{id})$ |
| `graphSlice_isPullback` / `graphIdeal_comap_p12_eq_graphSlice_ker` | slice identifies with the first graph's actual inverse image | $s_\tau(W)=p_{12}^{-1}\operatorname{Gr}(\tau)$ |
| `graphRightPullback` | open restriction along the pair isomorphism | $\mathsf R_\tau=u_\tau^*{}_{\mathrm{cyc}}$ |
| `graphSlicePullPush` | pair pullback followed by closed slice pushforward | $\mathsf K_\tau=(s_\tau)_{*,\mathrm{cyc}}\mathsf R_\tau$ |
| `graphIntersectionIntegralSubscheme` / `graphIntersectionCycle` | existing actual intersection as an integral support and its canonical cycle | $Z_{\sigma,\tau}$ / $[Z_{\sigma,\tau}]$ |
| `graphIntersectionCycle_image_p13` | supportwise outer-image formula | $(p_{13})_{*,Z_{\sigma,\tau}}[Z_{\sigma,\tau}]=[\operatorname{Gr}(\sigma\tau)]$ |
| `EtaleGraphIntersection` openness instances / `graphSliceMorphism_isOpenImmersion` | additional open-and-closed relative graph geometry under étaleness | prose only; no new cycle or projector |

The pair and inverse-image graph schemes may be reducible. They are not
installed as integral generators. The cycle maps above have specified
domains; no ambient outer pushforward or Chow algebra product is declared.
The canonical residue-degree proof now lives in `Cycles/ResidueDegree.lean`,
with the old split-point theorem retained only as a compatibility adapter.

### Structural-base graph and cycle comparison (SP34)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `forgetDeckBase p b` | injective change-of-base group map retaining the actual automorphism | $\operatorname{forg}_b:\operatorname{Aut}_S(Y)\hookrightarrow\operatorname{Aut}_B(Y)$, $\sigma\mapsto\bar\sigma$ |
| `pairBaseComparison p b`, `tripleBaseComparison p b` | actual closed inclusions, for separated $b:S\to B$ and $r=b\circ p$ | $\kappa_2:W_p\hookrightarrow W_r$, $\kappa_3:T_p\hookrightarrow T_r$, with $W_p=Y\times_S Y$ |
| `GraphBaseComparison` morphism and ideal-image theorems | graph, intersection, pair-isomorphism and slice compatibility | prose only; the graphs and slices are the existing objects with base subscripts |
| `ideal_comap_iso_eq_map_inv`, `openRestriction_iso_eq_pushforward_inv` | genuine ideal and cycle transport through inverse isomorphisms | $e^*_{\mathrm{cyc}}=(e^{-1})_{*,\mathrm{cyc}}$; theorem only |
| `graphCycle_pairBaseComparison`, `graphIntersectionCycle_tripleBaseComparison` | closed inclusion carries actual integral generators to their new-base versions | $\kappa_{2,*\mathrm{cyc}}[\operatorname{Gr}_p(\sigma)]=[\operatorname{Gr}_r(\bar\sigma)]$, $\kappa_{3,*\mathrm{cyc}}[Z^p_{\sigma,\tau}]=[Z^r_{\bar\sigma,\bar\tau}]$ |
| `graphCycleLinearMap_baseComparison` | rational weighted assembly square | $\kappa_{2,*\mathrm{cyc}}\zeta_p=\zeta_r\mathbf Q[\operatorname{forg}_b]$ |
| `graphRightPullback_baseComparison`, `graphSlicePullPush_baseComparison` | entire finite-cycle comparison squares, without ambient integrality | $\kappa_{2,*\mathrm{cyc}}\mathsf R^p_\tau=\mathsf R^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}}$, $\kappa_{3,*\mathrm{cyc}}\mathsf K^p_\tau=\mathsf K^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}}$ |

The numbered $\kappa_2,\kappa_3$ are scoped product inclusions, distinct
from the split-coordinate $\kappa_{JI}$ and the open extension inclusion
$\iota^{(2)}$. No second cycle, projector, or relation type is installed.
Products over $B$ are absolute over $k$ only when $B=\operatorname{Spec}k$.
Closed cycle pushforward is not asserted injective after passage to Chow.
SP35--SP38 supply actual principal-divisor construction and invariance
under support isomorphisms. SP39 adds compatible homogeneous degrees for
an explicit dimension function. SP40 constructs genuine relations and
quotient descent for closed pushforward and scheme isomorphisms. Geometric
dimension-function instantiation and general proper/flat/Gysin descent
remain separate gates to the target Chow operations.

### Signed local divisor coefficients (SP35)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| Mathlib `Ring.ord`, `Ring.ordFrac` / `SchemeCycles.localOrder` | actual principal-quotient length, extended to the fraction field and read as an integer on units | $\operatorname{ord}_A(f)$; one order, not a second valuation |
| `principalQuotient_length_ne_top`, `localOrder_algebraMap`, `localOrder_fraction` | finite lengths and fraction formula | $\operatorname{ord}_A(a/b)=\ell_A(A/(a))-\ell_A(A/(b))$ |
| `ord_ringEquiv`, `ordFrac_ringEquiv` | invariance of the actual length-defined order under compatible ring/field maps | prose only; compatibility theorem, not a new order input |
| Mathlib `Scheme.functionField` | actual generic-point stalk, a field for integral schemes | $k(X)=\mathcal O_{X,\eta_X}$ |
| `functionFieldIso` / `functionFieldEquiv` | categorical and ring presentations of one actual contravariant field isomorphism | $e^*:k(Y)\xrightarrow{\sim}k(X)$ |
| `functionFieldEquiv_algebraMap` | actual field/local-stalk compatibility | prose only; proved commutative square |
| `DivisorPoint X` | literal points with one-dimensional local ring | $\operatorname{DivPt}(X)=\{x:\dim\mathcal O_{X,x}=1\}$ |
| `divisorPointOfAffineHeightOne` | constructor from an actual affine-chart height-one prime | prose only; no second point index |
| `divisorPointEquiv e` | restriction of the actual scheme point equivalence | $e_1:\operatorname{DivPt}(X)\simeq\operatorname{DivPt}(Y)$ |
| `divisorOrder X x` | signed order through the canonical stalk-to-function-field algebra | $\operatorname{ord}_x:k(X)^\times\to\mathbf Z$ |
| `divisorOrder_iso` | local coefficient invariance through the actual geometric maps | $\operatorname{ord}_x(e^*f)=\operatorname{ord}_{e_1(x)}(f)$ |
| `Examples.localOrder_int_two`, `Examples.localOrder_int_two_inv` | computed nonzero signed coefficients, from $\mathbf Z/(2)$ having length one | $\operatorname{ord}_{\mathbf Z}(2)=1$, $\operatorname{ord}_{\mathbf Z}(1/2)=-1$; test only |

The algebra API allows Noetherian domains of dimension at most one; the
scheme index requires local dimension exactly one. No normality or DVR
premise, valuation inequality, divisor cycle, or arbitrary relation package
is introduced. `DivisorPoint` is not the boundary's ramified-prime/valuation
index. SP36 identifies it with the existing integral closed prime supports;
SP37 supplies finite support under quasi-compactness; SP38 assembles the
finite divisor cycle in the existing module.

### Actual prime supports (SP36)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `pointSupport X x` | actual reduced closed subscheme defined by the vanishing ideal of the point closure | $Z_x=(\overline{\{x\}})_{\mathrm{red}}$ |
| `ambientGenericPoint Z` | image of the integral subscheme's own generic point under its closed immersion | $\xi_Z=\iota_Z(\eta_Z)$; distinguish $\eta_Z\in Z$ from $\xi_Z\in X$ |
| `pointEquivIntegralClosedSubscheme X` | reduced closure and ambient generic point are inverse | $X\simeq\operatorname{IntSub}(X)$ |
| `pointClosureOrderIso`, `integralSupport` | topological irreducible point closure and the actual underlying closed support | $\overline{\{x\}}$, $|Z|$; underlying spaces, not additional scheme generators |
| `supportCodimension Z` | chain codimension of the actual irreducible closed support | $\operatorname{codim}(|Z|,X)$; not $\dim X-\dim Z$ |
| `supportCodimension_eq_stalkDim` | actual codimension/local-ring bridge | $\operatorname{codim}(|Z|,X)=\dim\mathcal O_{X,\xi_Z}$ |
| `PrimeDivisor X` | codimension-one subtype of the existing integral cycle generators | $\operatorname{PrimeDiv}(X)$ |
| `divisorPointEquivPrimeDivisor X` | existing divisor points identified with actual prime supports | $\operatorname{DivPt}(X)\simeq\operatorname{PrimeDiv}(X)$, $x\mapsto Z_x$ |
| `primeDivisorEquiv e`, `primeDivisorEquiv_val` | existing point transport on supports, proved equal to the scheme-theoretic image | $e_{\mathrm{div}}: \operatorname{PrimeDiv}(X)\simeq\operatorname{PrimeDiv}(Y)$, $Z\mapsto e(Z)$ |
| `closedImmersionPushforward_pointSupport` | compatibility with the existing finite-cycle pushforward | $f_{*,\mathrm{cyc}}[Z_x]=[Z_{f(x)}]$ for closed immersions |
| `primeDivisorOrder X Z` | the existing signed local order, reindexed by actual prime supports | $\operatorname{ord}_Z(f)=\operatorname{ord}_{\xi_Z}(f)$; no second order |
| `primeDivisorOrder_iso` | actual support/field coefficient comparison | $\operatorname{ord}_Z(e^*f)=\operatorname{ord}_{e_{\mathrm{div}}(Z)}(f)$ |

The support equivalence and codimension comparison hold for arbitrary
schemes. Integral locally Noetherian hypotheses are imposed only for the
existing signed coefficients. Codimension preservation is asserted for
isomorphisms, not for arbitrary closed immersions. The cycle module and
fundamental-cycle constructor are unchanged; no finite-support theorem,
graded principal divisor, quotient, projector, or relation package is
introduced by this checkpoint.

### Local and finite coefficient support (SP37)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `heightOne_mem_minimalPrimes_span` | height-one prime containing a nonzero element is minimal over its principal ideal | $\mathfrak p\in\operatorname{Min}(a)$; theorem, not a new support object |
| `finite_heightOne_primes_containing`, `finite_heightOne_primes_containing_either` | finite numerator/denominator prime bound in an arbitrary-dimensional Noetherian domain | $\{\mathfrak p:\operatorname{ht}\mathfrak p=1,\ a\in\mathfrak p\text{ or }b\in\mathfrak p\}$ |
| `exists_affine_fraction` | representation through the actual affine section-to-function-field map | $f=a/b$, $a,b\in\Gamma(U,\mathcal O_X)\setminus\{0\}$; auxiliary sections, not chosen cycle coefficients |
| `sectionToFunctionField_through_stalk`, `affineGerm_isUnit_iff` | actual section/stalk/field compatibility and unit-germ criterion | prose only; existing canonical maps |
| `divisorOrder_eq_zero_of_affine_fraction` | existing coefficient vanishes outside the numerator/denominator prime loci | $a,b\notin\mathfrak p_x\Rightarrow\operatorname{ord}_x(f)=0$; no converse asserted |
| `finite_divisorPoints_in_affine` | finite nonzero point-indexed coefficients in each affine chart | $\{x\in\operatorname{DivPt}(X):x\in U,\ \operatorname{ord}_x(f)\ne0\}$ |
| `primeDivisorSupports_locallyFinite` | locally finite family of the actual closed supports with nonzero coefficients | $(|Z|)_{Z\in\operatorname{PrimeDiv}(X),\ \operatorname{ord}_Z(f)\ne0}$; no new named projector or cycle type |
| `finite_primeDivisorOrder_support`, `finite_divisorOrder_support` | finite support of the same coefficient function under quasi-compactness, in its equivalent support/point indices | $\{Z:\operatorname{ord}_Z(f)\ne0\}$, equivalently $\{x:\operatorname{ord}_x(f)\ne0\}$ |

Local finiteness refers to the actual closed-support family, not just
point-finiteness of a set. Quasi-compactness is explicit only at the global
finite-support endpoint. No normality or global ring-dimension bound is
used, and the full prime-divisor type need not be finite. SP38 assembles
the finite principal-divisor cycle in the existing ungraded module;
SP39 gives its homogeneous degree for an explicit dimension function.

### Finite principal-divisor cycles and isomorphism transport (SP38)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `principalDivisor X f` | finite sum of the existing local orders on the existing prime-divisor subtype, embedded in the original cycle module | $\operatorname{div}_X(f)=\sum_Z\operatorname{ord}_Z(f)[Z]\in Z_{\mathrm{fin}}(X;\mathbf Z)$ |
| `principalDivisor_apply_prime`, `principalDivisor_apply_of_not_prime`, `principalDivisor_apply` | full coefficient formula on the original integral generators | $\operatorname{ord}_Z(f)$ at prime divisors, zero elsewhere; no new coefficient function |
| `principalDivisor_support`, `principalDivisor_eq_zero_iff` | exact finite support and coefficientwise zero criterion | $\operatorname{supp}(\operatorname{div}_X(f))=\{Z:\operatorname{ord}_Z(f)\ne0\}$ inside $\operatorname{IntSub}(X)$ |
| `principalDivisor_one`, `principalDivisor_mul`, `principalDivisor_inv`, `principalDivisor_div` | identity, product, inverse and quotient laws in the same cycle module | $\operatorname{div}_X(fg)=\operatorname{div}_X(f)+\operatorname{div}_X(g)$, $\operatorname{div}_X(f^{-1})=-\operatorname{div}_X(f)$ |
| `principalDivisorAddHom`, `principalDivisorAddHom_ofMul` | the same map bundled as a homomorphism, with an additive type tag on its multiplicative source | $\operatorname{div}_X:k(X)^\times\to Z_{\mathrm{fin}}(X;\mathbf Z)$; one map, not a second divisor |
| `closedImageSubschemeEquiv e` and its application lemmas | actual ideal-image equivalence on all existing integral cycle generators | $Z\mapsto e(Z)$ on $\operatorname{IntSub}$; extends the previously proved $e_{\mathrm{div}}$ |
| `closedImmersionPushforward_iso_eq_lmapDomain`, `_iso_apply_image`, `_iso_apply` | the existing geometric pushforward preserves coefficients at actual image supports | $(e_{*,\mathrm{cyc}}c)(e(Z))=c(Z)$ |
| `principalDivisor_iso` | pushforward/function-field compatibility through an actual scheme isomorphism | $e_{*,\mathrm{cyc}}\operatorname{div}_X(e^*f)=\operatorname{div}_Y(f)$ |
| `openRestriction_principalDivisor` | existing open restriction specialized to the same actual isomorphism | $e^*_{\mathrm{cyc}}\operatorname{div}_Y(f)=\operatorname{div}_X(e^*f)$ |

The principal-cycle endpoints have explicit integral, locally Noetherian
and quasi-compact hypotheses. The all-cycle coefficient transport holds
over any semiring without these ambient assumptions. No normality or DVR
assumption, zero-divisor/global-unit converse, new source hypothesis,
second cycle module, or relation package is introduced. Pullback of
principal divisors is asserted here only through an isomorphism, not an
arbitrary open immersion. SP39 supplies compatible dimension-function
degrees on relation supports and their ambient closed images. SP40 adds
genuine relations and closed-pushforward/isomorphism quotient descent.

### Dimension functions and homogeneous principal-divisor images (SP39)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `DimensionFunction X` | explicit integer-valued point function, strictly increasing in closure-inclusion order and incrementing by one across covers | $\delta:X\to\mathbf Z$; both conditions of the standard definition |
| `supportDegree δ Z` | degree of an existing integral support at its actual ambient generic point | $\deg_\delta(Z)=\delta(\xi_Z)$ |
| `primeDivisor_covBy_genericPoint`, `supportDegree_primeDivisor` | prime codimension gives immediate specialization and one-lower degree on an integral scheme | $\xi_Z\lessdot\eta_X$, $\deg_\delta(Z)=\delta(\eta_X)-1$ |
| `supportDegree_closedImageSubscheme` | degree of actual image support, even when only the support composite is closed | $\deg_\delta(f(Z))=\delta(f(\xi_Z))$ |
| `closedImmersion_covBy` | actual closed point embedding preserves immediate specialization | prose only; follows from the order-convex image |
| `DimensionFunction.comapClosedImmersion` and apply/id/comp laws | actual restriction of a dimension function, including both defining conditions | $\delta_W=\delta\circ\iota_W$, or $\delta\circ i$ |
| `supportDegree_comapClosedImmersion` | source degree equals actual ambient image degree | $\deg_{\delta\circ i}(Z)=\deg_\delta(i(Z))$; not codimension preservation |
| `cyclesOfDegree R δ n`, `mem_cyclesOfDegree_iff` | supported homogeneous submodule of the original cycle module | $Z^{\delta}_{\mathrm{fin},n}(X;R)\subset Z_{\mathrm{fin}}(X;R)$ |
| `single_mem_cyclesOfDegree`, `fundamentalCycle_mem_cyclesOfDegree`, `_iff` | generator membership and degree detection; the converse requires nontrivial coefficients | $[Z]\in Z^{\delta}_{\mathrm{fin},n}\iff\deg_\delta(Z)=n$ for nontrivial $R$ |
| `cyclesOfDegree_disjoint` | cycles of distinct degrees intersect only at zero | $Z^{\delta}_{\mathrm{fin},n}\cap Z^{\delta}_{\mathrm{fin},m}=0$ for $n\ne m$ |
| `closedImmersionPushforward_mem_cyclesOfDegree`, `_comap` | existing closed pushforward preserves compatible degrees; compatibility is proved for actual restriction | $i_{*,\mathrm{cyc}}Z^{\delta\circ i}_{\mathrm{fin},n}\subset Z^{\delta}_{\mathrm{fin},n}$ |
| `principalDivisor_mem_cyclesOfDegree` | existing finite principal divisor is one degree below the generic point | $\operatorname{div}_X(f)\in Z^{\delta}_{\mathrm{fin},\delta(\eta_X)-1}(X;\mathbf Z)$ |
| `closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree`, `principalDivisor_closedSupport_mem_cyclesOfDegree` | actual principal-divisor image has one-lower ambient carrier degree | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^{\delta}_{\mathrm{fin},\deg_\delta(W)-1}(X;\mathbf Z)$ |

Degree drop is proved from codimension inside the integral carrier, not
assumed of its divisor coefficients or computed by absolute Krull-dimension
subtraction. The topology and closed restriction need no local
Noetherianity; the finite principal cycle needs an integral locally
Noetherian quasi-compact carrier. The generic closed-cycle degree maps
work over any semiring, even trivial coefficients. The degree submodules
are not a second free cycle type, a direct-sum decomposition theorem,
a relation subgroup or a Chow quotient. A dimension function is explicit
input, not postulated to exist for every scheme. Constructing it from the
intended finite-type base and matching the target grading remain separate
from SP40's genuine relation generation and quotient descent.

### Genuine principal relations and closed quotient maps (SP40)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `idealSubscheme_isLocallyNoetherian`, `idealSubscheme_compactSpace`, `idealSubscheme_isNoetherian` | derived finiteness of actual closed carriers | prose only; no new hypothesis package |
| `closedImageSubscheme_isLocallyNoetherian`, `closedImageSubscheme_compactSpace` | finiteness transported by the actual support-to-image isomorphism | prose only; no new carrier |
| `ambientPrincipalDivisor W f` | the existing carrier principal cycle followed by the existing closed inclusion pushforward | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)$; a composite, not a second divisor |
| `closedImmersionPushforward_ambientPrincipalDivisor` | actual principal-generator image identity, using the inverse contravariant function-field isomorphism | $i_{*,\mathrm{cyc}}(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)=(\iota_{i(W)})_{*,\mathrm{cyc}}\operatorname{div}_{i(W)}((e_W^*)^{-1}f)$ |
| `PrincipalRelationData δ n` | actual integral degree-$n+1$ carriers with units in their function fields | $(W,f)$, $\deg_\delta(W)=n+1$, $f\in k(W)^\times$ |
| `principalRelationData_family_locallyFinite_iff` | local finiteness of actual nonempty carrier families is finiteness of the index under quasi-compactness | $(|W_a|)_{a\in A}$ locally finite $\Longleftrightarrow A$ finite |
| `principalRelation δ n d` | the same ambient principal image in the supported degree submodule | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^\delta_{\mathrm{fin},n}(X;\mathbf Z)$ |
| `PrincipalRelationData.zpow`, `principalRelation_zpow` | absorb integer coefficients into actual rational-function powers | $\operatorname{div}_W(f^m)=m\operatorname{div}_W(f)$ |
| `principalRelations δ n` | submodule generated by the actual degree-$n+1$ carrier principal images | $\mathcal R_n^\delta(X)$ |
| `mem_principalRelations_iff_exists_list`, `_iff_exists_finsupp` | exact unweighted finite-sum criterion and weighted finite-support criterion | $c\in\mathcal R_n^\delta\Longleftrightarrow c=\sum_{a=1}^r(\iota_{W_a})_{*,\mathrm{cyc}}\operatorname{div}_{W_a}(f_a)$ |
| `RationallyEquivalent δ n c e` and its equivalence laws | cycle difference is a genuine principal relation | $c\sim_{\mathrm{rat}}e$ |
| `ChowGroup δ n`, `classMap δ n` | quotient of the existing homogeneous integral cycles; canonical class map | $\mathrm{CH}_n^\delta(X)=Z^\delta_{\mathrm{fin},n}(X;\mathbf Z)/\mathcal R_n^\delta(X)$, $c\mapsto[c]$ |
| `classMap_eq_iff`, `classMap_eq_zero_iff`, `classMap_surjective`, `classMap_principalRelation` | exact quotient equality/kernel, surjectivity, and generator vanishing | $[c]=[e]\Longleftrightarrow c\sim_{\mathrm{rat}}e$, $\ker(c\mapsto[c])=\mathcal R_n^\delta$ |
| `gradedClosedImmersionPushforward` and val/id/comp laws | restriction of the existing cycle map to compatible homogeneous submodules | $i_{*,\mathrm{cyc}}$ with domain $Z^{\delta_X}_{\mathrm{fin},n}$ |
| `PrincipalRelationData.closedImage`, `gradedClosedImmersionPushforward_principalRelation` | actual image carrier/function and its proved generator identity | $(W,f)\mapsto(i(W),(e_W^*)^{-1}f)$ |
| `principalRelations_le_comap_closedImmersionPushforward` | preservation of the generated submodule, deduced from geometry | $i_{*,\mathrm{cyc}}\mathcal R_n^{\delta_X}(X)\subseteq\mathcal R_n^{\delta_Y}(Y)$ |
| `chowClosedImmersionPushforward` and classMap/id/comp laws | induced closed pushforward on the genuine quotient, with the existing cycle representative | $i_*:\mathrm{CH}_n^{\delta_X}(X)\to\mathrm{CH}_n^{\delta_Y}(Y)$, $[c]\mapsto[i_{*,\mathrm{cyc}}c]$ |
| `chowClosedImmersionPushforward_restricted_classMap` | canonical specialization where degree compatibility is already proved | $\delta_X=\delta_Y\circ i$ |
| `gradedIsoEquiv`, `_val`, `_symm_val` | actual homogeneous-cycle equivalence with inverse the existing open restriction | $e_{*,\mathrm{cyc}}$, with inverse $e^*_{\mathrm{cyc}}$ |
| `principalRelations_map_gradedIsoEquiv` | exact relation-submodule transport through the actual isomorphism | $e_{*,\mathrm{cyc}}\mathcal R_n^{\delta\circ e}(X)=\mathcal R_n^\delta(Y)$ |
| `chowIsoEquiv`, `_classMap`, `_symm_classMap`, `_toLinearMap` | induced quotient equivalence, identified with the existing closed quotient pushforward | $e_*:\mathrm{CH}_n^{\delta\circ e}(X)\xrightarrow{\sim}\mathrm{CH}_n^\delta(Y)$, with inverse induced by $e^*_{\mathrm{cyc}}$ |

The finite/local-finite comparison uses the closed **carriers**, including
carriers whose divisor is zero, not only nonzero divisor supports. The
unweighted finite-sum criterion identifies the generated subgroup with
the source convention on the chosen Noetherian domain. Integer scalars
are absorbed by actual function powers, not by a supplied relation axiom.
The dimension function is explicit, and the canonical closed restriction
provides the degree comparison. Relation preservation is proved, not a
theorem premise. The quotient is additive; no general closed-pushforward
injectivity, arbitrary open/flat/Gysin descent, proper norm theorem,
intersection product, Chow convolution or Hodge realization is supplied.
The new class notation $[c]$ is distinct from the existing Betti cycle
class map and the Hodge quotient selector. This does not install a second
cycle module or projector; the earlier finite-split zero-cycle adapter
remains separately scoped and has not been silently identified with this
general quotient. Its comparison is a later parity adapter if needed.
The general quotient here has integer coefficients; rational coefficient
extension and comparison with the prescribed rational Chow target remain
separate from the already proved finite-split scalar-extension adapter.

### Actual dimensions and a canonical low-dimensional grading (SP41)

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `integralSubschemePointOrderIso W`, `_val` | actual points of the closed carrier are the specialization interval below its ambient generic point | $\lvert W\rvert\simeq\{x:x\leq\xi_W\}$; the point map is the existing inclusion |
| `topologicalKrullDim_eq_pointKrullDim` | sobriety identifies point chains with irreducible-closed chains | $\dim X$; no second dimension invariant |
| `ambientGenericPoint_height_eq_supportDim`, `point_height_eq_supportDim`, `genericPoint_height_eq_topologicalKrullDim` | actual carrier dimension is generic-point height; the whole integral scheme is the generic closure | $\dim W=\operatorname{height}(\xi_W)$, $h_X(x)=\dim\overline{\{x\}}$ |
| `point_height_ne_top`, `point_height_toNat_eq`, `point_height_toNat_strictMono` | finite dimension makes conversion to integer height lossless and gives strict specialization monotonicity | $h_X:X\to\mathbf Z_{\geq0}$ when $\dim X<\infty$; not yet called a dimension function in general |
| `polynomialDimensionBound`, `mvPolynomial_ringKrullDim_le_bound`, `ringKrullDim_le_bound_of_surjective` | explicit finite upper bound from actual polynomial presentations | proof-local bound only; not a sharp dimension formula or a new grading |
| `exists_ringKrullDim_le_of_finiteType`, `ringKrullDim_lt_top_of_finiteType`, `finiteRingKrullDim_of_finiteType` | finite-type field algebras have finite dimension; nonempty order package additionally requires a nontrivial ring | $\dim A<\infty$ |
| `spec_topologicalKrullDim_lt_top_of_finiteType`, `quotientSpec_topologicalKrullDim_lt_top_of_finiteType`, `affine_topologicalKrullDim_lt_top_of_finiteType` | bounds on actual affine spectra, quotient spectra and affine schemes with their section algebras | $\dim\operatorname{Spec}A<\infty$ |
| `point_coheight_eq_of_isOpenImmersion` | actual stalk isomorphisms preserve point coheight | $\operatorname{coheight}_U(x)=\operatorname{coheight}_X(jx)$; not height or absolute-dimension preservation |
| `topologicalKrullDim_lt_top_of_finite_openCover` | finite chart bounds control global point-chain dimension | $\dim X\leq\max_i\dim U_i<\infty$ |
| `affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType`, `topologicalKrullDim_lt_top_of_compact_locallyOfFiniteType`, `topologicalKrullDim_lt_top_of_finiteType` | the actual structural morphism supplies the affine finite-type algebras; quasi-compactness supplies the finite subcover | $X\to\operatorname{Spec}k$ finite type $\Longrightarrow\dim X<\infty$ |
| `point_height_le_one`, `point_height_eq_zero_and_eq_one_of_lt` | under the actual dimension bound, every strict pair has heights zero and one | $x<y\Longrightarrow(h_X(x),h_X(y))=(0,1)$ if $\dim X\leq1$ |
| `DimensionFunction.ofKrullDimLEOne` and its apply/nonneg/value laws | the existing dimension-function type instantiated by literal point height, with both laws proved | $\delta_X:=h_X$ under $\dim X\leq1$; no extra grading-law input |
| `supportDegree_ofKrullDimLEOne_eq_iff`, `fundamentalCycle_mem_ofKrullDimLEOne_iff` | the existing support degree and homogeneous-cycle test match actual carrier dimension | $\deg_{\delta_X}(W)=n\Longleftrightarrow\dim W=n$, $[W]\in Z^{\delta_X}_{\mathrm{fin},n}\Longleftrightarrow\dim W=n$ for nontrivial coefficients |
| `Examples.affineLine`, `affineLine_dimension`, `affineLineDimensionFunction` | the actual polynomial spectrum and its constructed dimension function | $\mathbf A^1_k=\operatorname{Spec}k[T]$, $\delta_{\mathbf A^1_k}$ |
| `Examples.affineLineOriginIdeal_isMaximal`, `affineLineOrigin`, `affineLineOrigin_isClosed` | the actual origin is the prime kernel of the constant-coefficient map | $o=V(T)$; no freely chosen closed point |
| `Examples.affineLineDimensionFunction_genericPoint`, `affineLineDimensionFunction_origin` | explicit positive-dimensional checks of the constructed grading | $\delta(\eta)=1$, $\delta(o)=0$ |

The carrier-height theorem has no ambient geometric assumptions. The
finite-type bounds include the empty spectrum and do not use the pinned
Mathlib's unproved exact multivariate-polynomial dimension statement.
Finite-dimensionality gives finite, strictly monotone height, but not the
unit step across covers. Only the dimension-at-most-one case is installed
as a `DimensionFunction` here, without integrality or Noetherianity of the
ambient scheme. Its use in SP40 still requires the existing Noetherian
quotient hypotheses. SP42 subsequently proves the affine
transcendence-degree comparison. In higher-dimensional finite-type
geometry, the uniform-chain theorem, one-step law and general scheme
grading remain open.
The target's codimension convention and rational coefficient comparison
also remain separate; mixed-dimensional components do not acquire a
silently chosen global $d-p$ conversion. There is one cycle module, one
principal-relation quotient construction and no new projector or source axiom.

### Selected literature inputs

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `NormalizationInertia.InertiaFixedRingUnramifiedAt` in `Inputs/FixedInertia.lean` | canonical selected-prime unramifiedness premise, unchanged after its move | $h_I:\operatorname{Unram}_{q_I}(A\to S^I)$ |
| `inertiaFixedRingUnramifiedAt_iff` | lossless unbundling into the existing Mathlib premise | prose only; no second input |
| `LiteratureInputs.FiniteEtaleExtension j p` | actual finite étale extension with its pullback identification | $\mathscr E_j(p)\ni E=(\bar p:\bar Y\to X,\;Y\simeq U\times_X\bar Y)$ |
| `FiniteEtaleExtensionHypothesis j p` | selected existence proposition | $\mathscr E_j(p)\ne\varnothing$ |
| `FiniteEtaleExtension.restriction` | actual pullback and conjugation map on automorphisms | $\operatorname{res}_E:\operatorname{Aut}_X(\bar Y)\to\operatorname{Aut}_U(Y)$ |
| `DeckExtensionHypothesis E` | bijectivity of that selected restriction map | $\operatorname{Bijective}(\operatorname{res}_E)$ |
| `FiniteEtaleExtension.deckEquiv` / `liftDeckAction` | restriction as a multiplicative equivalence, and action transport by its inverse | $\operatorname{res}_E:\operatorname{Aut}_X(\bar Y)\simeq\operatorname{Aut}_U(Y)$ / $\bar\rho_G=\operatorname{res}_E^{-1}\circ\rho_G$ |
| `ChowLocalizationHypotheses i r` | selected additive exactness and surjectivity | $\operatorname{im}i=\ker r,\quad r\text{ surjective}$ |
| `ChowLocalization.projectorClosure` | literal raw-lift fiber, reusing the canonical closure interface | $\operatorname{Cl}_r(e_\eta)=\{\Pi:r(\Pi)=e_\eta\}$ |
| `ChowLocalization.convolutionDefect_mem_range` / `exists_boundary_of_convolutionDefect` | conditional boundary preimage of the existing defect, with a separate algebra restriction | $\operatorname{Def}(\Pi)\in\operatorname{im}i$, equivalently $i(b)=\Pi^2-\Pi$ |

The extension witness and its existence proposition are different objects;
neither implies the deck-restriction proposition. Additive exactness does not
assert that restriction is an algebra map. The boundary element `b` need not
be unique or zero. No new symbol is assigned to the input umbrella or to
routine adapters, and the old fixed-ring module imports the sole canonical
record rather than copying it.

### Marked block, realization, and Hodge target

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `MarkedSheetProjector.Residual H` | augmentation ideal of the pointwise sheet algebra | $E_H=\ker(\operatorname{ev}_H)=(1-q_H)\triangleleft F_{\mathbf Q}(H)$ |
| `MarkedAugmentedAlgebra.ResidualCorner` | unital residual corner, with the same underlying ideal and internal unit | $E_H^{\mathrm{corner}},\quad 1_{E_H^{\mathrm{corner}}}=1-q_H$ |
| `MarkedAugmentedAlgebra.selectorAlgebraDecomposition` | genuine selector/CRT product decomposition of algebras | $A_H\simeq_{\mathbf Q\text{-alg}}\mathbf Q\times E_H^{\mathrm{corner}}$ |
| `MarkedSheetProjector.residualClass H` | marked residual class | $a_H=q_H-1\in E_H$ |
| `MarkedAugmentedAlgebra.regularAction` | multiplicative regular action of the commutative source | $\lambda_H:F_{\mathbf Q}(H)\to\operatorname{End}_{\mathbf Q}(F_{\mathbf Q}(H))$ |
| `UniversalIdempotentAlgebra ℚ` | universal rational algebra with one distinguished idempotent | $\mathcal U=\mathbf Q\times\mathbf Q$ |
| `UniversalIdempotentAlgebra.selector` | distinguished universal idempotent | $u=(1,0)\in\mathcal U$ |
| `UniversalIdempotentAlgebra.mapOfIdempotent` | canonical algebra map determined by an idempotent $e$ in a rational algebra $B$ | $\varphi_e:\mathcal U\to B$, $(r,s)\mapsto re+s(1-e)$ |
| `UniversalIdempotentAlgebra.RepresentationMorphism` | linear intertwiner between two one-idempotent representations | $T:(V,\varphi_{e_V})\to(W,\varphi_{e_W})$ |
| `MarkedSelectorAlgebraPresentation` | optional stronger full component-algebra presentation; not required by the active Galois route | $\iota_H:F_{\mathbf Q}(H)\to\Gamma_\eta$ |
| `SchemeCorrespondence.sheetLinearization H` | auxiliary direct-import-only linear coset-average comparison, not an algebra map | $\ell_H(gH)=[g]e_H$ |
| generic graph operator | graph projector attached to $\alpha$ | $P_\alpha(t,x)=(t,t\alpha)$ |
| generic diagonal operator | projector onto the marked rational line | $P_0(t,x)=(t,0)$ |
| generic shear | change from diagonal to graph splitting | $U_\alpha(t,x)=(t,x+t\alpha)$ |
| `MarkedProjectorActionComparison` | canonical residual map and action square for a chosen projector, without ambient restriction | $\mathscr R_{\Pi}$ |
| `MarkedProjectorActionComparison.cycleClass_decode_eq_generatedClass` | detected Chow representative from the core comparison, without surjectivity or original idempotence | $\operatorname{cl}(D(\Pi))=\theta(a_H)$ |
| `MarkedProjectorActionComparison.toAlgebraicProjectorLift` | full lift using the chosen idempotent and surjective cancellation | $\Pi$; the same chosen element |
| `MarkedSelectorActionComparison` | extension-based specialization of the canonical comparison | $\mathscr R_{\Pi_x}$; no independent comparison fields |
| `MarkedGaloisSelectorComparison` | sheet specialization with prescribed generated class | $\mathscr R_{\alpha,x}$; retains the extension premise |
| residual realization | rational linear map from the underlying module of the augmentation ideal | $\theta:E_H\to V$ |
| `MarkedAugmentedAlgebra.productRealization` | Tate-augmented residual map | $\Theta=\operatorname{id}_{\mathbf Q}\oplus\theta$ |
| `MarkedGaloisSelectorComparison.palomarTargetSquare` | realized projector equality as algebra-homomorphism composites | $\rho\circ\varphi_\Pi=\varphi_{P_\alpha}$ |
| `RationalCorrespondenceAction` | compactified correspondence action | $\rho:\overline\Gamma\to\operatorname{End}_{\mathbf Q}(\mathbf Q\oplus V)$ |
| `RationalChowCorrespondenceModel` | generic/restriction/action package | $\mathscr C_{\mathrm{Chow}}$ |
| `RationalCohomologicalProjector` | independently specified target projector | $P$ |
| `PrescribedChowProjectorLift` | lift with prescribed action | $\operatorname{Lift}_{\mathrm{CH}}(P)$ |
| `AlgebraicProjectorLift.realization_idempotentMap_square` | one lift displayed as a commuting algebra-homomorphism square | $\rho\circ\varphi_\Pi=\varphi_P$ |
| `RationalHodgeCycleClassModel` | supplied cycle/Hodge model | $\mathscr H=(A,V,V_{\mathrm{Hdg}},\operatorname{cl})$ |
| `ClassGraphProjectorConstruction.encode` | graph construction from a supplied Chow class, used in the Hodge-to-graph equivalence direction; not asserted linear | $C:A\to\Gamma$ |
| `ClassGraphProjectorDetection.decode` | linear Chow detection compatible with lower-left cohomological evaluation | $D:\Gamma\to_{\mathbf Q} A$ |
| `IsRationalHodgeClass M alpha` | rational Hodge membership | $\alpha\in V_{\mathrm{Hdg}}$ |
| `IsAlgebraicHodgeClass M alpha` | cycle-class membership | $\alpha\in\operatorname{im}(\operatorname{cl})$ |
| `RationalHodgeConjectureAt M` | modeled rational Hodge target | $\mathrm{HC}_{\mathbf Q}(\mathscr H)$ |
| `EveryHodgeClassHasPalomarTargetSquare` | equality-of-composites presentation of graph-projector coverage | $\forall\alpha\in V_{\mathrm{Hdg}},\ \exists\Pi:\rho\circ\varphi_\Pi=\varphi_{P_\alpha}$ |
| `ClassDependentMarkedGaloisSelectorCoverage` | classwise marked-selector coverage | $\operatorname{Cov}_{\mathrm{Gal}}(\mathscr H,\rho)$ |
| `StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector` | existential replacement for the same target class, used only for the reverse coverage implication; no equality with an original projector | named hypothesis; no new projector notation |

### Exact affine dimension and actual carrier comparison (SP42)

Here \(k\) is a field, \(A\) a commutative \(k\)-algebra and
\(\kappa(p)\) the actual residue field of \(A_p\). Transcendence
degrees in the dimension formulas are finite, so Lean's conversion from
cardinals to natural numbers is lossless. The existing \(h_X\) notation
denotes point-closure dimension; no general \(\delta_X\) is constructed
in this checkpoint.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `trdeg_lt_of_surjective_of_not_injective` | strict degree drop under an actual noninjective domain surjection with finite transcendence degree | $A\twoheadrightarrow B,\ \ker f\ne0\implies\operatorname{trdeg}_kB<\operatorname{trdeg}_kA$ |
| `primeQuotient_trdeg_strictAnti` / `primeQuotient_trdeg_toNat_strictAnti` | strict decrease on actual prime quotients of a finite-type algebra | $p\subsetneq q\implies\operatorname{trdeg}_k(A/q)<\operatorname{trdeg}_k(A/p)$ |
| `integral_specComap_strictMono` | actual prime contraction and incomparability for an integral map | $P\subsetneq Q\implies f^{-1}P\subsetneq f^{-1}Q$ |
| `exists_primeSeries_lift_of_injective_integral` | actual finite-chain lift by lying over and going up, preserving length and the last contraction | $\ell(\widetilde c)=\ell(c),\ f^{-1}(\widetilde c_{\mathrm{last}})=c_{\mathrm{last}}$ |
| `ringKrullDim_le_of_integral` / `ringKrullDim_le_of_injective_integral` / `ringKrullDim_eq_of_injective_integral` | extended dimension comparison; injectivity is required for the reverse inequality and equality | $\dim S\le\dim R;\ R\hookrightarrow S\implies\dim R=\dim S$ |
| `trdeg_eq_normalization_size` / `normalization_size_le_ringKrullDim` | actual injective integral polynomial normalization; domain needed for the transcendence-degree identity, not the dimension lower bound | $k[T_1,\ldots,T_s]\hookrightarrow A,\ s=\operatorname{trdeg}_k A,\ s\le\dim A$ |
| `trdeg_toNat_le_ringKrullDim_of_finiteType` / `ringKrullDim_le_trdeg_toNat_of_finiteType` | independent normalization lower bound for domains and prime-chain upper bound for all finite-type algebras | $\operatorname{trdeg}_k A\le\dim A;\ \dim A\le\operatorname{trdeg}_k A$ |
| `trdeg_eq_of_isFractionRing` / `trdeg_eq_fractionRing` | actual fraction-field algebra and scalar-tower comparison | $\operatorname{trdeg}_kA=\operatorname{trdeg}_k\operatorname{Frac}(A)$ |
| `ringKrullDim_eq_trdeg_toNat_of_finiteType` / `ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType` | finite-type domain dimension equality | $\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)$ |
| `mvPolynomial_ringKrullDim_eq_card` | proved sharp polynomial formula over a field | $\dim k[T_1,\ldots,T_n]=n$ |
| `spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType` | topological dimension of the actual affine scheme of a finite-type domain | $\dim\operatorname{Spec}A=\operatorname{trdeg}_kA$ |
| `prime_coheight_eq_quotientDim` / `spec_point_height_eq_prime_coheight` | opposite prime/scheme orders; actual quotient dimension | $\operatorname{coht}_{\operatorname{Spec}_{\mathrm{prime}}A}(p)=\operatorname{ht}_{X}(p)=\dim(A/p)$ |
| `spec_pointSupport_dimension_eq_quotientDim` | existing reduced point carrier, not a new proxy type | $\dim\overline{\{p\}}_{\mathrm{red}}=\dim(A/p)$ |
| `primeQuotient_trdeg_eq_residueField` | actual prime-localization residue field is a fraction field of the quotient | $\operatorname{trdeg}_k(A/p)=\operatorname{trdeg}_k\kappa(p)$ |
| `spec_pointSupport_dimension_eq_residueField_trdeg` / `spec_point_height_toNat_eq_residueField_trdeg` | finite-type affine carrier dimension and the existing finite point-height value | $h_X(p)=\dim\overline{\{p\}}=\operatorname{trdeg}_k\kappa(p)$ |
| `prime_residueField_trdeg_toNat_strictAnti` | strict decrease on proper affine specialization | $p\subsetneq q\implies\operatorname{trdeg}_k\kappa(q)<\operatorname{trdeg}_k\kappa(p)$ |

No maximal-localization dimension identity, uniform maximal-chain theorem,
immediate-specialization unit step, general scheme chart/residue-field
transport or new dimension-function constructor is included in SP42.
The existing cycle module, Chow quotient and chosen projector are unchanged.

### Polynomial maximal height and closed-point local dimension (SP43)

Write \(R_n=k[T_1,\ldots,T_n]\), with \(k\) any field, and
\(X_n=\operatorname{Spec}R_n\). In the generic helper \(R\) is any
commutative ring and \(C:R\to R[T]\) is the actual constant-polynomial
homomorphism. No new cycle object or dimension-function package is used.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `polynomial_comap_map_C` | contraction is a left inverse to ideal extension | $C^{-1}(pR[T])=p$ |
| `polynomialPrimeExtension` | actual order embedding of prime ideals | $\operatorname{Spec}_{\mathrm{prime}}R\hookrightarrow\operatorname{Spec}_{\mathrm{prime}}R[T],\ p\mapsto pR[T]$ |
| `polynomialPrimeExtension_height_le` | extending prime chains does not decrease height | $\operatorname{ht}(p)\leq\operatorname{ht}(pR[T])$ |
| `polynomial_map_C_not_isMaximal` | polynomial quotient obstruction for any ideal | $pR[T]\notin\operatorname{MaxSpec}R[T]$ |
| `polynomial_map_comap_C_lt` | actual contracted-prime extension is strictly below a maximal ideal | $(m\cap R)R[T]\subsetneq m$ |
| `polynomial_primeHeight_comap_add_one_le` | one extra height step, not an equality or catenarity assertion | $\operatorname{ht}(m\cap R)+1\leq\operatorname{ht}(m)$ |
| `mvPolynomial_primeHeight_eq_card_of_isMaximal` / `mvPolynomial_height_eq_card_of_isMaximal` | full height for every polynomial maximal ideal | $\operatorname{ht}_{R_n}(m)=n$ |
| `mvPolynomial_localization_dimension_of_isMaximal` | dimension of the actual prime localization | $\dim(R_n)_m=n$ |
| `mvPolynomial_stalk_dimension_of_isMaximal` / `mvPolynomial_stalk_dimension_of_isClosed` | dimension of the actual structure-sheaf stalk | $\dim\mathcal O_{X_n,m}=n$ |
| `mvPolynomial_closedPoint_coheight` | coheight in the scheme's closure-inclusion order | $\operatorname{coht}_{X_n}(m)=n$ |

The result includes \(n=0\) and non-rational closed points. Scheme-point
height and closed-carrier dimension are zero at these closed points;
they are not the local dimension. The generic inequality alone does not
give an immediate-specialization unit step. General finite-type-domain
maximal-local comparison, normal-base going down, uniform saturated chains,
general scheme grading and the target Chow operations remain subsequent
proof obligations. No regularity or generator theorem is asserted here.

### Normal-base going down and finite-type-domain local dimension (SP44)

Here \(R\hookrightarrow S\) denotes the actual algebra map; normality
means integral closedness of the domain \(R\) in its fraction field.
For the normalization application \(A\) is a domain over a field \(k\),
and \(g:k[T_1,\ldots,T_s]\hookrightarrow A\) is the actual integral
normalization map. Neither \(A\) nor \(S\) is assumed normal.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `exists_monic_annihilator_coeff_mem_pow_of_mem_map` / `exists_monic_annihilator_of_mem_map` | actual finite integral subalgebra and determinant-trick annihilator; no global module finiteness | $y\in IS\implies\exists F\text{ monic},\ F(y)=0,\ F_i\in I^{d-i}\ (d=\deg F)$ |
| `monic_map_eq_X_pow_of_lower_coeff_zero` | actual coefficient-map reduction of a monic polynomial | $\overline F=X^{\deg F}$ |
| `coeff_mem_prime_of_monic_dvd_scaled` / `coeff_mem_prime_of_monic_dvd` | prime-ideal coefficient comparison for actual monic divisors, including scalar substitution | $G\mid F(aX),\ a\notin p,\ F_i\in p\ (i<\deg F)\implies G_j\in p\ (j<\deg G)$ |
| `mem_prime_of_mul_mem_map_of_isIntegrallyClosed` | normal-base cancellation relative to the prescribed upstairs prime | $p\subseteq Q\cap R,\ a\notin p,\ ab\in pS\implies b\in Q$ |
| `hasGoingDown_of_isIntegrallyClosed` | proved going down for integral injections of domains with normal base; no new global instance | $p\subseteq Q\cap R\implies\exists P\subseteq Q,\ P\cap R=p$ |
| `primeHeight_eq_under_of_isIntegral_of_hasGoingDown` | integral incomparability plus reuse of the existing going-down height bound | $\operatorname{ht}_S(Q)=\operatorname{ht}_R(Q\cap R)$ |
| `normalization_primeHeight_eq_size` | full maximal height from the actual polynomial normalization, without a finite-type assumption on A | $g:k[T_1,\ldots,T_s]\hookrightarrow A\text{ integral}\implies\operatorname{ht}_A(m)=s$ |
| `primeHeight_eq_trdeg_toNat_of_isMaximal` / `height_eq_trdeg_toNat_of_isMaximal` | finite-type-domain maximal heights | $\operatorname{ht}_A(m)=\operatorname{trdeg}_k A$ |
| `localization_dimension_eq_of_isMaximal` | dimension of the actual prime localization | $\dim A_m=\dim A$ |
| `affine_stalk_dimension_of_isMaximal` / `affine_stalk_dimension_of_isClosed` | dimension of the actual structure-sheaf stalk on X=Spec(A) | $\dim\mathcal O_{X,m}=\dim A$ |
| `affine_closedPoint_coheight_eq_trdeg` | actual scheme-order coheight at a closed point | $\operatorname{coht}_X(m)=\operatorname{trdeg}_k A$ |

The prime-height comparison theorem exposes its generic going-down premise;
the normalization and finite-type endpoints discharge that premise using
the proved normal-base theorem. The existing
`NormalizationInertia.primeHeight_under_le_of_hasGoingDown` is reused,
not copied. The older finite-invariant going-down theorem remains distinct:
it does not require a normal base, so this new theorem does not replace it.
No source-input package, scalar-linear proxy, new cycle space
or dimension-function assumption is introduced. The actual local-ring
comparison does not assume its map remains integral after localization
at a selected upstairs prime. Maximal-local equality does not yet prove
uniform saturated chains or the higher-dimensional immediate-specialization
unit-step law, and it does not construct general target realization.
The subsequent residue-normalization construction is recorded in SP45
below. It is the input to the affine prime dimension formula and then
the consecutive-prime unit-step law, not a consequence of maximal-local
equality alone.

### Residue-normalization localization (SP45)

Here \(\pi_q:B\to B/q\) is the actual quotient map,
\(g:P=k[T_1,\ldots,T_n]\hookrightarrow B/q\) is an integral
normalization and \(f:P\to B\) its chosen lift. Set
\(M=f(P\setminus\{0\})\), \(B'=M^{-1}B\),
\(K=\operatorname{Frac}(P)\), \(\lambda:B\to B'\), and
\(q'=qB'\). The finite-type construction allows any commutative
\(B\); only the transcendence-degree consumer requires a domain.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `quotientPolynomialLift` / `quotient_comp_quotientPolynomialLift` | chosen lifts of actual quotient variables and exact quotient square | $f:P\to B,\quad\pi_q f=g$ |
| `quotientPolynomialLift_injective` / `polynomial_notMem_of_quotient_injective` / `quotientPolynomialLift_notMem` | injection and nonzero polynomial images avoid the selected prime | $f\text{ injective},\ a\ne0\implies f(a)\notin q$ |
| `polynomial_map_nonZeroDivisors_le_primeCompl` / `polynomial_map_nonZeroDivisors_disjoint` | actual denominator image submonoid | $M\subseteq B\setminus q$ |
| `exists_lifted_residue_normalization` | Noether normalization of the actual prime quotient and variable lift | $\exists n,f:\ \pi_q f\text{ injective and integral}$ |
| `genericFiberAlgebra` / `genericFiberAlgebra_algebraMap_eq` | canonical localized algebra map, not a new carrier | $K\to B'$ |
| `genericFiberAlgebra_isScalarTower` / `genericFiber_isScalarTower_base` | exact compatibility of the actual scalar maps | $P\to K\to B',\quad k\to K\to B'$ |
| `genericFiber_finiteType` | actual localization pushout gives finite type | $B\text{ finite type over }P\implies B'\text{ finite type over }K$ |
| `genericFiber_denominators_le_nonZeroDivisors` / `genericFiber_isDomain` / `genericFiber_localization_injective` / `genericFiber_baseField_injective` | domain and injection properties of the actual localization | $B\text{ domain},\ P\hookrightarrow B\implies B'\text{ domain},\ B\hookrightarrow B',\ K\hookrightarrow B'$ |
| `residueLocalization_comap_map` / `residueLocalization_map_isPrime` | actual contraction and primality, requiring only quotient injectivity | $\lambda^{-1}(q')=q,\quad q'\text{ prime}$ |
| `residueLocalization_map_isMaximal` | field from the localized integral prime quotient, with exact kernel | $B'/q'\text{ field},\quad q'\text{ maximal}$ |
| `residueLocalization_primeHeight_map` | exact prime height under actual localization; no integral premise | $\operatorname{ht}_{B'}(q')=\operatorname{ht}_B(q)$ |
| `residueNormalization_localization` / `exists_residueNormalization_localization` | supplied-map and fully constructed finite-type localization endpoints | $B'/K\text{ finite type},\ q'\text{ maximal},\ \lambda^{-1}(q')=q,\ \operatorname{ht}(q')=\operatorname{ht}(q)$ |
| `primeHeight_eq_residueNormalization_trdeg` | SP44 applied to the actual domain generic fiber | $\operatorname{ht}_B(q)=\operatorname{trdeg}_K B'$ |

The generic algebra and localized-prime lemmas accept arbitrary actual
models of the localization; the existential endpoint uses literal
`Localization` and `FractionRing`, with the canonical algebra installed
locally. The pushout proof does not replace the carrier by a tensor proxy.
Only the quotient normalization is integral: \(P\to B\) is not
declared integral. No new axiom, input package, global algebra instance,
cycle space, Chow quotient or projector is introduced.

The subsequent original-field comparison and affine prime formula are
recorded in SP46 below. The consecutive-prime unit step, actual scheme-chart
transport, general grading and target realization remain subsequent
obligations.

### Original-field prime dimension formula (SP46)

Keep the SP45 notation \(P=k[T_1,\ldots,T_n]\),
\(K=\operatorname{Frac}(P)\), \(M=f(P\setminus\{0\})\) and
\(B'=M^{-1}B\). The original-field prime formula assumes that \(B\)
is a finite-type domain; the generic localization comparison needs neither
finite type nor finite transcendence degree.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `lift_trdeg_eq_of_isLocalization` / `trdeg_eq_of_isLocalization` | full cardinal degree preserved by the actual localization; universe lifts in the general form | $\operatorname{trdeg}_k B=\operatorname{trdeg}_k M^{-1}B$ |
| `trdeg_toNat_eq_of_isLocalization` | numeric consequence of cardinal invariance; not a finiteness assertion | Numeric projection of the preceding equality; no independent invariant |
| `polynomial_genericFiber_trdeg_toNat_add` | canonical fraction-field tower for an actual injective polynomial map, with no integral premise | $n+\operatorname{trdeg}_K B'=\operatorname{trdeg}_k B$ |
| `primeHeight_add_quotient_trdeg_eq` / `height_add_quotient_trdeg_eq` | original-field dimension formula for every prime of a finite-type domain | $\operatorname{ht}_B(q)+\operatorname{trdeg}_k(B/q)=\operatorname{trdeg}_k B$ |
| `primeHeight_add_residueField_trdeg_eq` | reuse of the existing actual prime-localization residue field | $\operatorname{ht}_B(q)+\operatorname{trdeg}_k\kappa(q)=\operatorname{trdeg}_k B$ |
| `height_add_quotient_dimension_eq` | actual prime quotient dimension plus ordinary ideal height | $\operatorname{ht}_B(q)+\dim(B/q)=\dim B$ |
| `localization_dimension_add_quotient_dimension_eq` | dimension of the actual prime localization | $\dim B_q+\dim(B/q)=\dim B$ |

The first comparison retains full cardinal information, including infinite
transcendence degree. In the polynomial generic-fiber application, both cardinal summands
are proved finite before converting the sum to natural numbers. The finite
transcendence degree of \(K/k\) is proved from the variable count, not by assuming
that the rational function field is a finite-type \(k\)-algebra. The
prime-height formula is an equality in \(\mathbb N\cup\{\infty\}\),
so prime-height finiteness is a conclusion, not an added hypothesis.
The generic helper does not need a prime or an integral polynomial map.
The actual residue-field adapter reuses
`primeQuotient_trdeg_eq_residueField`; no new residue-field model, source
input package, scalar-linear proxy or global algebra instance is introduced.

The subsequent consecutive-prime unit drop is recorded in SP47 below.
Actual scheme-chart transport, the general dimension-function constructor,
target codimension grading and realization remain separate.

### Consecutive-prime unit drop (SP47)

Here \(p\lessdot q\) means a cover in \(\operatorname{Spec}B\),
ordered by prime-ideal inclusion. Put \(\bar q=q(B/p)\), the actual
image under the quotient map. This notation does not denote a cover in
the full ideal lattice. For scheme points the order is reversed.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `primeQuotient_map_isPrime` | primality under the actual quotient map, for a comparable prime pair | $p\subseteq q\implies\bar q=q(B/p)\text{ prime}$ |
| `primeQuotient_bot_covBy_map` | actual quotient-spectrum correspondence on a prime cover | $p\lessdot q\implies0\lessdot\bar q\text{ in }\operatorname{Spec}(B/p)$ |
| `primeQuotient_primeHeight_eq_one_of_covBy` | full prime height of the actual image ideal | $\operatorname{ht}_{B/p}(\bar q)=1$ |
| `primeQuotient_trdeg_toNat_add_one_of_covBy` | finite transcendence-degree unit drop between actual prime quotients | $\operatorname{trdeg}_k(B/q)+1=\operatorname{trdeg}_k(B/p)$ |
| `prime_residueField_trdeg_toNat_add_one_of_covBy` | same unit drop in the existing actual prime-localization residue fields | $\operatorname{trdeg}_k\kappa(q)+1=\operatorname{trdeg}_k\kappa(p)$ |
| `primeQuotient_dimension_add_one_of_covBy` | actual quotient-ring dimension step | $\dim(B/q)+1=\dim(B/p)$ |

The quotient-prime lemmas require only a commutative ring. The three
dimension consequences require a finite-type algebra over a field, but
no domain, reducedness, normality or equidimensionality of \(B\).
Only its actual quotient \(B/p\) is used as a domain. The double-quotient
comparison is an actual \(k\)-algebra equivalence, retaining the field
action needed for transcendence degree. The existing residue-field
comparison is reused; no replacement quotient, residue-field model,
catenarity input, dimension-function premise, global instance, cycle space,
Chow quotient or projector is introduced. Quotient-dimension drop is not
identified with an ambient local-ring dimension increment on arbitrary
reducible algebras.

SP48 below combines the strict degree drop, unit law and existing
prime/scheme order reversal into an actual affine `DimensionFunction`.
General chart transport and the structural-field residue-field comparison
remain separate; no unrestricted preservation of absolute point height
under open immersion is assumed.

### Actual affine dimension functions (SP48)

For a finite-type algebra \(A\) over \(k\), write
\(\delta_{A/k}\) for the constructed function on the actual affine
spectrum. For an affine scheme with structural morphism
\(p:X\to\operatorname{Spec}k\) locally of finite type, write
\(\delta_{X/k}\) for the corresponding intrinsic point-height function.
These are instances of the existing `DimensionFunction`, not new structures.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `specPointOrderIso` | expose the existing identity-on-points comparison, with dual prime order | $(\operatorname{Spec}A,\leq_{\mathrm{cl}})\simeq(\operatorname{Spec}A,\subseteq)^{\mathrm{op}}$ |
| `DimensionFunction.ofSpecFiniteType`, `ofSpecFiniteType_apply` | actual affine constructor and literal prime-residue-field evaluation | $\delta_{A/k}(x)=\operatorname{trdeg}_k\kappa(x)$ |
| `DimensionFunction.ofSpecFiniteType_eq_pointHeight` | equality to actual finite closure height | $\delta_{A/k}(x)=h_{\operatorname{Spec}A}(x)=\dim\overline{\{x\}}$ |
| `DimensionFunction.ofSpecFiniteType_nonneg` | nonnegative point values | $0\leq\delta_{A/k}(x)$ |
| `supportDegree_ofSpecFiniteType_eq_iff` | exact actual-carrier dimension test for natural n | $\deg_{\delta_{A/k}}W=n\iff\dim W=n$ |
| `fundamentalCycle_mem_ofSpecFiniteType_iff` | existing homogeneous-cycle membership detects carrier dimension | $[W]\in Z^{\delta_{A/k}}_{\mathrm{fin},n}(\operatorname{Spec}A;R)\iff\dim W=n$ |
| `DimensionFunction.ofAffineLocallyOfFiniteType`, `ofAffineLocallyOfFiniteType_apply` | actual affine structural-morphism constructor and literal point height | $\delta_{X/k}(x)=h_X(x)$ |
| `DimensionFunction.ofAffineLocallyOfFiniteType_nonneg` | nonnegative structural-affine values | $0\leq\delta_{X/k}(x)$ |
| `supportDegree_ofAffineLocallyOfFiniteType_eq_iff` | geometric degree of actual integral closed carriers | $\deg_{\delta_{X/k}}W=n\iff\dim W=n$ |
| `fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff` | the same criterion in the existing cycle module on X | $[W]\in Z^{\delta_{X/k}}_{\mathrm{fin},n}(X;R)\iff\dim W=n$ |

Both strictness and the immediate-specialization unit law are proved.
Scheme closure order reverses prime inclusion, and SP47 is applied only
after that reversal. The affine structural constructor extracts the actual
finite-type algebra on global sections through `X.isoSpec`; it does not
ask for a preinstalled sections algebra. The existing closed-immersion
restriction along the isomorphism and actual carrier isomorphisms supply
the transport. Finite-dimensionality justifies the integer point-height
comparison. No ambient domain, reducedness, normality, nonemptiness or
dimension-at-most-one premise is needed. The fundamental-cycle iff uses
nontrivial coefficient semirings; its nontriviality premise is retained.

The spectrum constructor uses `Ideal.ResidueField`; the structural-affine
constructor uses literal point height. SP49 below explicitly constructs the
structural action on the separate `Scheme.residueField` and proves the
affine algebra comparison and open-immersion residue-degree invariance.
SP50 below proves the arbitrary structural affine value comparison and
affine-open value agreement. SP51 adds pointwise finiteness and affine-chart
value agreement in a general ambient scheme. SP52 below transfers the
common-chart order and cover laws and constructs the global function.
SP53 below identifies its values with global point height and actual
closure/carrier dimension.

### Structural and affine residue-field comparison (SP49)

Write \(\kappa_X(x)=\mathcal O_{X,x}/\mathfrak m_x\) for the actual
scheme residue field, and \(\kappa(\mathfrak p_x)\) for the existing
prime-localization residue field on a spectrum. The canonical comparison
is \(\psi_{A,x}\). The structural action is defined before this map,
by pulling back and evaluating actual global constants.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `residueFieldBaseMap`, `residueFieldBaseAlgebra`, `residueFieldBaseAlgebra_algebraMap` | actual structural ring map and its locally installed algebra | $k\to\Gamma(\operatorname{Spec}k,\mathcal O)\xrightarrow{p^\sharp}\Gamma(X,\mathcal O_X)\xrightarrow{\operatorname{ev}_x}\kappa_X(x)$ |
| `residueFieldBaseMap_comp` | actual evaluation naturality retains the structural action | $u_x^*\circ\operatorname{ev}_{u(x)}\circ p^\sharp=\operatorname{ev}_x\circ(p\circ u)^\sharp$ on global base constants |
| `residueFieldBaseAlgHom`, `residueFieldBaseAlgHom_apply` | existing geometric residue map bundled as a base-algebra map | $u_x^*:\kappa_Y(u(x))\to_k\kappa_X(x)$ |
| `residueFieldBaseAlgEquivOfIsOpenImmersion`, `_apply` | same map is a base-algebra equivalence for an actual open immersion | $u_x^*:\kappa_Y(u(x))\simeq_k\kappa_X(x)$ |
| `specResidueFieldEquiv` | actual stalk/localization-induced residue-field equivalence | $\psi_{A,x}:\kappa_{\operatorname{Spec}A}(x)\simeq\kappa(\mathfrak p_x)$ |
| `specResidueFieldEquiv_evaluation` | compatibility with every actual A-constant | $\psi_{A,x}(\operatorname{ev}_x(a))=\overline a\in\kappa(\mathfrak p_x)$ |
| `specResidueFieldAlgEquiv`, `specResidueFieldAlgEquiv_apply` | same canonical map with structural base compatibility proved | $\psi_{A,x}:\kappa_{\operatorname{Spec}A}(x)\simeq_k\kappa(\mathfrak p_x)$ |
| `spec_schemeResidueField_trdeg_eq` | full-cardinal comparison over a field | $\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)=\operatorname{trdeg}_k\kappa(\mathfrak p_x)$ |
| `spec_schemeResidueField_trdeg_lt_aleph0` | finite type of A proves finite residue transcendence degree | $\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)<\aleph_0$ |
| `DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg` | existing affine function evaluated in the actual scheme residue field | $\delta_{A/k}(x)=\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)$ |
| `residueFieldBase_trdeg_eq_of_isOpenImmersion` | full-cardinal invariance for actual open immersions | $\operatorname{trdeg}_k\kappa_Y(u(x))=\operatorname{trdeg}_k\kappa_X(x)$ |

The base action is an ordinary definition, installed with `letI` in each
signature that uses it. No global instance is added and the action is not
defined by transport through \(\psi_{A,x}\). The underlying ring maps,
stalks, localizations and residue fields are the existing actual objects.
Naturality of global sections, evaluation and the existing scalar tower
prove multiplicativity and base compatibility. All algebra comparisons
allow arbitrary commutative base and ambient rings; a field is required
only for the transcendence-degree statements. Full-cardinal invariance
does not require finite type. Finite type of the ambient algebra proves
finite residue degree before numeric conversion; it does not assert that
the residue field is a finite-type algebra. The existing dimension function
is unchanged, and no new cycle module, Chow quotient or projector is added.

SP50 below identifies `ofAffineLocallyOfFiniteType` on an arbitrary affine
structural \(X\) with its actual structural residue degree and proves
affine-open value agreement. SP51 adds pointwise finiteness and affine-chart
value agreement in a general ambient scheme. SP52 below constructs the
global function using the common-chart order and cover laws. SP53 below
identifies global point height and closure/carrier dimension. Target
codimension conversion and further realization remain separate.

### Structural residue-degree values on actual affine schemes (SP50)

The notation \(\delta_{X/k}\), \(h_X(x)\) and \(\kappa_X(x)\)
continues to denote the existing affine dimension function, actual scheme
point height and actual scheme-stalk residue field. No new object or
independent symbol is introduced.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `point_height_iso` in `AffineSchemeDimensionFunction.lean` | expose the existing actual-isomorphism height theorem, proof unchanged | $h_Y(e(x))=h_X(x)$ for $e:X\simeq Y$; theorem only |
| `affine_schemeResidueField_trdeg_lt_aleph0` | actual structural residue degree is finite for affine locally finite-type X | $\operatorname{trdeg}_k\kappa_X(x)<\aleph_0$ |
| `DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg` | identify the existing height-defined affine function with actual structural residue degree | $\delta_{X/k}(x)=h_X(x)=\operatorname{trdeg}_k\kappa_X(x)$ |
| `DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion` | compare existing dimension values under an affine open immersion over k | $\delta_{X/k}(x)=\delta_{Y/k}(f(x))$ for open $f:X\to Y$, with source structural map $p\circ f$ |

The new leaf `Cycles/AffineSchemeResidueDegree.lean` takes the actual
structural morphism \(p:X\to\operatorname{Spec}k\) and locally installs
its independently defined residue-field algebra. Its proof extracts the
finite-type sections algebra from `X.isoSpec.inv ≫ p` and retains the
equality of its spectrum map with that morphism. The actual isomorphism
identities prove that composition with `X.isoSpec.hom` is \(p\), so the
SP49 residue-degree equality uses precisely the original structural action.
Finite transcendence degree is proved before conversion to a natural
number or integer; finite type of the residue field is not asserted.
No preinstalled sections algebra, affine presentation, integrality,
reducedness or nonemptiness is an input. The existing point-height theorem
is reused, not duplicated. The open comparison assumes both schemes
affine and the target structural morphism locally of finite type; the
source instance follows by composition with the actual open immersion.

SP51 below proves pointwise structural residue-degree finiteness and
affine-chart value agreement in a general locally finite-type ambient
scheme. SP52 transfers the common-chart order and cover laws to construct
the global dimension function. SP53 below identifies its values with
global point height and actual closure/carrier dimension. Target
codimension conversion and further realization remain open.

### Pointwise residue degrees and affine-chart values (SP51)

Keep \(\kappa_X(x)\) for the actual scheme residue field with its
structural action. The notation \(\delta_{U/k}\) denotes the existing
dimension function only on the affine chart \(U\); no global
dimension-function symbol is introduced for the general ambient \(X\).

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `schemeResidueField_trdeg_lt_aleph0` | every actual structural residue degree is finite under locally finite type | $\operatorname{trdeg}_k\kappa_X(x)<\aleph_0$ |
| `affineChart_dimension_eq_schemeResidueField_trdeg` | existing affine-chart value equals the ambient structural residue degree | $\delta_{U/k}(u)=\operatorname{trdeg}_k\kappa_X(i(u))$ for open $i:U\to X$ |
| `affineChart_dimension_eq_of_eq_image` | values on two actual affine charts agree at the same ambient point | $i(u)=j(v)\Rightarrow\delta_{U/k}(u)=\delta_{V/k}(v)$ |

All three theorems are in `Cycles/ChartResidueDegree.lean`. The ambient
structural morphism \(p:X\to\operatorname{Spec}k\) is locally of finite
type; \(X\) need not be affine, quasi-compact, integral, reduced or
nonempty. Pointwise finiteness uses `X.affineCover.exists_eq` and one
actual chart, then SP50's finite degree and SP49's base-compatible residue
map. There is no finite subcover, global dimension bound or claim that
residue fields are finite-type algebras. Each chart carries the actual
composite structural map \(p\circ i\). The second theorem rewrites
its existing affine dimension value through the actual residue map. For
the third theorem a local proof expression packages the dependent ambient
point, residue field and scalar action together, so equality of actual
images compares the values without a replacement carrier or a supplied
gluing hypothesis. No affine intersection is assumed or constructed.

SP52 below supplies common-chart specialization and cover-law transfer
and constructs the global dimension function from these value theorems.
No global constructor, unrestricted open-height invariance, target
codimension conversion or additional realization is asserted by SP51
itself.

### Global structural residue-degree dimension function (SP52)

Extend the existing notation \(\delta_{X/k}\) to every scheme locally
of finite type over the structural field. This is the same affine
dimension-function object when \(X\) is affine; no independent grading
symbol is introduced. Continue to use \(\kappa_X(x)\) with the locally
installed structural action.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `exists_isAffineOpen_mem_of_le` | a common actual affine open for a specialization pair, on any scheme | $x\leq y\Rightarrow\exists U\text{ affine open},\ x,y\in U$ |
| `DimensionFunction.ofLocallyOfFiniteType` | the global structural residue-degree dimension function, with both laws proved | $\delta_{X/k}:X\to\mathbb Z$, $x<y\Rightarrow\delta(x)<\delta(y)$, $x\lessdot y\Rightarrow\delta(y)=\delta(x)+1$ |
| `DimensionFunction.ofLocallyOfFiniteType_apply` | evaluation using the actual structural residue field | $\delta_{X/k}(x)=\operatorname{trdeg}_k\kappa_X(x)$ |
| `DimensionFunction.ofLocallyOfFiniteType_nonneg` | the field normalization is nonnegative | $0\leq\delta_{X/k}(x)$ |
| `DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType` | equality of the whole global and existing affine dimension-function objects | $\delta_{X/k}^{\mathrm{global}}=\delta_{X/k}^{\mathrm{affine}}$ for affine $X$; superscripts only for this comparison |
| `DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion` | arbitrary actual open immersions preserve the global values over the field | $\delta_{X/k}(x)=\delta_{Y/k}(f(x))$, with source structural map $p\circ f$ |

All six endpoints are in `Cycles/FieldDimensionFunction.lean`. The
common-chart helper is valid for any scheme. The constructor takes an
actual locally finite-type structural morphism to \(\operatorname{Spec}k\)
and uses SP51's finite residue degrees. An affine neighbourhood of the
specialized point contains its generizations. The actual open embedding
reflects specialization, transferring strict order and the ambient cover
relation into the chart with its actual scheme specialization order.
The affine strictness and unit-step laws then transfer through the
structural residue-degree comparison. Neither affineness of the ambient
scheme, quasi-compactness, integrality nor a global dimension bound is
needed. No supplied dimension-function or gluing hypothesis, new point
order, global algebra instance, residue carrier, cycle module, Chow
quotient or projector is introduced.

SP53 below identifies these global values with actual point height and
the existing closure/carrier dimension, using both the strictness and
the affine normalization. The two defining laws alone allow additive
shifts, so the comparison is not inferred from those laws alone. Target
codimension conversion and further realization remain separate.

### Global point height and actual carrier dimension (SP53)

Keep the same \(\delta_{X/k}\), actual point height \(h_X(x)\),
scheme residue field \(\kappa_X(x)\) and existing integral closed
carrier \(W\). These are comparisons of existing objects, not new
gradings or replacement carrier types.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `point_height_eq_ofLocallyOfFiniteType` | literal extended point height equals the finite structural value | $h_X(x)=\delta_{X/k}(x)$ in $\mathbb N\cup\{\infty\}$ |
| `point_height_ne_top_of_locallyOfFiniteType` | pointwise finite height without a global dimension bound | $h_X(x)<\infty$ |
| `DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight` | the existing global function equals integer point height | $\delta_{X/k}(x)=h_X(x)\in\mathbb Z$ |
| `pointSupport_dimension_eq_ofLocallyOfFiniteType` | dimension of the actual reduced point-closure carrier | $\dim\overline{\{x\}}=\delta_{X/k}(x)$ |
| `supportDegree_ofLocallyOfFiniteType_eq_iff` | the existing support degree detects actual carrier dimension | $\deg_{\delta_{X/k}}W=n\iff\dim W=n$, $n\in\mathbb N$ |
| `fundamentalCycle_mem_ofLocallyOfFiniteType_iff` | existing homogeneous fundamental cycles detect actual dimension | $[W]\in Z^{\delta_{X/k}}_{\mathrm{fin},n}(X;R)\iff\dim W=n$, for nontrivial $R$ |
| `point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType` | open immersions over the field preserve actual point height in the stated setting | $h_U(u)=h_X(i(u))$, for locally finite-type $X/k$ and open $i:U\to X$ |

All seven endpoints are in `Cycles/FieldSupportDimension.lean`.
Nonnegative strictness of the constructed function gives the upper height
bound by a strictly increasing natural-valued map. One actual affine
neighbourhood provides the lower bound: the existing affine function is
literal finite chart height, SP52 compares its value with the ambient
function, and the actual open embedding has a strict point map. The
proof fixes the open scheme's specialization order explicitly; it does
not identify that order with a subtype instance by fiat. The full extended
height equality is proved before any finite-height conversion. Reusing
the existing actual point-closure and generic-point carrier comparisons
then gives the geometric grading criteria. Ambient affineness,
quasi-compactness, Noetherianity, integrality, nonemptiness and a global
dimension bound are not premises. Nontriviality of coefficients is
retained for the fundamental-cycle converse. No new scalar action,
dimension function, carrier, cycle module, Chow quotient or projector
is introduced.

The next bounded goal is the integral codimension/degree formula. For
actual integral \(X\), put \(d=\delta_{X/k}(\eta_X)\) and prove
finite actual chain codimension and
\(\operatorname{codim}_X W+\deg_{\delta_{X/k}}W=d\).
The generic-point height comparison gives finite integral ambient
dimension, enabling induction on coheight using the existing unit-step
law. Then reindex codimension \(p\) as degree \(d-p\). A later
reducible extension must use actual pure-dimensional geometry or
componentwise grading; smoothness alone does not supply one uniform
dimension. The current quotient's Noetherian premise, general rational
coefficient extension and target realization remain separate obligations.

## Objects deliberately assigned no independent notation

The following should be named in prose or by the notation of their target:

- theorem wrappers converting nonemptiness to a tautological lift whose target
  is defined as its own action;
- `Diagram.toIntermediate` and `Diagram.toBase` wrappers around the canonical
  maps of `NormalizedCover`;
- the local one-boundary structures when viewed as `PUnit` specializations;
- compatibility aliases for fixed-ring and prime-inertia premises;
- conversion theorems between
  `IsEmpty (RamifiedCodimensionOnePoint ...)` and
  `NoCodimensionOneRamification`;
- verification-only names and import shims.

## Semantic non-identifications

These notational distinctions are mandatory:

```text
q_A in k^(G/H)             != e_H in Q[G]
e_H in Q[G]                != Pi in the compactified Chow algebra
boundary in Y_L            != pulled-back boundary in Y_N
valuation inertia I_E      != prime inertia I_Q^pr definitionally
raw closure Cl_r(e_eta)    != idempotent extension Ext_r(e_eta)
codimension-one purity     != selector gluing purity
```

Any future theorem joining one row to another must expose the comparison map
or hypothesis in its statement.

## Release gates

- [ ] Every active proof-spine object has exactly one row in the registry.
- [ ] Every symbol in the canonical manuscript has one semantic type throughout.
- [ ] Removed aliases have no active callers outside compatibility sources.
- [ ] Conditional research modules are absent from root umbrella imports and
      release verification.
- [x] `lake build` and `lake env lean research/Verification.lean` succeed.
- [x] The canonical manuscript `paper/main.tex` builds to `paper/main.pdf`
      without undefined references or citations. Archived provenance PDFs are
      not release build targets.
- [ ] The source and claim ledgers describe only the active proof path.
- [x] The working-tree changes introduce no project axiom, `sorry`, or
      `admit` under `HodgeConjecture/`.
