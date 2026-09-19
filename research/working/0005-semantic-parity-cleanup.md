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

Editorial record (SP54): at the user's request, manuscript status labels,
disclaimer prose and deferred-work commentary have been removed. Theorem
hypotheses remain explicit. Proof-status, gap and release records remain in
the research documents, including this queue. The single manuscript now has
six main sections and three technical appendices: graph/cycle/dimension
foundations, detailed split computations, and the centralized Lean/source
crosswalk. The main text packages graph calculus, cycle/Chow infrastructure
and split geometric realization, retaining the multiplicative-rigidity
corollary. Detailed mathematical statements and proofs are preserved in the
same PDF. No proof-status change follows from this editorial reorganization.

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

### Construction and input checkpoints (SP17--SP63)

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
| SP54 | Actual integral chain codimension and the existing d-minus-n grading | IDENTIFY / REINDEX | Prove finite ambient dimension and coheight, then derive codimension plus degree from the existing cover law. Identify support, fundamental-cycle and full-cycle degree d-minus-n criteria with actual codimension n. Reuse the existing grading; principal-relation data reindexing is recorded in SP55. | PROVED; FULL BUILD, 509 AXIOM REPORTS, SIXTEEN REGRESSIONS, DEPENDENCY AUDIT, AND SINGLE-PDF CHECKS PASS |
| SP55 | Actual codimension indexing of principal relations and generic-degree vanishing | REINDEX / CONNECT | Reindex degree d-minus-(n+1) relation data by the same codimension-n carriers and their unchanged function-field units. Preserve the actual ambient principal-divisor generator. Prove generic-degree index emptiness for any integral scheme with a supplied dimension function, and derive zero relation span and rational equivalence as equality under the existing Noetherian premise. | PROVED; FULL BUILD, 518 AXIOM REPORTS, SIXTEEN REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP56 | Rational homogeneous cycles and the scalar-extended principal-relation quotient | EXTEND COEFFICIENTS / COMPARE | Extend coefficients on the same homogeneous cycle module and identify its tensor scalar extension. Form the rational span of the same actual principal divisors and compare the resulting rational quotient with the tensor extension of the integral Chow group, preserving class representatives. Retain quotient-layer Noetherianity and distinguish coefficient injectivity from Chow rationalization. | PROVED; FULL BUILD, 538 AXIOM REPORTS, TWENTY REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP57 | Rational closed pushforward and actual isomorphism restriction on the existing Chow quotient | EXTEND / DESCEND / COMPARE | Factor one coefficient-parametric graded closed pushforward, retain the integer specializations, prove coefficient compatibility and preservation of the same principal-relation span, and descend to rational Chow with identity/composition and tensor naturality. Identify the rational isomorphism's forward and inverse representative formulas with actual closed pushforward and open restriction. | PROVED; FULL BUILD, 560 AXIOM REPORTS, TWENTY REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP58 | Actual function fields, divisor-point embedding and signed orders under open immersions | GENERALIZE / PRESERVE | Generalize the existing generic-stalk/function-field construction to integral open immersions and retain the old isomorphism specializations. Use actual stalk isomorphisms to embed divisor points with exact open-image range, then preserve the signed local coefficient using target local Noetherianity. | PROVED; FULL BUILD, 572 AXIOM REPORTS, TWENTY REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP59 | Actual open support restriction, reduced closure and principal-divisor cycles | IDENTIFY / ASSEMBLE | Prove inverse support identities for nonempty actual ideal-comap restriction and ambient reduced closure, preserve chain codimension, and evaluate the existing finite-cycle restriction at the closure coefficient. Combine this with the actual local-order transport to restrict principal-divisor cycles, deriving source local Noetherianity and compactness from the target. | PROVED; FULL BUILD, 584 AXIOM REPORTS, TWENTY REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP60 | Supplied dimension-function restriction, homogeneous cycles and the actual carrier square | RESTRICT / COMPARE | Restrict the dimension function by the actual open point map, proving both laws, and preserve the existing homogeneous cycle modules over any semiring. Prove the Cartesian open-restriction/closed-pushforward square for an actual integral carrier, including empty inverse images, without introducing principal-relation or Chow descent hypotheses. | PROVED; FULL BUILD, 599 AXIOM REPORTS, TWENTY REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP61 | Actual ambient principal-generator restriction and preservation of its relation span | TRANSPORT / PRESERVE | Apply the actual carrier square to the existing ambient principal divisor, using the actual function-field map on a nonempty restriction and zero for an empty carrier. Restrict degree-one-higher relation data without finiteness premises; under target-only Noetherianity identify the graded generators, preserve their span and preserve rational equivalence of integral cycles. | PROVED; FULL BUILD, 609 AXIOM REPORTS, SIXTEEN REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP62 | Integral and rational Chow open restriction with coefficient and tensor compatibility | DESCEND / COMPARE | Descend the existing actual graded open restriction to both existing Chow quotients, preserving cycle representatives, identity and contravariant composition. Prove raw and graded coefficient compatibility without finiteness premises, and the full tensor square with only target Noetherianity at the quotient layer. | PROVED; FULL BUILD, 622 AXIOM REPORTS, EIGHTEEN REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP63 | Surjectivity of the existing raw, graded and Chow open restrictions | LIFT / DESCEND | Lift each actual integral open support through its reduced ambient closure and preserve the supplied degree, over every semiring. Lift integral and rational Chow classes through actual homogeneous representatives under target-only Noetherianity. Keep the closure lift at cycle level; no Chow closure operation or localization exactness is asserted. | PROVED; FULL BUILD, INTEGRATED VERIFICATION (626 AXIOM REPORTS, 734 CHECKS, 565 EXAMPLES), SIXTEEN FOCUSED REGRESSIONS, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP64 | Normal-Noetherian bounded overrings and their existing-colon transporter | ADAPT / PROVE | Embed a uniformly bounded overring in the base module, derive finiteness and integrality, and use normality. Compose two nonzero bounds through `Submodule.colon`; a proper overring has zero transporter into a bounded stage. | PROVED; FULL BUILD, SIX FOCUSED REGRESSIONS, STANDARD-AXIOM ALLOWLIST, INTEGRATED VERIFICATION, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP65 | Actual affine sections and the fixed--moving boundary-section algebra in the specified field | CONSTRUCT / IDENTIFY | Use the existing generic germ and fraction-field equivalence for an injective algebra map, its range equivalence, constants, restriction, antitonicity and full-open image. Specialize to the same normalization and boundary ideal; prove nonemptiness from a nontrivial subgroup's faithful action. | PROVED; FULL BUILD, SIXTEEN FOCUSED REGRESSIONS, STANDARD-AXIOM ALLOWLIST, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP66 | Genuine normalization trace dual, common denominator and actual-section colon consumers | REUSE / BOUND / APPLY | Reuse Mathlib's trace-dual submodule, contain it in an integral generic basis's finite trace-dual span, and clear that span by one nonzero normalization element. Specialize to the existing normal closure; apply B0 conditionally to B1's actual sections without duplicating carriers or assuming geometric landing. | PROVED; FULL BUILD, FOURTEEN FOCUSED REGRESSIONS, STANDARD-AXIOM ALLOWLIST, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP67 | Actual height-one boundary poles and the uniform-landing separation implication | GLUE / CONSTRUCT / COMPARE | Glue local fractions into actual sections; clear the height-one localized ideal containment to construct a fraction outside the base. Specialize to the same fixed--moving boundary, derive the trace-pole witness and zero colon, and prove separation from explicitly supplied nonzero uniform landing for every subgroup. | PROVED; FULL BUILD, TWELVE FOCUSED REGRESSIONS, STANDARD-AXIOM ALLOWLIST, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP68 | Prescribed first element and the fixed--moving regular-pair separation criterion | REFINE / CANCEL / APPLY | Preserve the existing height-one denominator theorem as a wrapper around a fixed-element refinement. Cancel a regular moving element on the existing quotient by a nonzero fixed element; use the same two boundary-ideal summands to exclude containing height-one primes. | PROVED; FULL BUILD, TEN FOCUSED REGRESSIONS, STANDARD-AXIOM ALLOWLIST, BOUNDARY-POLE RERUN, DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP69 | Actual geometric-input audit and research-only regular-pair controls | AUDIT / TEST SCOPE | Distinguish supplied normalized-cover data from constructed geometry. Record the etale-visible quadratic boundary obstruction and the unimplemented full-visible option; test good and bad first-element choices on separate algebraic ideals. | RESEARCH ONLY; EIGHT ALGEBRA DIAGNOSTICS, EIGHT STANDARD-AXIOM AUDITS AND FULL BUILD PASS; ACTIVE LIBRARY AND MANUSCRIPT UNCHANGED |
| SP70 | Finite normal affine models and full-visible boundary separation | IDENTIFY / CONSTRUCT / SEPARATE | Identify supplied finite normal affine algebras with the existing normalization rings, transport finite models and etaleness, and construct the existing normalized cover. Empty conjugate boundaries and the core-free sheet action give unit moving/combined ideals and direct separation. | PROVED; FULL BUILD, TWENTY FOCUSED REGRESSIONS, SEVENTEEN STANDARD-AXIOM AUDITS, FRESH DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP71 | Actual whole inverse-image affine rings and normalization over the original base | DERIVE / IDENTIFY / COMMUTE | Derive finite and etale section algebras from a finite etale scheme morphism. For an integral source and nonempty chart, use the actual function field and explicit normal stalks to identify the whole inverse-image open with its normalization, prove the structural equality over the original base, and derive finite/etale normalization. | PROVED; FULL BUILD, EIGHTEEN FOCUSED REGRESSIONS, ELEVEN STANDARD-AXIOM AUDITS, SP70 RERUN, FRESH DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP72 | Actual dominant function-field map and finite generic extension | CONSTRUCT / COMMUTE / LOCALIZE | Construct the generic-stalk map with germ, identity and composition laws; identify its open-immersion specialization. Derive section scalar towers and finite-dimensionality from the actual finite affine algebra, with a global endpoint choosing its chart internally. | PROVED; FULL BUILD, EIGHTEEN FOCUSED REGRESSIONS, ELEVEN STANDARD-AXIOM AUDITS, SP71 RERUN, FRESH DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP73 | Formal unramifiedness and separability of the actual generic extension | LOCALIZE / COMPOSE / APPLY | Transfer formal unramifiedness from an actual dominant affine scheme morphism to its existing function-field algebra. For finite morphisms, use SP72 finite-dimensionality to prove separability; finite etale morphisms are a specialization. | PROVED; FULL BUILD, SIXTEEN FOCUSED REGRESSIONS, THREE STANDARD-AXIOM AUDITS, SP72 RERUN, FRESH DEPENDENCY AUDIT AND SINGLE-PDF CHECKS PASS |
| SP74 | Constructed marked normal closure and extension-specific Galois bridge | CONSTRUCT / PRESERVE / TRANSFER | Build the existing normal-closure datum inside the upstairs algebraic closure, preserving its canonical marking. Transfer separability to any marked normal closure and apply the Galois consequence to the actual finite generic extension. | PROVED; FULL BUILD, TWENTY-TWO FOCUSED REGRESSIONS, SEVEN STANDARD-AXIOM AUDITS, SP73 RERUN, FRESH DEPENDENCY AUDIT, SINGLE-PDF CHECKS AND INDEPENDENT REVIEW PASS |
| SP75 | Local-separability consumer generalization and core-free hypothesis cleanup | GENERALIZE / MOVE / REUSE | Replace fourteen perfect-field premises by extension separability; remove twelve without replacement. Move the two existing separability/Galois helpers to the core, retaining one perfect-field compatibility wrapper and all other geometric inputs. | PROVED / VALIDATED |
| SP76 | Finite normal-closure normalization and actual affine-preimage cover | DERIVE / CONSTRUCT / SEPARATE | Derive finiteness over a normal Noetherian base, eliminate the separately supplied second affine algebra, and construct the existing cover from the actual affine inverse image and marked generic extension. | PROVED / VALIDATED |
| SP77 | Finite tensor source, marked field quotient and integral evaluation | CONSTRUCT / EVALUATE / COMPARE | Prove finite-index tensor finiteness/etaleness, evaluate onto the existing marked normal closure, identify the actual generic kernel quotient, and restrict the same embeddings to integral closures with exact factor/pure-tensor compatibility. Keep integral factor identification and whole-chart etaleness separate. | PROVED / VALIDATED |
| SP78 | Canonical tensor base change and full evaluator homomorphism square | LOCALIZE / COMPARE / COMMUTE | Identify each localized integral closure with its algebraic ambient field, construct finite-index tensor base change, and prove the actual evaluator homomorphisms commute. Relocate the three existing evaluator helpers without duplication. | PROVED / VALIDATED |
| SP79 | Selected generic evaluation factor and canonical idempotent | SPLIT / SELECT / CHARACTERIZE | Derive finite etale source structure under extension separability, split the actual evaluation kernel factor, identify its first projection with the existing evaluator, and characterize its selecting idempotent and complementary kernel ideal. | PROVED / VALIDATED |
| SP80 | Integral trace section, actual normalization factor and whole-ring etaleness | CONTRACT / SELECT / IDENTIFY / LOCALIZE | Derive generic spanning from the existing evaluator square, construct the integral selector by trace, identify its complementary quotient with the actual normalization, derive finite etale structure, and compare with the existing generic selector. Whole-source normality is bypassed. | PROVED / VALIDATED |
| SP81 | Actual finite etale affine normalized cover and marked refinement | TRANSPORT / CONSTRUCT / FACTOR | Preserve the actual intermediate scheme's local presentations through the tensor source and selected open component; construct the existing cover with finite-etale structural/refinement maps and exact factorization on the actual chart and over the original base. | PROVED / VALIDATED |
| SP82 | Same-ambient normalization localization and actual affine restriction | LOCALIZE / RESTRICT / COMMUTE | Retain the ambient ring, normalization carriers and original marking; prove generic localization/naturality/composition, principal-open restriction, and both actual structural/refinement squares on nested affine charts. | PROVED / VALIDATED |

SP82 (2026-09-19): **same-ambient localization / actual affine restriction**.
The checkpoint is proved and validated. The 28 production APIs compile
cleanly in the 2764-job scoped build.
Seventeen are in `NormalizationLocalization.lean`, nine in
`AffineNormalizationRestriction.lean` and two in
`FiniteEtaleNormalClosureRestriction.lean`. The canonical inclusion
`rho^E_{B,C}:IntCl_B(E) -> IntCl_C(E)` keeps each ambient element
unchanged. Its injectivity, identity, composition and naturality with
the existing normalization map are proved. Under `C=M⁻¹B`, its target
carries the corresponding localization structure, and the canonical
tensor base-change equivalence preserves the actual scalar/inclusion
formula on pure tensors. The compatible ambient `C`-action makes the
denominators units. No normality, Noetherianity, finite-degree premise,
replacement field, normalization carrier or input axiom is introduced.

The contravariant scheme map has structural and naturality squares
and generic identity/composition laws. Principal localization gives
an open immersion whose range is the inverse image of the original
basic open. Arbitrary multiplicative-set localization is not asserted
to be open. The actual adapter derives its scalar towers from section
restriction and generic germs, constructs the restriction morphism
and its structural squares, proves principal-open localization/open
immersion, and proves naturality of the existing whole-preimage
normalization isomorphism.

For any nonempty affine `W <= U`, the normal-closure specialization
proves both `pi_U after j = iota after pi_W` and
`lambda_U after j = tilde-iota after lambda_W`, on the original marked
normal closure. The chart square needs dominant `p`; the refinement
square adds finite `p` and explicit normal stalks on both inverse images.
Neither square needs etaleness, base normality or Noetherianity.
The smaller base chart is `W`; retain SP81's `V=p⁻¹U` for the upstairs
open. The generic identity/composition laws are proved, but actual
overlap/coherence data and global gluing are not assembled by them.

Notation parity:

| Lean object / group | Mathematical role | TeX notation |
| --- | --- | --- |
| `normalizationBaseChangeMap`, `_coe`, `_injective`, `_self`, `_trans`, `_naturality` | existing integral-closure inclusion and strict same-ambient laws | \(\rho^E_{B,C}:T_B(E)\to T_C(E)\); \(T_B(E)=\operatorname{IntCl}_B(E)\) is local shorthand, not a second object |
| `normalizedCoordinateRing_isLocalization`, `normalizationLocalizationBaseChangeEquiv`, `_tmul` | actual localization and tensor comparison preserving ambient scalars | \(C\otimes_B T_B(E)\simeq T_C(E)\) |
| `normalizationBaseChange`, `_comp_toBase`, `_naturality`, `_self`, `_trans` | contravariant map and structural/naturality/composition laws | \(j^E_{B,C}=\operatorname{Spec}(\rho^E_{B,C})\); laws are prose only |
| `normalizedCoordinateRing_isLocalizationAway`, `normalizationBaseChange_isOpenImmersion`, `_range` | principal localization and exact original-basic-open inverse-image range | existing \(j^E_{B,B_f}\), \(\mu_E^{-1}(D(f))\) |
| `sectionRestriction_functionFieldScalarTower`, `sectionRestriction_ambientScalarTower`, `finiteAffinePreimageRestriction_functionFieldScalarTower` | derived compatibility of actual restrictions, germs and ambient actions | existing section maps and ambient fields; prose only |
| `affineNormalizationRestriction`, `_comp_toBase`, `_comp_toChart`, `_basicOpen_isLocalization`, `_basicOpen_isOpenImmersion` | actual normalization restriction and principal-open specialization | \(j^N_{W,U}:Z_W\to Z_U\), using the same \(N\) |
| `finiteAffinePreimageNormalizationIso_restriction` | naturality of the existing whole-preimage normalization isomorphism | existing \(\nu_{p,U},\nu_{p,W}\); inclusions \(\iota,\widetilde\iota\) |
| `finiteEtaleAffineNormalClosureToChart_restriction`, `finiteEtaleAffineNormalClosureToPreimage_restriction` | actual structural and marked-refinement restriction squares | \(\pi_U\circ j^N_{W,U}=\iota\circ\pi_W\), \(\lambda_U\circ j^N_{W,U}=\widetilde\iota\circ\lambda_W\) |

Primary sources 0307, 01I3 and 00E2 were checked in the exact scopes
recorded in the source ledger. The paper reuses its 0307 entry and adds
only `StacksPrincipalLocalizationOpen` (01I3); no source axiom is used.
The focused suite passes 39 examples and 28 enforced standard-three
axiom audits without warnings or errors. Three fresh neighbor suites
also pass cleanly: SP81 `FiniteEtaleNormalClosureVerification` 25/19,
SP71 `FiniteAffineChartVerification` 18/11, and SP78
`NormalizationBaseChangeVerification` 25/13. The four suites total
107 examples and 71 audits. The full build passes 3203 jobs with only
the two unchanged `Challenge.lean` placeholder warnings at lines 33 and
46. The fresh unchanged `ProofDependencies` audit passes six primary
endpoint contracts and two support reports without warnings or errors.

The single PDF passes its final build at 81 pages and 835379 bytes.
The final log has no warnings, undefined references or citations, or
overfull/underfull boxes. Visual checks of pages 13, 14, 61, 62, 73, 74
and 81 pass, including the final crosswalk path formatting. Independent
mathematical/code/Lean--TeX review passes with no defects.
All 28 code/central/test/TeX parity checks pass, with exactly one central
check and axiom report per new declaration. The static central inventory
is 987 checks, 565 examples and 879 reports; its historical prefix is
byte-identical to `db8a206` and was not re-elaborated in full.
The audit 0018 prefix and the SP81-to-end queue suffix are also
byte-identical to `db8a206`; `ProofDependencies` is unchanged.
The three production modules have no axioms, proof placeholders or
native-decision escapes. Earlier validation records retain their
original scope.

Next assemble actual overlap comparisons and coherence/cocycle data,
then glue the refinement and its compatible global Galois action.
Normal stalks from smooth geometry and Chow--Betti generation remain
separate. The SP81 block and all subsequent queue history below are
preserved byte-for-byte.

SP81 (2026-09-19): **actual finite etale affine cover / marked refinement**.
The checkpoint is proved and validated. For a finite dominant etale
map `p:Y -> X` of integral schemes and a nonempty affine `U`, put
`V=p⁻¹U`, `B_U=Γ(X,U)` and `A_U=Γ(Y,V)`. Explicit normal-stalk
hypotheses on both opens give the normal section rings. The original
function fields, scalar maps and marked normal closure supply the
existing `NormalizedCover`, with actual visible scheme `V` and the
existing normalization-isomorphism map. No Noetherianity is assumed.
The datum identity is literal and full visibility gives boundary
separation.

The structural maps from the normal-closure normalization to `Spec B_U`
and the actual `U` are finite etale. Its refinement to `V` is the
original marked normalization leg followed by the inverse of the
existing visible normalization isomorphism. Composing with the
isomorphism recovers that leg. Composing with `p|_U` gives exactly
the actual chart structural map, with the original composite over `X`
also proved. The refinement itself is finite etale.
Both actual maps are surjective by lying over for the actual injective
integral normalization maps. Chart surjectivity only needs dominant `p`,
integral schemes and the nonempty affine chart; finiteness, etaleness
and both normal-stalk hypotheses are omitted. Refinement surjectivity
uses finite dominant `p` and normal stalks on `V`, with no etale or
base-normality premise. The finite-etale conclusions retain `hX` and `hY`.

The pinned library does not supply a general `Algebra.Etale`-to-`IsEtale`
converse. The generic `piTensorProduct_ringHomProperty` instead preserves
isomorphism-, identity-, composition- and base-change-stable properties
through finite tensor products. `piTensorProduct_isEtale` applies it to
the local standard-smooth presentations of the actual intermediate
scheme. SP80's actual complementary-idempotent quotient gives an open
immersion `Spec(ev_B)` into that tensor source, so the normalization
structural map is scheme-etale by composition. No new converse, carrier,
field marking, cover package or source axiom is introduced.

Notation parity:

| Lean object / group | Mathematical role | TeX notation |
| --- | --- | --- |
| `piTensorProduct_ringHomProperty`, `piTensorProduct_isEtale` | generic finite-tensor stability and actual scheme-etale source | existing \(P_B\); prose only |
| `NormalClosureData.normalizationTensorEvaluation_isOpenImmersion`, `.normalizationToBase_isEtale_of_etaleModel` | selected open component and its scheme-etale structural composite | existing \(\operatorname{Spec}(\operatorname{ev}_B)\) and normalization structural map |
| `functionFieldNormalClosure_normalization_finite_etale` | finite-etale normal-closure ring of the actual chart | existing \(B_U,A_U,\widetilde B_N\) |
| `finiteEtaleAffinePreimageNormalizedCover`, `_normalClosure`; `conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover` | existing cover, original marked datum and full-visible separation | existing \(C_U,\mathcal N,\operatorname{Sep}_{\partial}(C_U)\) |
| `finiteEtaleAffineNormalClosureToBase_finite_etale` | finite-etale structural map to the actual section-ring spectrum | existing \(Y_N\to\operatorname{Spec}(B_U)\), with \(Z_U=Y_N\) on this chart |
| `finiteEtaleAffineNormalClosureToChart`, `_comp_inclusion`, `_finite_etale`, `_surjective` | structural morphism to the actual affine open, its original-base equality and surjectivity | \(\pi_U:Z_U\to U\) |
| `finiteEtaleAffineNormalClosureToPreimage`, `_comp_normalizationIso`, `_comp_toBase`, `_comp_restrict`, `_finite_etale`, `_surjective` | actual finite-etale surjective refinement, original marked leg and exact factorization | \(\lambda_U:Z_U\to V\), \(\nu_{p,U}\circ\lambda_U=\operatorname{Norm}(\mathcal N.\mathit{embedding})\), \(p|_V\circ\lambda_U=\pi_U\) |

Retain `V=p⁻¹U`, `B_U`, `A_U`, `K(X)`, `K(Y)`, the marked normal
closure, `Y_L`, `Y_N`, `ν_{p,U}`, `C_U` and all existing tensor/selector
notation. The older `q_U` continues to mean the intermediate
normalization structural map; it is not silently reused for the new
refinement. The manuscript's `Z_U` denotes this same existing
normal-closure normalization on the chart, while `π_U` and `λ_U`
denote the actual chart and refinement maps. The final inventory is
19 APIs, seventeen in `FiniteEtaleNormalClosure.lean` and two tensor helpers.

The checked primary sources are Stacks Tags 02GN, 02GO and 02GP for
composition, base change and open-immersion etaleness, and Tag 02GW for
the etale cancellation law, and Tag 00GQ for lying over along integral
inclusions. The actual marked cover and factorization equalities are
direct project constructions. The two helpers compile (2452 jobs), and
the scoped main build passes 2761 jobs with all 19 APIs and no warnings
or errors.
The static central inventory is 959 checks, 565 examples and 851 axiom
reports after appending nineteen checks and reports. Its historical
prefix is byte-identical to `4de0703`; the historical central file was
not re-elaborated in this checkpoint.
The 81-page PDF (831678 bytes) rebuilds with no undefined references or
citations, overfull or underfull boxes, or final-log warnings. Visual
checks of pages 12, 13, 61, 72 and 78 pass. Independent geometry and
Lean--TeX review pass with no defects. The focused SP81 suite passes
25 examples and exactly nineteen enforced standard-three axiom audits,
with a duplicate-free registry check and no warnings or errors. Four
chart regressions omit finite/etale premises; six inverse-image
regressions omit etaleness. Five fresh neighbor suites pass without
warnings or errors: SP80 `NormalizationIntegralFactorVerification`
passes 30 examples and 28 enforced audits; SP77 `NormalClosureTensorVerification`
passes 28/17; SP76 `FiniteNormalClosureVerification` passes 23/7;
SP71 `FiniteAffineChartVerification` passes 18/11; and SP74
`FunctionFieldNormalClosureVerification` passes 22/7. Together the six
suites pass 146 examples and 89 enforced standard-three axiom audits.
The full build passes 3200 jobs with only the two unchanged
`Challenge.lean` placeholder warnings at lines 33 and 46. The unchanged
`ProofDependencies` audit passes six primary endpoint contracts and two
support reports without warnings or errors; its file is unchanged.
All nineteen code/central/test/TeX API parity checks pass. The historical
`Verification.lean` and audit 0018 prefixes and the SP80-to-end queue
suffix are byte-identical to `4de0703`.
Earlier checkpoint results retain their original scope.

The next bounded bridge is localization and overlap
compatibility of these actual models and maps, followed by cocycle
identities, gluing and a compatible global Galois action. Deriving normal
stalks from smooth geometry and Chow--Betti generation remain separate.
The SP80 (2026-09-19) block and all subsequent queue history below are
preserved unchanged.

SP80 (2026-09-19): **integral trace section / actual normalization factor**.
The checkpoint is proved and validated. Over a normal base domain
`B` with fraction field `K`, let `N/K` be finite and `T=IntCl_B(N)`.
For an actual map `f:S -> T`, with `S/B` formally unramified and
essentially of finite type, `UnramifiedIntegralFactor.lean` contracts
the existing `Algebra.FormallyUnramified.sec` by `Algebra.intTraceAux`
to construct a `B`-linear map `r:T -> S`. It satisfies the source-action
law `r(f(s)*t)=s*r(t)`. If the image of `S` spans `N` over `K`, the
central-tensor contraction identity in `SeparabilityTrace.lean` proves
`f(r(t))=t`. Thus `E=r(1)` is an integral idempotent with `f(E)=1`,
`E*s=r(f(s))`, `E*s=0 ↔ f(s)=0`, and `ker(f)=(1-E)`.

The new `normalizationTensorEvaluation_span` derives the needed spanning
condition from the existing SP78 comparison and generic surjectivity.
`NormalizationIntegralFactor.lean` specializes to the actual finite
normal etale intermediate model with fraction field `L`, constructs
`r_B` and `E_m` on the original integral tensor carrier, and identifies
`P_B/(1-E_m)` with `T` by the original evaluator. The quotient is finite
because `P_B` is finite; localization away from `E_m` gives its etaleness.
Under extension separability, the generic comparison is exactly
`β_Σ(1⊗E_m)=e_m`. Separability is used for this comparison with SP79,
not as an added premise of the integral factor or whole-ring finite-etale
result. No Noetherian-base, whole-source normality/flatness or assumed
integral-surjectivity premise is added.

Notation parity:

| Lean object / group | Mathematical role | TeX notation |
| --- | --- | --- |
| `traceContraction`, `_tmul`, `_eq_lmul_of_central`, `_eq_one_of_central`, `_one_tmul_mul` | contraction of a central separability tensor by the algebra trace | prose only; trace-contraction identity |
| `unramifiedIntegralSection`, `_mul`, `_rightInverse`; `unramifiedIntegralEvaluation_surjective` | generic integral trace section, source-action law and derived surjectivity | prose only; `r` within the generic lemma |
| `unramifiedIntegralIdempotent`, `_map`, `_mul`, `_baseChange_mul`, `_isIdempotentElem`, `_mul_eq_zero_iff`; `unramifiedIntegralEvaluation_ker_eq_span_one_sub` | integral selector, scalar-extension action, idempotence and complementary kernel | prose only; `E=r(1)` within the generic lemma |
| `NormalClosureData.normalizationTensorEvaluation_span` | derive generic spanning for the original integral evaluation | existing \(\operatorname{ev}_B\), \(\beta_\Sigma\) and \(\operatorname{ev}_K\); no independent notation |
| `.normalizationTensorSection`, `_mul`, `_rightInverse`; `.normalizationTensorEvaluation_surjective` | actual normalization trace section and original evaluation | \(r_B:T\to P_B\), \(\operatorname{ev}_B r_B=\operatorname{id}_T\) |
| `.normalizationTensorIdempotent`, `_spec`, `_baseChange` | integral selecting idempotent and exact generic comparison | \(E_{\mathfrak m}=r_B(1)\), \(\ker(\operatorname{ev}_B)=(1-E_{\mathfrak m})\), \(\beta_\Sigma(1\otimes E_{\mathfrak m})=e_{\mathfrak m}\) |
| `.normalizationTensorQuotientEquiv`, `_mk` | actual complementary quotient and evaluator-preserving comparison | \(P_B/(1-E_{\mathfrak m})\simeq_B T\); no second symbol for the comparison |
| `.normalization_finite_of_etaleModel`, `.normalization_etale_of_etaleModel` | finite etale structure on the existing normalization | existing \(T=\widetilde B_N\) |

Retain the existing `Σ`, `P_B`, `P_K`, `ev_B`, `ev_K`, `m`, `β_L`,
`β_N`, `β_Σ` and `e_m`. The only new independent notation is the
actual section `r_B` and its integral selector `E_m`; no second kernel
symbol, tensor carrier, field marking, normalization model or Chow
projector is introduced. The section is linear with the stated action
law, not an asserted unital algebra section. The proposed normality/
integral-closedness theorem for all of `P_B` is bypassed, not proved.

The exact primary source checked is [Stacks, Lemma 10.151.4, Tag
02FL](https://stacks.math.columbia.edu/tag/02FL), for the unramified
diagonal localization/separability tensor only. The trace contraction,
actual integral section, normalization factor and generic comparison
are direct project proofs, not new source-input packages or axioms.

Validation status: complete. All 28 public APIs compile: five
trace-contraction, eleven generic integral-factor, one generic-span,
and eleven marked normalization-factor declarations. The scoped
`NormalizationIntegralFactor` build passes 2759 jobs without warnings.
The central inventory is 940 checks, 565 examples and 832 axiom reports;
the historical audit prefix is byte-identical and was not rerun in full.
All 28 declarations have notation/source parity. The 79-page PDF
(826296 bytes) passes its build and final warning/box/reference scan.
Visual checks of pages 11, 12, 13, 60, 71, 72, 77 and 79 pass. The
historical 0018 prefix and SP79-to-end queue suffix are byte-identical.
The focused suite passes 30 examples and three private helpers without
warnings or errors, with 28 enforced standard-three axiom audits and a
unique-declaration registry check. It includes the actual finite-etale
scheme-chart ring specialization: both section-ring normality inputs
follow from normal stalks, and no Noetherianity premise is used.
Independent mathematical and Lean--TeX review pass. The full build,
with 3198 jobs, passes with only the two unchanged Challenge placeholder
warnings. Fresh SP79, SP78, SP77, SP76 and SP74 suites pass 25/16,
25/13, 28/17, 23/7 and 22/7 examples/enforced audits respectively,
without warnings or errors. These six suites pass 153 examples and
88 enforced standard-three axiom audits in total. The fresh unchanged
dependency audit passes six primary endpoint contracts and two support
reports. Earlier checkpoint counts retain their historical scope.

The next bounded bridge is to integrate the verified
scheme-chart ring specialization into a named actual affine
normalized-cover constructor and structural-map/finite-etale morphism
endpoints, followed by overlap compatibility and gluing of the global
finite etale Galois refinement. The earlier affine-cover
constructor retains its stronger normality/Noetherianity and upstairs-normal-stalk
inputs; deriving the stalk inputs from smooth geometry and Chow--Betti
generation remain separate. The SP79 (2026-09-18) block and all subsequent
queue history below are preserved unchanged.

SP79 (2026-09-18): **selected generic evaluation factor / canonical idempotent**.
`ReducedArtinianFactor.lean` constructs the factor selected by a surjective
algebra map `f:P -> N` from a reduced Artinian algebra to a field. The
maximal-ideal decomposition splits as `N × Π_{I ≠ ker(f)} P/I`; its
first projection is exactly `f`, pointwise and as an algebra homomorphism.
The inverse image `e` of `(1,0)` is idempotent, satisfies `f(e)=1`, and
annihilates exactly `ker(f)`. The kernel is the principal ideal `(1-e)`.
Value one and annihilation of the kernel characterize `e` uniquely;
idempotence need not be assumed in the uniqueness theorem.

`NormalClosureFactor.lean` proves the original `P_K` finite over `K`
without separability, and etale under separability of `L/K`. It derives
reduced Artinianness and applies the generic construction to the existing
surjective `ev_K`. Thus `Φ_m:P_K ≃_K N × Q_m` selects the marked
`N`, with `Q_m` the actual product of residue quotients at the other
maximal ideals. The full identity `pr₁∘Φ_m=ev_K` is proved, and
`e_m=Φ_m⁻¹(1,0)` has the canonical properties above. No new tensor
carrier, source axiom, field marking or independently supplied splitting
is introduced. No unital section `N -> P_K` or new Chow projector is
asserted.

Notation parity:

| Lean object / group | Mathematical role | TeX notation |
| --- | --- | --- |
| `fieldQuotientProductEquiv` and its pointwise / homomorphism first-projection laws | generic selected field-quotient decomposition | prose only; the generic algebra lemma |
| `fieldQuotientIdempotent` and its idempotence / map / annihilator / uniqueness laws; `fieldQuotient_ker_eq_span_one_sub` | generic selecting element and complementary principal kernel | prose only; `e` within the generic lemma |
| `NormalClosureData.tensorSource_finite` / `.tensorSource_etale` | finite / separable-etale properties of the existing tensor source | existing \(P_K\) |
| `.tensorEvaluationProductEquiv` / `.fst_comp_tensorEvaluationProductEquiv` | selected generic product equivalence and exact first projection | \(\Phi_{\mathfrak m}:P_K\simeq_K N\times Q_{\mathfrak m}\), \(Q_{\mathfrak m}=\prod_{I\ne\mathfrak m}P_K/I\), \(\operatorname{pr}_1\Phi_{\mathfrak m}=\operatorname{ev}_K\) |
| `.tensorEvaluationIdempotent` / `_spec` / `_unique` | the canonical algebra-factor selector and its characterization | \(e_{\mathfrak m}=\Phi_{\mathfrak m}^{-1}(1,0)\), \(\mathfrak m=(1-e_{\mathfrak m})\) |

Retain the existing `Σ`, `P_B`, `P_K`, `ev_B`, `ev_K`, `m`, `β_L`,
`β_N` and `β_Σ`. The new algebra selector is not a second Chow-level
projector. The checked standard source is Stacks Lemma 10.143.4, Tag
00U3, for classification of etale algebras over a field. The selected
factor, original evaluator comparison and idempotent laws are direct
Lean proofs, not additional cited assumptions.

The inventory is sixteen new APIs: nine generic and seven marked
normal-closure declarations, all registered. Validation completed on
2026-09-19 after the checkpoint began on 2026-09-18. The generic leaf
build passes 1453 jobs and the specialization passes 2125 jobs, both
without warnings. The full build passes 3195 jobs with only the two
existing Challenge placeholder warnings. The focused suite passes
25 examples and 16 enforced standard-three axiom audits; fresh SP78,
SP77, SP76 and SP74 pass 25/13, 28/17, 23/7 and 22/7, respectively.
Thus the five suites pass 123 examples and 60 enforced axiom audits.
The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.

The central inventory is 912 checks, 565 examples and 804 axiom reports
after appending sixteen checks and reports; the historical prefix is
byte-identical and was not rerun in full. The 78-page PDF (819834 bytes)
passes its build and warning/box/reference scan. Visual review of pages
11, 12, 59, 69, 70, 75 and 78 passes, as does independent mathematical
and Lean--TeX review. The historical audit prefix and SP78-to-end queue
suffix remain byte-identical. The checkpoint is proved and validated.

Next prove the required integral-closedness of `P_B` inside `P_K`,
descend the canonical generic idempotent, and identify the selected image
with `IntCl_B(N)`. Integrality alone does not prove descent; `P_B`
need not be a domain. Whole-chart etaleness, overlaps and gluing remain
further geometric steps;
Chow--Betti generation remains independent. Historical SP78 and earlier
queue blocks below are preserved unchanged.

SP78 (2026-09-18): **tensor base change / full evaluator square**.
`PiTensorBaseChange.lean` constructs algebra equivalences for factorwise
tensor congruence and scalar extension of the existing finite-index
tensor product. Its factor, inverse-factor and pure-tensor formulas
retain the original generators; no replacement tensor carrier is used.

`NormalizationBaseChange.lean` uses fraction-field localization to
construct `K⊗_B IntCl_B(L) ≃_K L` with the actual multiplication formula.
The one-factor theorem only needs compatible scalar towers, the specified
fraction field and algebraicity of `L/K`; it adds no normality,
Noetherianity, separability or finite-degree premise. Applied factorwise
to the marked closure, it constructs `K⊗_B P_B ≃_K P_K`. The full
evaluator square is proved as equality of algebra homomorphisms, not
assumed or restricted to selected pure tensors.

The three existing generic evaluation helpers move unchanged from
`NormalClosureTensor.lean` to `FiniteTensorProduct.lean`, under their
existing public names. This removes a field-normalization dependency
from generic tensor base change without duplicating the evaluator or
altering its maps. No new source axiom or geometric input package appears.

Notation parity: retain `Σ`, `P_B`, `P_K`, `ev_B`, `ev_K`, `m` and
the existing `\widetilde B_L`, `\widetilde B_N`. Write `β_L` and `β_N`
for the one-factor comparisons, and `β_Σ` for the tensor comparison.
The full square is `ev_K∘β_Σ=β_N∘(1_K⊗ev_B)`. Generic congruence,
scalar-extension helpers and formulas are prose-only; no new projector,
normalization ring or field marking is introduced. Stacks Lemma 10.36.11,
Tag 0307, is checked for the localization-of-integral-closure input only.

The API inventory is seven generic tensor declarations and six
normalization declarations; the three relocated helpers are not new
APIs. The central inventory is 896 checks, 565 examples and 788 reports
after appending thirteen checks and reports; its historical prefix is
byte-identical and was not rerun in full. The 76-page PDF (812185 bytes)
passes its build and clean warning/box/reference scan; visual checks of
pages 10, 11, 58, 68, 69, 75 and 76 pass. Both new leaves compile without
warnings. `NormalizationBaseChangeVerification.lean` passes 25 examples
and 13 enforced standard-three axiom audits, including three actual
function-field cases. The full build passes (3189 jobs; only the two
existing Challenge placeholder warnings). Fresh SP77, SP76 and SP74
reruns pass 28/17, 23/7 and 22/7, respectively: 98 examples and 44 enforced
axiom audits across the four suites. The fresh unchanged dependency audit
passes six primary endpoint contracts and two support reports.

Next prove
generic direct-factor/idempotent splitting using separability, then
extend/select the integral factor and prove its image normal and equal
to `IntCl_B(N)`. The new base-change equivalence and full square do not
already prove those steps or whole-chart etaleness. Overlaps, gluing and
Chow--Betti generation remain separate. Historical SP77 and earlier queue
blocks below are preserved unchanged.

SP77 (2026-09-18): **finite tensor source / marked evaluations**.
`FiniteTensorProduct.lean` proves finiteness and etaleness independently
for the existing finite-index tensor carrier. Finite-index induction
uses existing binary tensor instances and private algebra-equivalence
upgrades of existing reindexing/regrouping maps. No public replacement
tensor representation is introduced.

`NormalClosureTensor.lean` defines the common finite-family algebra-map
evaluation and its pure-tensor/factor formulas. Specializing to all
embeddings of the existing intermediate field in its marked normal
closure gives an evaluation onto that same `N`. Its algebraic range
contains every conjugate field; the normal-closure property proves
surjectivity. The actual kernel is maximal and its quotient is
canonically equivalent to `N`, with the representative formula proved.
These results use no separability or independently supplied surjectivity.

`NormalizationTensor.lean` specializes the same evaluator to the existing
restrictions `normalizationMap N (σ.restrictScalars B)`. The integral
factor formula and the equality with field evaluation on integral pure
tensors are proved after inclusion into `N`. An actual finite normal
intermediate model with fraction field `L` makes the source finite; its
etaleness makes the source etale. The original field marking, integral
closures and scalar towers are reused. No new source axiom or input
package is introduced. The two source-property theorems omit the unused
`Algebra B K`, `Algebra B N`, `IsScalarTower B K L`, and
`IsScalarTower B K N` assumptions; evaluation retains its actual scalar
compatibility. Stacks Lemma 10.143.3, Tag 00U2, parts (2) and (3), is
checked and cited for source etale stability under composition/base
change only, not for identification or etaleness of the target.

Notation parity: write `Σ=Hom_K(L,N)`, `P_K=⊗_{Σ,K}L` and
`P_B=⊗_{Σ,B}IntCl_B(L)`, with evaluations `ev_K` and `ev_B`, and
`m=ker(ev_K)`. In the manuscript the unchanged integral closures are
`\widetilde B_L` and `\widetilde B_N`, evaluation is typeset
`\operatorname{ev}_K`/`\operatorname{ev}_B`, and the kernel is
`\mathfrak m`. These are the existing tensor carriers with genuinely
constructed maps and their actual kernel, not new abstract models.
Keep `I` for the existing inertia/split-index notation and `μ` for the
existing collision multiplication. The generic evaluation is distinct
from the older `N⊗_K L` sheet comparison: its all-embeddings source maps
onto `N`, rather than identifying the one-factor base change with the
generic-sheet algebra. The generic finite-family evaluator and all
compatibility/property theorems are prose-only helpers, not extra
projectors or independently named geometric objects.

Validation: all 17 new APIs compile. The central inventory is 883 checks,
565 examples and 775 reports after appending 17 checks and reports; its
historical prefix is byte-identical and was not rerun in full. The 76-page
PDF (805454 bytes) passes its build and clean warning/box/reference scan;
visual checks of pages 9, 10, 58, 68, 69, 75 and 76 pass, as do independent
code and Lean--TeX reviews covering all 17 names. The full build passes
(3187 jobs; only the two existing Challenge placeholder warnings).
`NormalClosureTensorVerification.lean` passes 28 examples and 17 enforced
standard-three axiom audits without warnings. Fresh SP76 and SP74 reruns
pass 23/7 and 22/7, respectively: 73 examples and 31 audits in these three
suites. The fresh unchanged dependency audit passes six primary endpoint
contracts and two support reports.

The generic quotient is not an integral direct factor, and no
scalar-extension/localization isomorphism between
these tensor sources is yet asserted. First construct the canonical
comparison `K⊗_B P_B ≃ P_K` and equality of evaluator homomorphism
composites. Then, under separability, prove a generic direct-factor/
idempotent splitting of the maximal quotient; that splitting is not yet
formalized. Next extend/select the integral factor, prove its image normal
and identify it with the existing `IntCl_B(N)`. Whole-chart target
etaleness, overlaps, gluing and Chow--Betti generation remain separate.
Historical SP76 and earlier
queue blocks below are preserved unchanged.

SP76 (2026-09-18): **finite normal-closure normalization / actual affine cover**.
`FiniteNormalClosure.lean` supplies seven declarations using existing
carriers, fields, normalization maps and the existing `NormalizedCover`:

- `CollisionFoundations.normalizedCoordinateRing_finite_of_isSeparable`
  applies Mathlib's `IsIntegralClosure.finite` over a normal Noetherian
  base with its fraction field and a finite separable extension.
- `NormalizationInertia.normalClosureNormalizationRing_finite`
  specializes to a marked normal closure using `D.finiteNormal` and
  `D.isSeparable`.
- `NormalizationInertia.normalizedCoverOfFiniteNormalAffineModel` and
  `conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel`
  use a single finite normal intermediate algebra `A`, with no second
  supplied algebra `S`.
- `CollisionFoundations.functionFieldNormalClosure_normalization_finite`
  gives chart finiteness for the actual generic extension of a finite
  dominant formally unramified morphism of integral schemes.
- `CollisionFoundations.finiteAffinePreimageNormalizedCover` and
  `conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover`
  construct the cover and separation directly from the actual inverse
  image of a nonempty affine chart, its normalization isomorphism and
  `functionFieldNormalClosureData p`.

Base normality and Noetherianity remain explicit. The last two declarations
also assume normal stalks on the inverse-image open. Finite etale morphisms
supply formal unramifiedness. No perfectness, dimension-one or Dedekind
premise, new carrier, new cover package, projector or source axiom is
introduced. The exact standard finiteness result is Stacks Lemma 10.161.8,
Tag 032L; Lean uses the checked Mathlib theorem.

The retained two-model constructor is not redundant: supplying both
finite normal models avoids the new constructor's normal-Noetherian base
and extension-separability premises. The new one-model constructor trades
those explicit hypotheses for removal of the separately supplied `S`.

Notation parity: `B_U=Γ(X,U)`, `A_U=Γ(Y,V)`, `V=p^{-1}U`,
`K=K(X)`, `L=K(Y)` and `\mathcal N=(K,L,N,\iota)` retain their existing
meanings. The finite `N`-model is the existing integral-closure ring,
not a new `S` carrier. `\nu_{p,U}` denotes the existing affine-preimage
normalization-isomorphism map, and `C_U` the constructed instance of the
existing chartwise cover `C`. `\kappa_p` and the generic-germ scalar maps
are unchanged, as are the boundary ideals and the single projector.

Validation: the full build passes (3180 jobs; only the two existing
Challenge placeholder warnings). `FiniteNormalClosureVerification.lean`
passes 23 examples and seven enforced standard-three axiom audits;
fresh consumer, affine-chart and normal-closure suites pass 24/29,
18/11 and 22/7. The central inventory has 866 checks, 565 examples and
758 reports after appending seven checks and reports; its historical
prefix is byte-identical and was not rerun in full. The 74-page PDF
(788608 bytes) passes its build and clean warning/box/reference scan;
visual checks of pages 8--10, 57, 66--67 and 73--74 pass, as do
independent code and Lean--TeX reviews. The fresh unchanged dependency
audit passes six endpoint contracts and two support reports.

Next identify this specific normal-closure
normalization as a direct factor of a finite tensor construction from
the actual finite etale intermediate algebra. That unproved comparison
is the proposed route to whole-chart etaleness, which generic etaleness,
localization to `N`, finiteness and full-visible separation do not supply.
Overlap compatibility, gluing and the actual
global finite etale Galois refinement remain subsequent. Deriving normal
stalks from smooth geometry and Chow--Betti generation remain separate.
Historical SP75 and earlier queue blocks below are preserved unchanged.

SP75 (2026-09-18): **local separability / consumer hypothesis cleanup**.
The existing declarations now state the hypotheses actually used. No
new library declarations, aliases, packages, carriers, maps, projectors or source
axioms are introduced. Twenty-six signatures are generalized, two
existing helpers are moved and one compatibility-wrapper proof is changed.

Fourteen declarations now have explicit `[Algebra.IsSeparable K L]`:

- `NormalClosureData.fixedField_intermediateFixingSubgroup`;
- `intermediateNormalizationEquivFixedRing` and its `coe` formula;
- `baseEquivFullInvariantNormalizationRing`;
- `NormalClosureData.normalClosureTensorToGenericSheets_bijective`,
  `.normalClosureTensorGenericSheetsEquiv` and
  `.normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv`;
- the four denominator/landing/colon consumers in
  `NormalizationTraceBound.lean`, and the three trace-pole/trace-colon/
  trace-landing consumers in `BoundaryPole.lean`.

Twelve declarations lose `PerfectField K` with no separability replacement:
`intermediateFixingSubgroup_normalCore_eq_bot`; the three full-visible
unit-ideal/separation results; the finite-affine-cover separation result;
the three inertia-diagram consequences; the two sheet-extension and two
Galois-projector-extension consequences. Other finiteness, normality,
Noetherianity, formal-unramifiedness, ramification-realization and purity
hypotheses remain exactly where required. In particular, removal of a
field hypothesis is not a construction of those geometric inputs.

`NormalClosureData.isSeparable` and `.isGalois_of_isSeparable` move from
`NormalClosureConstruction.lean` into `NormalClosure.lean` under the same
names. The sole library `[PerfectField K]` compatibility wrapper is the
existing `.isGalois`, which derives separability of the finite marked
extension and delegates to `.isGalois_of_isSeparable`. The trace denominator
uses `.isSeparable` directly. These 26 generalized signatures, two moved
helpers and one wrapper are the 29 declarations selected for fresh audits.

Notation parity is unchanged: `\mathcal N=(K,L,N,\iota)`, `\kappa_p`,
the fixed-field/sheet comparison maps, `J_{\mathrm{fix}}`,
`J_{\mathrm{mov}}`, `J_{\mathrm{fm}}`, `T^\vee_B` and the existing
projector all denote the same objects. This checkpoint changes hypothesis
placement and module ownership, not their definitions or TeX identities.

Validation: `NormalClosureConsumersVerification.lean` passes 24 examples
and 29 enforced standard-three axiom audits. The updated trace and pole
suites pass 14/11 and 12/9, and fresh SP74 and finite-affine-cover suites
pass 22/7 and 20/17. The central inventory has 859 checks, 565 examples
and 751 reports after appending 29 checks and reports; its historical
prefix is byte-identical and was not rerun in full. The 74-page PDF
(785575 bytes) passes its build and clean warning/box/reference scan;
visual checks of pages 9--13, 57 and 66--67 and independent Lean--TeX
review pass. The full build passes (3179 jobs; only the two existing
Challenge placeholder warnings). The fresh unchanged dependency audit
passes six endpoint contracts and two support reports.

The next bounded theorem should derive
`Module.Finite B (integralClosure B N)` over normal Noetherian affine `B`
from the constructed finite separable `N/K`, replacing the separately
supplied second finite normal algebra `S`. The inspected Mathlib
`IsIntegralClosure.finite` has no dimension-one or Dedekind premise despite
its file location; this specialization is not yet implemented. Normality
of `B` remains explicit. Etaleness of that `N`-model, overlap compatibility,
normalization gluing and the actual global Galois scheme refinement follow
as separate tasks, as do normal stalks from smoothness and Chow--Betti
generation. Historical SP74 and earlier queue blocks below are preserved
unchanged.

SP74 (2026-09-18): **constructed marked normal closure / Galois bridge**.
`NormalClosureConstruction.lean` constructs the existing
`NormalClosureData K L N` from a finite field extension, with
`N=IntermediateField.normalClosure K L (AlgebraicClosure L)`.
The marked embedding, viewed in the algebraic closure, is proved equal
to the original upstairs-field inclusion. The constructor itself does
not require separability or perfectness. For any supplied marked normal
closure of separable `L/K`, the new generic theorems prove separability
and Galoisness of `N/K` without `PerfectField K`.

`FunctionFieldNormalClosure.lean` constructs this datum from the actual
generic-stalk extension of a finite dominant morphism of integral
schemes. The embedding formula preserves the canonical marking; scheme
formal unramifiedness supplies separability by SP73 and hence makes
the constructed finite normal closure Galois. Finite etale morphisms
are a specialization.

The seven public declarations are `NormalClosureData.ofAlgebraicClosure`,
`NormalClosureData.ofAlgebraicClosure_embedding_apply`,
`NormalClosureData.isSeparable`, `NormalClosureData.isGalois_of_isSeparable`,
`functionFieldNormalClosureData`,
`functionFieldNormalClosureData_embedding_apply` and
`functionFieldNormalClosure_isGalois`.

Notation parity: retain the existing `\mathcal N=(K,L,N,\iota)` and put
`N=\bigvee_{\sigma:L\to_K\overline L}\sigma(L)\subseteq\overline L`,
the existing Mathlib normal-closure intermediate field. The ambient
inclusions `j_N,j_L` satisfy `j_N\circ\iota=j_L`, the embedding formula.
For schemes, `K=K(X)`, `L=K(Y)` and the `K` action is the existing
`\kappa_p`. No new carrier alias, normal-closure package, generic map,
ideal or projector is introduced. Manuscript Proposition
`prop:constructed-normal-closure` uses this same notation.

The manuscript cites Stacks 09DT for normal-closure existence and
0BMG(1) for finite normal containment in the chosen algebraic normal
ambient field; the [source ledger](../SOURCE_LEDGER.md) records the
exact match. These citations are attribution, not added Lean axioms.
The full build passes (3179 jobs), with only the two expected unchanged
Challenge placeholder warnings.
`lake env lean research/FunctionFieldNormalClosureVerification.lean`
passes through the boundary umbrella: twenty-two regressions and seven
enforced axiom
allowlists, permitting only `propext`, `Classical.choice` and `Quot.sound`.
The fresh SP73 rerun passes sixteen
regressions and three enforced standard-axiom audits; the fresh unchanged
dependency audit passes six endpoint contracts and two support reports.
The central inventory now has 830 checks, 565 examples and 722 reports,
with seven checks and seven reports appended. Its historical prefix is
preserved byte-for-byte; the entire historical suite was not rerun.
The single PDF build passes (74 pages, 785530 bytes), with no warning,
overfull, underfull, undefined-reference or multiply-defined-label
diagnostics. Final pages 6, 8, 9, 56, 57, 66, 67, 72 and 73 pass visual
inspection, including Proposition 3.5, the crosswalk, registry and new
bibliography entries. Independent core/scheme/manuscript review passes.

Next connect the local-separability Galois
result to the existing fixed-field, core-free and selector consumers,
replacing avoidable perfectness assumptions. No old `PerfectField K`
consumer signature is changed in SP74. The inspected next proof uses
extension separability for fixed-field and selector/tensor comparisons;
core-freeness appears to need only existing normality and finiteness,
so audit removal of both perfectness and separability there and in the
full-visible boundary consumers. That removal is not yet proved.
Scheme-level Galois refinement,
normal stalks, normalization gluing and Chow--Betti generation remain
separate. Historical SP73 and earlier queue blocks below are preserved
unchanged.

SP73 (2026-09-18): **actual generic formal unramifiedness / separability**.
`Boundary/Normalization/SeparableFunctionField.lean` implements the
previously inspected localization route. For a dominant affine formally
unramified morphism of integral schemes, the actual section-algebra
property passes to the upstairs fraction field, then through SP72's
proved scalar tower to the downstairs function field. The affine-chart
theorem accepts a nonempty affine base open, and the global theorem
chooses one internally. Neither formal-unramifiedness theorem needs a
finite morphism.

For a finite dominant formally unramified morphism, SP72 gives
finite-dimensionality, hence essential finite type. Mathlib's
field-theoretic formal-unramifiedness theorem gives separability of the
same actual `kappa_p` algebra. Finite etale morphisms satisfy the scheme
formal-unramifiedness hypothesis automatically. No normality, perfectness,
characteristic-zero or Noetherian premise is used.

The three public declarations, in `CollisionFoundations`, are
`functionFieldMapOfDominant_formallyUnramified_of_affine`,
`functionFieldMapOfDominant_formallyUnramified` and
`functionFieldMapOfDominant_isSeparable`.
Notation parity: `\kappa_p:K(X)\to K(Y)` remains the same generic-stalk
map; `B_U,A_U` and `\rho_{X,U},\rho_{Y,V}` remain the same section rings
and generic germs. The new declarations prove properties of this existing
algebra, not a second field embedding, field carrier, ideal, projector or
input package. Manuscript Proposition `prop:separable-function-field`
uses the same `\kappa_p` and distinguishes affine formal unramifiedness
from finite separability.

The full build passes (3177 jobs), with only the two expected unchanged
Challenge placeholder warnings.
`lake env lean research/SeparableFunctionFieldVerification.lean` passes:
sixteen focused regressions and three enforced axiom allowlists,
permitting only `propext`, `Classical.choice` and `Quot.sound`.
The fresh SP72 rerun passes eighteen
examples and eleven enforced standard-axiom audits. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.
The central inventory now has 823 checks, 565 examples and 715 reports,
with three checks and three reports appended. Its historical prefix is
preserved byte-for-byte; the entire historical suite was not rerun.
The single PDF build passes (73 pages, 781158 bytes), with no warning,
overfull, underfull, undefined-reference or multiply-defined-label
diagnostics. Final pages 8, 9, 54, 55, 56, 65 and 66 pass visual inspection;
Appendix C starts on a new page so its headings stay with the table.

Next construct marked normal-closure field data
from the actual finite separable extension. The existing downstream
`PerfectField K` hypotheses remain undischarged. Actual global Galois
refinement, normal stalks from smooth geometry, gluing and Chow--Betti
generation remain separate tasks. Historical SP72 and earlier queue
blocks below are preserved unchanged.

SP72 (2026-09-18): **actual dominant function fields / finite extension**.
`Cycles/FunctionFieldMap.lean` constructs the actual generic-stalk map
for a dominant morphism of integral schemes. Nonempty inverse images
need only dominance, and generic-point preservation needs only
irreducibility. The field map is injective, commutes with section germs
on every nonempty base open, satisfies identity and contravariant
composition, and equals the existing open-immersion isomorphism.

`Boundary/Normalization/FiniteFunctionField.lean` uses that germ square
to derive section scalar towers on all nonempty opens. For finite `p`,
the actual finite affine section algebra localizes to the finite extension
of the actual function fields. The global theorem chooses a nonempty
affine chart internally. No normality, etaleness, Noetherianity,
separately supplied chart or independent extension premise is added.

The eleven new public declarations are
`nonempty_preimage_of_isDominant`, `genericPoint_eq_of_isDominant`,
`functionFieldMapOfDominant`, `functionFieldMapOfDominant_injective`,
`functionFieldMapOfDominant_germ`,
`functionFieldMapOfDominant_eq_openImmersion`,
`functionFieldMapOfDominant_id`, `functionFieldMapOfDominant_comp`,
`functionFieldMapOfDominant_sectionScalarTower`,
`functionFieldMapOfDominant_finiteDimensional_of_affine` and
`functionFieldMapOfDominant_finiteDimensional`.

Notation parity: `\kappa_p:K(X)\to K(Y)` denotes the actual
`functionFieldMapOfDominant p`; `\rho_{X,U}` and `\rho_{Y,V}` denote
the existing `germToFunctionField` maps, with `V=p^{-1}U`.
The germ theorem is `\kappa_p\circ\rho_{X,U}=\rho_{Y,V}\circ p^*`.
The SP71 section-ring notation `B_U,A_U` and actual pullback `p^*`
are retained. The finite-dimensional result uses the algebra induced by
this exact `\kappa_p`, not a separately chosen field embedding. No new
field carrier, cover package, ideal or projector is introduced.

The full build passes (3176 jobs), with only the two expected unchanged
Challenge placeholder warnings.
`lake env lean research/FiniteFunctionFieldVerification.lean` passes
without warnings: eighteen focused regressions and eleven enforced
axiom allowlists permitting only `propext`, `Classical.choice` and
`Quot.sound`. The fresh SP71 rerun,
`lake env lean research/FiniteAffineChartVerification.lean`, passes its
eighteen regressions and eleven enforced audits without warnings.
The fresh unchanged `research/ProofDependencies.lean` audit passes all
six endpoint contracts and two support reports. The central inventory
now has 820 checks, 565 examples and 712 reports, with eleven checks and
eleven reports appended. Its historical prefix is preserved byte-for-byte;
the entire historical suite was not rerun.

The single PDF build passes (72 pages, 778658 bytes), with no warning,
overfull, underfull, undefined-reference or multiply-defined-label
diagnostics. Final pages 7, 8, 54, 55, 64 and 65 pass visual inspection;
independent core/manuscript review passes.

Next construct marked normal-closure field data
from this actual finite extension and establish separability for the
Galois conclusion. Separability has not yet been derived from scheme
etaleness or characteristic zero/perfectness of the intended complex
scalar structure. The next priority is the inspected, unimplemented
etale/localization route through `FormallyUnramified` and its field
separability theorem; this does not prove downstream `PerfectField K`
hypotheses. Actual global finite etale Galois
refinement, normal stalks from smooth geometry, gluing and Chow--Betti
generation remain separate tasks. The manuscript states the map, germ
square and finite-dimensionality with the same hypotheses. Historical
SP71 and earlier queue blocks below are preserved unchanged.

SP71 (2026-09-18): **actual finite-morphism affine charts**.
`AffineEtaleAlgebra.lean` proves smoothness of the actual ring map on
compatible affine charts of a smooth morphism, then etaleness on affine
charts of an etale morphism and on global sections of affine schemes.
`AffineNormality.lean` derives normal affine sections from normality of
the actual stalks on a nonempty affine open of an integral scheme.

`FiniteAffineChart.lean` starts with a finite morphism `p:Y -> X` and
affine `U`. Its whole inverse image is affine; its existing section ring
is finite over the existing section ring of `U`, and etale when `p` is
etale. No integrality, nonemptiness or normality is required for this
finite/etale algebra layer. For integral `Y` and a nonempty inverse image,
explicit normal stalks supply normality of the section ring. Its fraction
field is the existing `Y.functionField`. The canonical isomorphism to
normalization is proved to commute over the original `X`; finiteness and
etaleness transport to the normalization. No replacement ring, field,
cover package, ideal or projector is introduced.

The eleven new public declarations are `affine_appLE_smooth`,
`affine_appLE_etale`, `affine_appTop_etale`,
`affineSections_isIntegrallyClosed_of_stalks`,
`finiteAffinePreimage_moduleFinite`, `finiteAffinePreimage_etale`,
`finiteAffinePreimageNormalizationIso`,
`finiteAffinePreimageNormalizationIso_hom`,
`finiteAffinePreimageNormalizationIso_hom_comp_toBase`,
`finiteAffinePreimage_normalization_finite` and
`finiteAffinePreimage_normalization_etale`.

Notation parity: `B_U=\Gamma(X,U)` and
`A_U=\Gamma(Y,p^{-1}U)` are existing section rings; `K(Y)` denotes
`Y.functionField`. The scalar map `p^*` is the actual `p.app U`, and its
composite with the generic germ gives the map to `K(Y)`.
`\nu_{p,U}` denotes `finiteAffinePreimageNormalizationIso`, from
`V=p^{-1}U` to `\operatorname{Spec}(\operatorname{IntCl}_{B_U}K(Y))`.
This integral closure is over the image of the actual scalar map;
injectivity of that map is not assumed. `q_U` denotes
`normalizedModelToBase`, and `\iota_U` denotes `hU.fromSpec`.
The `hom_comp_toBase` theorem is
`\iota_U\circ q_U\circ\nu_{p,U}=p|_V` over the original `X`.
The established fixed/moving ideal notation is unchanged.

The full build passes (3174 jobs), with only the two expected unchanged
Challenge placeholder warnings. `lake env lean
research/FiniteAffineChartVerification.lean` passes without warnings:
eighteen focused regressions and enforced axiom allowlists for all eleven
new declarations, permitting only `propext`, `Classical.choice` and
`Quot.sound`. The fresh SP70 rerun,
`lake env lean research/FiniteAffineCoverVerification.lean`, passes its
twenty regressions and seventeen enforced audits without warnings.
The fresh unchanged `research/ProofDependencies.lean` audit passes its
six endpoint contracts and two support reports. The central inventory
now contains 809 checks, 565 examples and 701 reports, with eleven checks
and eleven reports appended. The historical prefix is preserved
byte-for-byte; the entire historical suite was not rerun.

The single PDF build passes (72 pages, 775350 bytes), with a clean
undefined-reference, multiply-defined-label, overfull and underfull
warning scan. Final pages 7, 8, 54 and 64 pass visual inspection;
independent Lean--TeX review passes after clarifying the scalar composite
and integral closure over its image.

Normal stalks from the intended smooth geometry,
an actual global Galois refinement and marked generic extension/normal
closure data, chart gluing, and Chow--Betti generation remain separate
tasks. Next construct the canonical `K(X) -> K(Y)` for a dominant finite
morphism of integral schemes and prove finite-dimensionality from the
actual section algebra, feeding the generic extension needed for
`NormalClosureData`. Normal
stalks from smoothness remain a larger foundational task. The manuscript
gives the chart construction with its exact
hypotheses, without an editorial gap paragraph. Historical SP70 and
earlier queue blocks below are preserved unchanged.

SP70 (2026-09-18): **finite affine normalization / full-visible separation**.
The user selected finite etale covers over the whole smooth projective
base as the first geometric branch. The bounded affine implementation
starts with supplied finite normal algebras, compatible fraction fields
and marked `NormalClosureData`. It proves the canonical normalization map
is an equivalence, transports the finite models and etaleness, and builds
the existing `NormalizedCover` with the whole intermediate model visible.
It does not add a parallel cover package, ideal or projector.

For any surjective visible open, the pulled-back conjugate boundaries are
empty and their ideals top. Over perfect `K`, core-freeness gives a moved
sheet for each nontrivial subgroup; consequently `J_mov(I)=J_fm(I)=top`
and boundary separation follows directly. No Noetherian, regular-pair or
uniform-landing premise is needed for this implication.

The production witnesses are in
`Boundary/Normalization/FiniteAffineCover.lean` and
`Boundary/Normalization/FullVisibleBoundary.lean`. In the former,
`normalizationIntermediateEquiv` identifies the existing canonical
`normalizationToIntermediate`, and `intermediateNormalizationIso`
identifies the existing `intermediateToNormalization`.
`normalizedCoverOfFiniteNormalAffineModels` constructs the cover;
`conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModels`
composes its proved full visibility with the latter file's
`conjugateBoundarySeparation_of_surjective`. The constructor requires
finite normal algebras, not etaleness; `normalizedCoordinateRing_etale`
separately transports etaleness when given. All existing boundary-ideal
notation is retained. Manuscript notation: `A,S` are the actual finite
normal rings and `L,N` their chosen fraction fields;
`\nu_A:\widetilde B_L\to A` denotes `normalizationIntermediateEquiv`,
whose underlying map is the existing `normalizationToIntermediate`;
`j_A:\operatorname{Spec}A\to Y_L` denotes
`intermediateNormalizationIso.hom`, the existing
`intermediateToNormalization`. These are proved isomorphisms, not
replacement objects, and no new ideal or projector is introduced.

The full Lean build passes (3163 jobs), with only the two expected
unchanged Challenge placeholder warnings.
`lake env lean research/FiniteAffineCoverVerification.lean` passes
without warnings: twenty focused regressions and enforced standard-axiom
audits for all seventeen new declarations. The only permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`; no project axiom is added.
Its umbrella import checks public availability. The fresh unchanged
`research/ProofDependencies.lean` audit passes all six endpoint contracts
and its two supporting reports. The centralized inventory now contains
798 checks, 565 examples and 690 reports, with only seventeen checks and
seventeen reports appended. Its historical prefix is unchanged, and the
entire historical suite was not rerun.

The single PDF build passes (71 pages,
771887 bytes), with no undefined-reference, overfull or underfull
warnings. Final PDF pages 7, 10, 11, 53, 54 and 63 pass visual inspection;
independent Lean--TeX review passes, including the compatible structure
maps for `S`. A global smooth-projective
finite etale cover and Galois refinement, general etale-to-normality,
agreement across affine charts and Chow--Betti generation remain separate
geometric tasks. The main target is unchanged; the single manuscript has
matching propositions with the same hypotheses. Historical
SP69, SP68 and earlier queue blocks below are preserved unchanged.

SP69 (2026-09-18): **geometric-pair input audit / algebra controls**.
The current package supplies finite normalization models and an open
immersion; no instantiated `NormalizedCover` was found in the active
library. The [input audit](0018-geometric-pair-input-audit.md) checks the
characteristic-zero model `x=t^2`, `U=D(t)`: the visible map is etale but
the nontrivial subgroup has `J_fix=J_mov=J_fm=(t)`. This is a mathematical
example, not a Lean-formalized normalized cover or a Hodge counterexample.

`research/RegularPairGeometryControls.lean` contains research-only
commutative-algebra diagnostics. In `Q[y][x]`, `A=(x), M=(y)` admit
`f=x,g=y`; choosing `f=xy` instead admits no regular `g in M`. The
generic domain obstruction uses `a != 0`, a nonunit `b`, and the nonzero
class of `a` killed by each `g in (b)` modulo `ab`. These test ideals
are not asserted to be the fixed/moving ideals of any normalized cover.

Validation: `lake env lean research/RegularPairGeometryControls.lean`
passes without warnings. Its eight named diagnostic theorems are
`not_regular_of_mem_radical`, `not_regular_of_mem_factor`,
`constant_regular_mod_X`, `coordinate_pair_regular`,
`coordinate_sum_not_le_heightOne`, `coordinate_sum_ne_top`,
`product_choice_mem_fixed` and `product_choice_no_regular_moving`.
The enforced audits for all eight accept only `propext`,
`Classical.choice` and `Quot.sound`. A fresh `lake build` passes
(3161 jobs; only the two unchanged expected Challenge placeholder
warnings). No production declarations, library exports,
verification-inventory entries or project axioms are added. The production
inventory remains 781 checks, 565 examples and 673 reports; that unchanged
inventory was not independently rerun. The main manuscript and PDF are
unchanged and were not rebuilt for this research audit.

Associated-prime avoidance is a source/API analysis, not a newly proved
general theorem. Full-visible affine normalization would give
`J_mov(I)=top` and allow `g_I=1`, using the already proved core-free
normal-closure action; that positive subclass is not implemented or
assumed here. The next action is to choose and construct actual geometry:
a finite etale smooth-projective cover with full-visible normalization,
or a genuinely nonempty-boundary construction with independent
quotient-regularity or all-section landing input.

Scope correction for the earlier discussion: a zero moving summand
together with a proper fixed summand of codimension at least two is an
arbitrary-ideal algebra example only, not a known realized normalized
cover. Historical SP68 and earlier queue blocks below are preserved
unchanged; their validation results are not relabeled as SP69 runs.

SP68 (2026-09-18): **fixed--moving regular pairs / direct separation criterion**.
`Boundary/Normalization/HeightOneBoundaryPole.lean` refines its denominator
construction to any specified `f != 0`, without requiring `f in J`, in
`exists_heightOne_boundary_denominator_of_ne_zero`; the existing existential
statement becomes a wrapper with its public type unchanged.

`Boundary/Normalization/RegularPairBoundary.lean` proves
`not_le_heightOne_of_regularPair`: if `f,g in J`, `f != 0`, and `g` acts
injectively on the existing quotient `T/(f)`, no height-one prime contains
`J`. Otherwise
the fixed-element denominator gives `t g^n in (f)` with `t` outside the
prime; cancellation of `g^n` modulo `f` puts `t` in that prime. Only a
Noetherian domain is needed, not normality, perfectness or trace data.
The criterion allows `(f,g)=T`; it does not require a nonzero final
quotient as a full regular sequence would.

`conjugateBoundarySeparation_of_fixedMoving_regularPairs` specializes to
`0 != f_I in J_fix(I)` and `g_I in J_mov(I)` with this quotient
injectivity, for every nontrivial subgroup. Noetherian `B` and the existing
finite normalization model supply Noetherian `T`. It reuses
`J_fm(I)=J_fix(I)+J_mov(I)` and the existing separation proposition,
without a new carrier, ideal, input package or projector. Its pair premise
is explicit; no actual geometric pair or uniform trace multiplier is
constructed.

Validation: `lake build` passes (3161 jobs; only the two unchanged expected
`Challenge.lean` placeholder warnings). All ten examples in
`research/RegularPairBoundaryVerification.lean` pass without errors or
warnings, and its enforced allowlist accepts only `propext`,
`Classical.choice` and `Quot.sound` for all three new declarations.
After the denominator refactor, `research/BoundaryPoleVerification.lean`
was freshly rerun: its twelve examples and nine-declaration standard-axiom
allowlist pass without errors or warnings. The unchanged
`research/ProofDependencies.lean` was also freshly run and passes its six
primary dependency-boundary assertions and two supporting reports.

The single manuscript builds to 70 pages (767370 bytes), with a clean
final LaTeX log. Statements and transition, crosswalk, declaration inventory
and bibliography were visually checked on pages 9--11, 54, 63 and 70.
Independent Lean--TeX reviews pass; all three new names appear in the
manuscript, verification inventory and focused suite.

The historical verification inventory is preserved byte-for-byte as a
prefix, with three declaration checks and three axiom reports appended
(781 checks, 565 examples and 673 reports in the file). The appended SP68
block passes standalone with `import HodgeConjecture`, verifying all three
umbrella exports and standard-axiom reports. The full historical inventory
was not rerun. Historical SP67 and earlier validation blocks below remain
unchanged, not relabeled as new runs; the separate boundary-pole rerun is
recorded explicitly above.

Next test the sufficient criterion on identified geometry, construct
`f_I,g_I` where applicable, and prove quotient injectivity. Separated
fixed/moving witnesses are not necessary for separation; the condition
can fail when the moving ideal is zero and the proper fixed ideal already
has codimension at least two. The nonzero fixed-locus ideal alone does
not supply a compatible moving element. The generic theorem with both
elements in `J_fm(I)` and B4's independent all-section uniform landing remain
alternatives, not solved premises. The sibling landing endpoint assumes that landing,
and its finite coefficient denominator does not establish it. These are
boundary criteria, separate from Hodge-class generation and
convolution-defect vanishing.

SP67 (2026-09-18): **actual boundary poles / separation criterion**.
`Boundary/Normalization/SectionLocalization.lean` glues pointwise local
fractions into an actual section with its prescribed rational-function
image. The ideal-power criterion applies this to `z` with `J^n z <= T`
on a nonempty `V` contained in `D(J)`. It reuses the existing `eta_V`
and `R_V`; no section carrier or comparison hypothesis is introduced.

`Boundary/Normalization/HeightOneBoundaryPole.lean` constructs
`0 != f in J`, `t` outside `p`, and `t J^n <= (f)` for a height-one prime
`p` containing nonzero `J` in a Noetherian domain. The resulting `t/f`
belongs to `R_V` but not to `T`. The proof adapts the sibling's argument
to pinned dimension/prime/radical APIs without introducing a normality
assumption. Localization-denominator clearing is a private helper, not a
second public algebraic object.

`Boundary/Normalization/BoundaryPole.lean` specializes to `J_fm(I)`,
`U_I`, `eta_I` and `R_I`. Noetherianity of the base and the supplied finite
normalization model imply `R_I != T` whenever a height-one prime contains
the fixed--moving ideal. With perfect `K`, B2 gives an actual section
defeating every nonzero proposed trace multiplier, and the existing colon
`(T^vee_B:R_I)` is zero. The separation implication consumes the explicit
premise `forall I != bottom, exists s != 0, s R_I <= T^vee_B`, quantified
over all actual boundary sections. No separately supplied pole witness,
candidate ideal or replacement transporter is added.

Validation: `lake build` passes (3157 jobs; only the two unchanged expected
`Challenge.lean` placeholder warnings are reported). All twelve examples
in `research/BoundaryPoleVerification.lean` pass without errors or warnings,
and its enforced axiom allowlist verifies all nine new public declarations;
each uses only `propext`, `Classical.choice` and `Quot.sound`. The unchanged
`research/ProofDependencies.lean` was freshly run and passes its six primary
dependency-boundary assertions and two supporting reports. The single
manuscript builds to 69 pages (765141 bytes), with a clean final LaTeX log.
Propositions, section transition, crosswalk and declaration inventory were
visually checked on pages 9--11, 53 and 62. Independent final Lean--TeX
review passes; all nine names appear in the manuscript, inventory and
focused suite.

The historical verification inventory is preserved byte-for-byte as a
prefix, with nine declaration checks and nine axiom reports appended
(778 checks, 565 examples and 670 reports in the file). The appended SP67
block passes standalone with `import HodgeConjecture`, verifying all nine
umbrella exports and standard-axiom reports. The full historical inventory
was not rerun for SP67. Historical SP66 and earlier validation blocks below
remain unchanged, not relabeled as SP67 runs.

Next B4 must independently construct a nonzero geometric uniform-landing
multiplier for every nontrivial subgroup and prove landing of **every**
section. A finite coefficient denominator or a named candidate ideal
cannot substitute for this implication. The constructed pole and
conditional separation comparison are boundary results, not Hodge-class
generation or convolution-defect vanishing.

SP66 (2026-09-18): **normalization trace dual / uniform denominator**.
`Boundary/Normalization/TraceDualBound.lean` uses the existing
`Submodule.traceDual B K (1 : Submodule T N)`. The notation is
`T^vee_B = {z in N : Tr_{N/K}(zT) subset B}`; the trace-integrality base
is `B`, not `T`. An integral generic basis and its trace-dual basis bound
the entire submodule by a finite `T`-span. Clearing those basis denominators
gives one nonzero `d : T` with `d T^vee_B <= T`. This needs no
Noetherianity, normality of `B` or finite freeness of the normalization,
and does not assert `T <= T^vee_B` over a nonnormal `B`.

`Boundary/Normalization/NormalizationTraceBound.lean` specializes the
same submodule to `NormalizedCover C` as `normalizationTraceDual C`.
Finite normal closure over a perfect `K` supplies separability, and B1's
actual fraction-field comparison supplies the other denominator premise.
Under the additional Noetherian-base hypothesis, the supplied finite
normalization model and its integral-closure construction discharge B0's
Noetherianity and normality assumptions. A nonzero member of the existing
colon `(T^vee_B:R_I)` therefore forces the actual section algebra to be the
base. Conversely a proper section algebra has zero such colon. The
uniform landing formulation quantifies actual sections of `U_I`, not a
new section carrier or merely a finite coefficient family.

Validation: `lake build` passes (3154 jobs; only the unchanged expected
`Challenge.lean` placeholders are reported). All fourteen regressions in
`research/NormalizationTraceBoundVerification.lean` pass without warnings,
and its enforced axiom allowlist verifies all eleven new public declarations;
each uses only `propext`, `Classical.choice` and `Quot.sound`. The unchanged
`research/ProofDependencies.lean` passes its six primary dependency-boundary
assertions and two supporting reports. The single manuscript builds to
68 pages with no LaTeX warnings or overfull/underfull boxes. Propositions,
section transition, crosswalk and declaration inventory were visually
checked on pages 8--10, 52 and 61. Independent Lean--TeX review passes,
with module-finiteness of `T` over `B` explicit in the conditional corollary.

The historical verification inventory is preserved byte-for-byte as a
prefix, with eleven declaration checks and eleven axiom reports appended
(769 checks, 565 examples and 661 reports in the file). The appended SP66
block passes standalone with `import HodgeConjecture`, verifying the umbrella
exports, all eleven declaration checks and all eleven standard-axiom reports.
The full historical inventory was not rerun for SP66. Historical SP65
and SP64 validation blocks below remain unchanged.

B3 next examines geometric uniform landing, a pole witness and the
comparison to `ConjugateBoundarySeparation`. The new denominator and colon
consequences do not supply a nonzero geometric multiplier or prove
Hodge-class generation.

SP65 (2026-09-17): **actual sections / specified fraction field**.
`Boundary/Normalization/AffineSections.lean` constructs
`affineSectionsToFractionField` as an injective algebra map from actual
sections of a nonempty open of `Spec T`. Its range
`affineSectionSubalgebra` is algebra-equivalent to the section ring;
constants and sheaf restriction are compatible, smaller opens yield larger
subalgebras, and the full-open image is the embedded base. It uses the
existing `CommRingCat` carrier, section action and generic-stalk/function-field
objects. Normality and Noetherianity are not required.

`Boundary/Normalization/BoundarySections.lean` specializes to the existing
`NormalizedCover C` and `fixedMovingBoundaryIdeal C I`. It proves that the
existing normal-closure field `N` is the fraction field of the normalization
ring. A nontrivial subgroup has nonzero fixed-locus ideal by faithfulness
on that fraction field, making the boundary complement nonempty. The actual
section algebra then embeds into `N` and is identified with its range.
There is no new field, boundary ideal, section-comparison premise or
section-module carrier; use `boundarySectionSubalgebra.toSubmodule`.

Validation: `lake build` passes (3152 jobs; only the unchanged expected
`Challenge.lean` placeholders are reported). All sixteen examples in
`research/BoundarySectionsVerification.lean` pass without warnings, and its
enforced axiom allowlist verifies all twenty-one new public declarations;
each uses only `propext`, `Classical.choice` and `Quot.sound`.
The unchanged `research/ProofDependencies.lean` passes its six primary
dependency-boundary assertions and two supporting reports. The single
manuscript builds to 67 pages with no LaTeX warnings or overfull/underfull
boxes; propositions, section transition, crosswalk and declaration inventory
were visually checked on pages 7--9, 51 and 60. Independent Lean--TeX review
found no mathematical mismatch.

The historical verification inventory is preserved byte-for-byte as a
prefix, with twenty-one declaration checks and twenty-one axiom reports
appended (758 checks, 565 examples and 650 reports in the file). That appended
SP65 block passes standalone with `import HodgeConjecture`, verifying the
umbrella exports and all twenty-one axiom reports. The full
historical inventory was not rerun for SP65. The next bounded checkpoint is the
genuine normalization trace dual and its uniform denominator. Uniform
geometric trace landing, a boundary pole witness and the separation
comparison remain separate obligations; neither projector-defect vanishing
nor Hodge-class generation is asserted by this section embedding.

SP64 (2026-09-17): **bounded overrings / uniform landing algebra**.
The generic normal-Noetherian overring criterion is duplicated and adapted
in `Boundary/Normalization/BoundedOverring.lean`. Two consumers reuse
`Submodule.colon`: a nonzero multiplier landing an overring in a uniformly
bounded stage forces equality with the base; a proper overring consequently
has zero transporter. There is no new ideal carrier, section algebra,
trace-dual object, geometric hypothesis package, or external input instance.
The existing boundary endpoint is the intended later consumer; no artificial
proof dependency on the new module has been added to it.

Validation (2026-09-17): full build (3150 jobs), six focused examples and
an enforced standard-axiom allowlist pass. Integrated verification reaches
all 737 declaration checks, 565 examples and 629 axiom reports without an
error or unexpected axiom. The original 7002-line verification prefix is
byte-for-byte preserved; historical SP63 counts above are unchanged. The
existing six-endpoint dependency audit and two support reports pass.
The single 66-page PDF compiles without layout/reference warnings; rendered
pages 7, 8, 51 and 59 were inspected. Independent Lean/mathematical/TeX
review passes. Manuscript Proposition `prop:bounded-overring` states the
same hypotheses and both consequences, without editorial status prose.

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

SP54 checks recorded (2026-09-15): the nine-endpoint leaf and full
3132-job Lean build pass, with only the two existing `Challenge`
warnings. The six primary proof-dependency assertions and two supporting
reports pass. The independent leaf audit passes nine public axiom
reports and nine regressions; the exact-original-four-import replay
passes nine checks and sixteen regressions without warnings or errors.
Every new axiom report contains exactly `propext`, `Classical.choice`
and `Quot.sound`. The updated verification inventory is 509 axiom
reports, 617 declaration checks and 399 examples. Earlier verification
content and imports are unchanged. The focused tests cover actual
coheight and stalk parity, finite-value recovery, all three shifted
grading criteria, integer subtraction when n exceeds d, trivial
coefficients, generic and prime-divisor supports, the actual affine-line
origin and the retained integral premise. Mathematical and
cross-document parity reviews pass. The full integrated verification
passes all 617 declaration checks and 399 examples without warnings or
errors. All 509 selected axiom reports match the exact inventory, with
no missing, unexpected or duplicate reports and no unpermitted axioms.
The existing `polynomialDimensionBound` is axiom-free;
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 507 reports use exactly the standard three.
The reorganized single PDF builds to 56 pages with a clean final log,
including no undefined references, warnings or overfull/underfull boxes.
The main argument finishes on page 17; detailed foundations, split
computations and the declaration/source crosswalk follow in the same PDF.
The abstract, graph package and proof, infrastructure package, split
realization, rigidity, coverage/conclusion, new Proposition A.25, crosswalk
and source inputs were visually checked on pages 1, 9, 11, 13, 16, 17,
33, 42 and 52. All 62 pre-checkpoint labels and all 495 distinct original
literal `leanpath` strings survive; the final manuscript has 75 unique
labels and no missing references. The 46 detailed statements, including
SP54, are retained through relocation, with only a punctuation correction
after the editorial cleanup; four main-text summary/rigidity statements
bring the total to 50. Independent mathematical review confirms the
separate construction, detection, extension, action and coverage premises.
Existing sources 0A21 and 02IZ were checked for the integral numerical
formula. No source axiom, bibliography or dependency-pin change was made;
the submission wrappers are unchanged. Diff checks pass.

SP55 validation (2026-09-15): the new leaf and updated
`PrincipalRelations.lean` pass the 2804-job leaf build. The full 3133-job
Lean build passes with only the two existing `Challenge` warnings.
The six primary proof-dependency assertions and two supporting reports
pass. The independent leaf audit passes nine public axiom reports and
ten regressions without warnings or errors; all nine endpoints depend
exactly on `propext`, `Classical.choice` and `Quot.sound`.
The exact-original-four-import replay passes nine endpoint checks/reports
and sixteen new regressions without warnings or errors. Tests retain both
roundtrips, all four literal projections, the unchanged ambient generator,
generic no-field scope, generic-degree class-map injectivity, nonempty
degree d-minus-one data, and the actual Spec(k) negative-degree datum with
zero unit divisor. The earlier verification content and imports are
unchanged. The full integrated run passes all 626 declaration checks and
415 examples without warnings or errors. All 518 selected axiom reports
match the exact declaration inventory, with no missing, unexpected or
duplicate reports and no unpermitted axioms. The existing
`polynomialDimensionBound` is axiom-free;
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`;
the other 516 reports use exactly the standard three.
The single PDF builds to 57 pages with a clean final log. The main
infrastructure theorem on pages 12--13, Proposition A.26 and its proof on
page 34, and the declaration crosswalk on pages 47 and 52 were visually
checked. All nine new API names appear once each, in Appendix C; the
manuscript has 76 unique labels and no missing references. No editorial
status or gap commentary was added to the manuscript. Independent
mathematical and manuscript parity reviews pass. The existing source
conventions in 02I9, 02RW and 02QO were rechecked; no new source axiom,
bibliography entry, submission-wrapper change or dependency-pin change
was introduced. Diff checks pass.

SP56 validation (2026-09-15): all three new leaf modules and the full
3137-job Lean build pass, with only the two existing `Challenge`
warnings. The twenty public endpoints comprise seven coefficient
extension declarations, two generic scalar-extension quotient
declarations, and eleven rational principal-relation/Chow declarations.
The focused replay uses the unchanged original four imports and passes
all twenty declaration checks, twenty axiom reports and twenty new
regressions without warnings or errors. These cover arbitrary-scheme
coefficient extension without Noetherianity, signed and fundamental
cycles on the same actual supports, tensor/inverse formulas, empty and
negative degrees, unchanged actual principal generators, quotient
representatives, generic-degree vanishing, a nonflat integer-to-mod-two
scalar extension, and a genuinely nonzero torsion class killed by
rational tensoring.

The complete integrated `research/Verification.lean` passes all 646
declaration checks and 435 examples, with no warnings or errors. All 538
selected axiom reports were captured and matched against their exact
declaration inventory: no missing, unexpected or duplicate reports, and
no disallowed axiom. The twenty new reports and 516 previous reports use
exactly `propext`, `Classical.choice`, and `Quot.sound`. The existing
`polynomialDimensionBound` uses no axioms; the existing
`genericFiber_isScalarTower_base` uses `propext` and `Quot.sound` only.
The six primary proof-dependency checks and two supporting reports pass.
Independent source and mathematical/parity reviews pass.

The single PDF builds to 58 pages with a clean final log. Main-theorem
pages 12--13, Proposition A.27 and its proof on page 35, the new crosswalk
row on page 48, and additional declarations on page 53 were visually
inspected. All twenty new public endpoints occur once in the Appendix C
declaration map, with the general Chow equivalence qualified to
distinguish the older split-specific name. All 77 manuscript labels are
unique and every reference resolves. Historical SP18--SP55 validation
blocks remain byte-identical. No manuscript status/gap commentary,
project axiom, bibliography entry, submission-wrapper change or
dependency-pin change was introduced. Diff checks pass.

SP57 validation (2026-09-15): the modified graded-pushforward module,
all three new leaf modules, and the full 3140-job Lean build pass, with
only the two existing `Challenge` warnings. The twenty-one new public
endpoints comprise four coefficient-parametric graded declarations,
three coefficient/open-restriction compatibility declarations, eight
rational Chow pushforward declarations and six rational Chow isomorphism
declarations. The four existing integer graded API names retain their
signatures as specializations of the same geometric map. The focused
replay uses the unchanged original four imports and passes twenty-two
checks/axiom reports: all twenty-one new endpoints plus the previously
unreported integer `_val` theorem. All these reports use exactly
`propext`, `Classical.choice`, and `Quot.sound`.

All twenty new regressions pass without warnings or errors. They cover
semiring-parametric cycles without Noetherianity, the literal integer
specialization, actual fundamental-image supports, raw and graded cast
compatibility, inverse isomorphism open restriction, unchanged actual
principal generators, rational quotient representatives, canonical
restricted grading, identity/composition, both rationalization squares,
and the rational isomorphism's actual forward/inverse maps and tensor
comparison. No cancellation or injectivity of general Chow
rationalization is used.

The complete integrated `research/Verification.lean` passes all 668
declaration checks and 455 examples, without warnings or errors. All 560
selected axiom reports were captured and matched against their exact
inventory: no missing, unexpected or duplicate reports and no disallowed
axiom. Of these, 558 use exactly the standard three. The existing
`polynomialDimensionBound` uses no axioms, and the existing
`genericFiber_isScalarTower_base` uses only `propext` and `Quot.sound`.
The six primary proof-dependency checks and two supporting reports pass.
Independent source and mathematical/manuscript parity reviews pass.

The single PDF builds to 60 pages with a clean final log. The main
statement on page 13, Proposition A.28 and its proof on pages 35--36,
the new crosswalk row on page 50, and additional declarations on page 55
were visually inspected. All twenty-one new public APIs occur exactly
once in Appendix C; all 78 manuscript labels are unique and every
reference resolves. Historical SP18--SP56 validation blocks remain
byte-identical. No manuscript status/gap commentary, project axiom,
bibliography entry, submission-wrapper change or dependency-pin change
was introduced. Diff checks pass.

SP58 validation: both affected leaf modules compile clean, and the full
Lean build passes all 3140 jobs with only the two existing intentional
Challenge warnings. The ten new public endpoints comprise four actual
open-immersion function-field declarations and six stalk-dimension,
divisor-point and signed-order declarations. The axiom audit additionally
selects the previously unreported existing `functionFieldIso` and
`divisorPointEquiv_val`; these are not new APIs.

The focused replay with the exact original four imports passes twelve
checks/reports and twenty regressions without warnings. The regressions
cover arbitrary-scheme stalk dimensions and divisor-point embeddings,
the exact image and empty-open branch, the actual specialization and
local-algebra squares, unchanged isomorphism specializations, target-only
local Noetherianity, inverse/unit orders, and actual local coheight.
On the genuine punctured affine line, the point map is nonsurjective
but the actual function-field equivalence exists; the omitted origin is
an actual divisor point outside the embedding's image.

The full integrated `research/Verification.lean` replay passes without
warnings: 680 declaration checks, 475 examples and all 572 selected
axiom reports. The reports match their exact inventory with no missing,
unexpected or duplicate report and no disallowed axiom. Of these, 570
use exactly the standard three. The existing `polynomialDimensionBound`
uses no axioms, and `genericFiber_isScalarTower_base` uses only `propext`
and `Quot.sound`. The six primary proof-dependency checks and two
supporting reports pass. Independent source and mathematical/manuscript
parity reviews pass.

The single PDF builds to 60 pages with a clean final log. The main
statement on page 12, Proposition A.29 and its proof on pages 36--37,
the new crosswalk row on page 50 and additional declarations on page 56
were visually inspected. All ten new APIs occur exactly once in
Appendix C; all 79 manuscript labels are unique and every reference
resolves. Historical SP18--SP57 validation blocks and the pre-SP58
verification prefix remain byte-identical. No manuscript status/gap
commentary, project axiom, bibliography entry, submission-wrapper change
or dependency-pin change was introduced. Diff checks pass.

SP59 validation: the new `OpenSupport.lean` leaf passes its final
2379-job build without warnings, and the `PrincipalDivisorTransport`
consumer passes its 2385-job build without warnings. The full Lean build
passes all 3141 jobs with only the two existing intentional Challenge
warnings. The twelve new public endpoints comprise ten support/coefficient
declarations and two prime-order/principal-divisor transport declarations.
The old isomorphism restriction signature is unchanged.

The focused replay with the exact original four imports passes twelve
declaration/axiom checks and twenty regressions without warnings. The
regressions cover actual reduced closure and generic points, the
nonempty criterion, literal ideal-sheaf comap recovery, both inverse
support directions, chain codimension and divisor-point compatibility,
arbitrary-semiring coefficient evaluation, and the existing empty
generator branch. The punctured affine-line tests prove disappearance
of the actual origin cycle and principal-divisor restriction for every
nonzero rational function. Target-only finiteness hypotheses, the
unchanged isomorphism specialization, inverse functions and nonprime
zero coefficients are also checked.

The full integrated `research/Verification.lean` replay passes without
warnings: 692 declaration checks, 495 examples and all 584 selected
axiom reports. The reports match their exact inventory with no missing,
unexpected or duplicate report and no disallowed axiom. Of these, 582
use exactly the standard three. The existing `polynomialDimensionBound`
uses no axioms, and `genericFiber_isScalarTower_base` uses only `propext`
and `Quot.sound`. The six primary proof-dependency checks and two
supporting reports pass. Independent source and mathematical/manuscript
parity reviews pass.

The single PDF builds to 61 pages with a clean final log. The main
statement on page 12, Proposition A.30 and its proof on pages 37--38,
the new crosswalk row on page 51 and additional declarations on page 57
were visually inspected. All twelve new APIs occur exactly once in
Appendix C; all 80 manuscript labels are unique and every reference
resolves. Historical SP18--SP58 validation blocks and the pre-SP59
verification prefix remain byte-identical. No manuscript status/gap
commentary, project axiom, bibliography entry, submission-wrapper change
or dependency-pin change was introduced. Diff checks pass.

SP60 validation: the full `lake build` passes all 3143 jobs, with only
the two existing intentional `Challenge.lean` sorry warnings.
`OpenClosedBaseChange.lean` passes its targeted 2380-job build without
warnings, and `OpenGrading.lean` passes its 2383-job build without
warnings. The fifteen newly public endpoints comprise thirteen
open-grading declarations, the existing Cartesian inclusion equation
now exposed from `OpenSupport.lean`, and one actual finite-cycle
base-change theorem. The existing isomorphism homogeneity signature
is retained and compiles as a specialization of the general theorem.

The focused replay with the verification file's original four imports
passes all fifteen new axiom reports and twenty regressions without
warnings. The tests cover literal dimension-function values, both laws,
identity/composition, agreement with closed restriction for isomorphisms,
both support-degree formulas, negative degrees, actual homogeneous
representatives, empty sources, trivial semirings, the actual inclusion
equation without an open premise, the finite-cycle square, weighted
generators and empty restricted carriers. On the genuine proper open
`D(T)` in the affine line, every cycle pushed from the origin carrier
restricts to zero. Tests also check that no ambient integral, Noetherian
or source-compactness premise has been introduced.

The full integrated `research/Verification.lean` replay passes without
warnings: 707 declaration checks, 515 examples and all 599 selected
axiom reports. The reports match their exact inventory with no missing,
unexpected or duplicate report and no disallowed axiom. Of these, 597
use exactly the standard three. The existing `polynomialDimensionBound`
uses no axioms, and `genericFiber_isScalarTower_base` uses only `propext`
and `Quot.sound`. The six primary proof-dependency checks and two
supporting reports pass. Independent source and mathematical/manuscript
parity reviews pass.

The single PDF builds to 62 pages with a clean final log. The main
statement on page 12, Proposition A.31 and its proof on pages 38--39,
the new crosswalk row on page 52 and additional declarations on pages
57--58 were visually inspected. The Unicode iota in the newly exposed
inclusion API renders correctly while its literal Lean identifier is
preserved. All fifteen new APIs occur exactly once in Appendix C; all
81 manuscript labels are unique and every reference resolves.
Historical SP18--SP59 validation blocks and the pre-SP60 verification
prefix remain byte-identical. No manuscript status/gap commentary,
project axiom, bibliography entry, submission-wrapper change or
dependency-pin change was introduced. Diff checks pass.

SP61 validation: the full `lake build` passes all 3145 jobs, with only
the two existing intentional `Challenge.lean` sorry warnings.
`PrincipalDivisorRestriction.lean` passes its targeted 2388-job build
and `PrincipalRelationRestriction.lean` passes its 2395-job build,
both without warnings. The ten new public endpoints comprise two
actual ambient principal-divisor identities and eight declarations
for source Noetherianity, actual relation-data restriction, its literal
projections, graded generator identities, relation-span preservation
and rational-equivalence preservation.

The focused replay with the verification file's original four imports
passes all ten new axiom reports and sixteen regressions without
warnings. Tests cover both ambient identities with carrier-only
finiteness, source Noetherianity derived without integrality, relation
data without ambient finiteness, literal carrier and function projections,
the degree-one-higher condition and negative degrees, both graded
generator branches, relation-span preservation, negative multiples,
rational-equivalence preservation and unit-one data. An empty open
annihilates every relation generator. On the genuine proper open `D(T)`
in the affine line, the ambient principal divisor of every function
on the origin carrier restricts to zero. No function field or artificial
relation datum is assigned to an empty restricted carrier.

The full integrated `research/Verification.lean` replay passes without
warnings: 717 declaration checks, 531 examples and all 609 selected
axiom reports. The reports match their exact inventory with no missing,
unexpected or duplicate report and no disallowed axiom. Of these, 607
use exactly the standard three. The existing `polynomialDimensionBound`
uses no axioms, and `genericFiber_isScalarTower_base` uses only `propext`
and `Quot.sound`. The six primary proof-dependency checks and two
supporting reports pass. Independent source and mathematical/manuscript
parity reviews pass.

The single PDF builds to 64 pages with a clean final log. The main
statement on page 13, Proposition A.32 and its proof on pages 39--40,
the new crosswalk row on page 54 and additional declarations on page 59
were visually inspected. All ten new APIs occur exactly once in
Appendix C; all 82 manuscript labels are unique and every reference
resolves. Historical SP18--SP60 validation blocks and the pre-SP61
verification prefix remain byte-identical. No manuscript status/gap
commentary, project axiom, bibliography entry, submission-wrapper change
or dependency-pin change was introduced. Diff checks pass.

SP62 validation: the full `lake build` passes all 3148 jobs, with only
the two existing intentional `Challenge.lean` sorry warnings.
`ChowOpenRestriction.lean` passes its targeted 2396-job build,
`CoefficientRestriction.lean` passes its 2386-job build, and
`RationalChowOpenRestriction.lean` passes its 2402-job build, all without
warnings. The thirteen new public endpoints comprise four integral
quotient-map declarations, two raw/graded coefficient comparisons, and
seven rational relation-span, quotient-map and scalar-extension
declarations.

The focused replay with the verification file's original four imports
passes all thirteen new axiom reports and eighteen regressions without
warnings. Tests cover coefficient compatibility without ambient
finiteness, signed coefficients on actual reduced-closure supports,
literal integral/rational representatives, target-only Noetherianity,
identity and contravariant composition, principal-generator classes,
rational-span preservation and both empty-open quotient maps. The
ordinary rationalization comparison, full tensor comparison and
arbitrary pure-tensor representative formula pass. The rational map
agrees with the existing inverse scheme-isomorphism map. An explicit
generic-degree example proves that empty-open restriction is not
injective, using the existing zero relation span and a nonzero actual
fundamental cycle; no injectivity of restriction or Chow rationalization
is assumed.

The full integrated `research/Verification.lean` replay passes without
warnings: 730 declaration checks, 549 examples and all 622 selected
axiom reports. The reports match their exact inventory with no missing,
unexpected or duplicate report and no disallowed axiom. Of these, 620
use exactly the standard three. The existing `polynomialDimensionBound`
uses no axioms, and `genericFiber_isScalarTower_base` uses only `propext`
and `Quot.sound`. The six primary proof-dependency checks and two
supporting reports pass. Independent source and mathematical/manuscript
parity reviews pass.

The single PDF builds to 65 pages with a clean final log. The main
statement on page 13, Proposition A.33 and its tensor square and proof
on pages 40--41, the new crosswalk row on page 54 and additional
declarations on page 60 were visually inspected. All thirteen new APIs
occur exactly once in Appendix C; all 83 manuscript labels are unique
and every reference resolves. Historical SP18--SP61 validation blocks
and the pre-SP62 verification prefix remain byte-identical. No manuscript
status/gap commentary, project axiom, bibliography entry,
submission-wrapper change or dependency-pin change was introduced.
Diff checks pass.

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

SP64's local algebra notation is `T` for a normal Noetherian domain,
`F = Frac(T)` for the field (the Lean parameter is `N`), `R` for its
`T`-subalgebra, and `M` for a bounded `T`-submodule. Nonzero multipliers
are `a`, or `d` and `s` with `a = ds`. The existing
`M.colon R.toSubmodule` is written `(M:R)`. These are local theorem
parameters, not new canonical geometric objects; `R = ⊥` means `R = T`
under the embedding. All three new declarations are propositions, with
no separate notation. Do not identify this colon ideal with the collision
ideal, the marked residual ideal, or the correspondence idempotence defect.

SP65's generic notation is `eta_V : Gamma(V,O) -> F` for the injective
generic-germ algebra map and `R_V` for its image, on a nonempty open of
`Spec T`. Specializing to the existing normalization fixes
`T = tilde B_N`, `U_I = Spec T \\ V(J_fm(I))`, `eta_I` with codomain the
existing `N`, and `R_I = image(eta_I)`. The image is the section algebra,
not an independently supplied realization. The module in the later colon
ideal is simply `R_I.toSubmodule`.

SP66 reuses the existing trace dual, denoted
`T^vee_B = {z in N : Tr_{N/K}(zT) subset B}`. The subscript records the
base of trace-integrality; no inclusion `T <= T^vee_B` is assumed for a
nonnormal base. One nonzero `d : T` clears the entire trace dual. The
transporter from actual sections into it is the existing colon
`(T^vee_B:R_I)` with `R_I.toSubmodule`, not a newly defined ideal or
an identification with the fixed--moving boundary ideal.

SP67 adds no canonical carrier or ideal. Its local witness uses
`0 != f in J`, `t` outside `p`, `t J^n <= (f)`, and `z=t/f` on a nonempty
`V` contained in `D(J)`. In the boundary specialization the same notation
remains `U_I`, `eta_I`, `R_I` and `T^vee_B`. The nine public declarations
are propositions and receive **prose only** notation. The zero-colon
statement concerns `(T^vee_B:R_I)`, not the fixed--moving ideal itself or
the correspondence idempotence defect.

SP68 retains the existing notation `J_fix(I)`, `J_mov(I)` and `J_fm(I)`.
The local witnesses are `0 != f_I in J_fix(I)` and `g_I in J_mov(I)`,
with multiplication by `g_I` injective on the existing quotient `T/(f_I)`.
No canonical pair or new quotient carrier is defined. The three public
theorems receive **prose only** notation. The denominator refinement's
`f,t,n` have the same local meaning as SP67; its previous existential
theorem remains a wrapper, not a duplicate proof or object.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `affineSectionsToFractionField` | actual generic germ on a nonempty open of the affine spectrum, expressed in the specified fraction field | $\eta_V:\Gamma(V,\mathcal O)\hookrightarrow F$ |
| `affineSectionSubalgebra` / `affineSectionsEquivSubalgebra` | actual section image and its canonical algebra equivalence | $R_V=\operatorname{im}\eta_V$, $\Gamma(V,\mathcal O)\simeq_T R_V$ |
| `fixedMovingBoundaryOpen` | complement of the existing fixed--moving boundary ideal | $U_I=\operatorname{Spec}\widetilde B_N\setminus V(J_{\mathrm{fm}}(I))$ |
| `BoundarySectionRing` | actual structure-sheaf sections on the boundary complement | $\Gamma(U_I,\mathcal O)$ |
| `boundarySectionsToNormalClosure` | specialization of the generic-germ algebra embedding | $\eta_I:\Gamma(U_I,\mathcal O)\hookrightarrow N$ |
| `boundarySectionSubalgebra` / `boundarySectionsEquivSubalgebra` | section overring in the same normal-closure field and canonical image equivalence | $R_I=\operatorname{im}\eta_I$, $\Gamma(U_I,\mathcal O)\simeq_{\widetilde B_N}R_I$ |
| `Submodule.traceDual B K (1 : Submodule T N)` / `normalizationTraceDual C` | existing trace-dual submodule and its normalization specialization | $T^\vee_B=\{z\in N:\operatorname{Tr}_{N/K}(zT)\subseteq B\}$ |
| existing trace-dual colon of `boundarySectionSubalgebra.toSubmodule` | scalar multipliers sending every actual boundary section into the trace dual | $(T^\vee_B:R_I)$ |
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
The quotient constructed at SP40 has integer coefficients. SP56 below
constructs its rational coefficient extension using the same homogeneous
cycles and principal generators, independently of the earlier finite-split
adapter. Comparison with the prescribed target rational Chow groups
remains a separate geometric identification.

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
SP54 below identifies the integral target's codimension convention, and
SP56 constructs the rational coefficient comparison. Mixed-dimensional
components do not acquire a silently chosen global $d-p$ conversion.
Both comparisons retain the existing cycle module and actual
principal-relation construction, with no new projector or source axiom.

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

SP54 below proves the integral codimension/degree comparison and
identifies codimension \(n\) with the existing degree \(d-n\)
submodule. SP55 then reindexes the existing principal-relation data
while retaining its actual carriers and function-field units. SP56
extends the existing homogeneous cycles and Chow quotient to rational
coefficients, preserving representatives. SP57 proves naturality for the
existing closed-pushforward and isomorphism operations. SP58 supplies
integral open-immersion function-field and local-order transport. SP59
compares actual supports with nonempty open restriction and reduced
closure and proves the finite principal-cycle identity. SP60 supplies
general-open grading and Cartesian compatibility with actual closed
carrier inclusions. SP61 transports the ambient principal generator in
both nonempty and empty branches and preserves the graded relation span.
SP62 descends to the actual integral and rational Chow quotient maps,
with representative, functoriality, coefficient and tensor comparisons.
SP63 proves raw and graded cycle surjectivity via actual reduced closure,
then surjectivity of these quotient maps through their representatives.
The next bounded step is the actual closed-complement image/kernel
comparison, followed by the relation-lifting argument for localization.

### Actual integral codimension and the existing shifted grading (SP54)

Let \(X\) be integral and let \(p:X\to\operatorname{Spec}k\) be
locally of finite type over a field. Retain the existing notation
\(\delta=\delta_{X/k}\), \(d=\delta(\eta_X)\),
\(\operatorname{coht}_X(x)\), and
\(\operatorname{codim}_X W=\operatorname{codim}(|W|,X)\).
Codimension still means the actual coheight of the irreducible closed
support. It is not defined as a dimension difference.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `integral_topologicalKrullDim_eq_ofLocallyOfFiniteType` | finite actual ambient dimension from the generic structural value | $\dim X=\delta(\eta_X)=d$ in the full extended dimension type |
| `point_coheight_ne_top_of_integral_locallyOfFiniteType` | actual point coheight is finite | $\operatorname{coht}_X(x)<\infty$ |
| `point_coheight_add_dimension_of_integral_locallyOfFiniteType` | actual coheight measures the drop from the generic value | $\operatorname{coht}_X(x)+\delta(x)=d$ |
| `supportCodimension_ne_top_of_integral_locallyOfFiniteType` | the existing integral support has finite chain codimension | $\operatorname{codim}_X W<\infty$ |
| `supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType` | existing chain codimension plus existing support degree | $\operatorname{codim}_X W+\deg_\delta W=d$ |
| `supportCodimension_add_dimension_of_integral_locallyOfFiniteType` | actual carrier and ambient dimensions in the extended dimension type | $\operatorname{codim}_X W+\dim W=\dim X$ |
| `supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType` | degree detects actual codimension for every natural n | $\deg_\delta W=d-n\iff\operatorname{codim}_X W=n$ |
| `fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType` | coefficient-one homogeneity detects actual codimension | $[W]\in Z^\delta_{\mathrm{fin},d-n}(X;R)\iff\operatorname{codim}_X W=n$, for nontrivial $R$ |
| `mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType` | the existing homogeneous submodule consists of finite codimension-n cycles | $c\in Z^\delta_{\mathrm{fin},d-n}(X;R)\iff\forall W,\ c(W)\ne0\Rightarrow\operatorname{codim}_X W=n$ |

All nine endpoints are in `Cycles/IntegralCodimension.lean`.
SP53 identifies generic height with finite ambient dimension, which
bounds actual point coheight. Induction on that finite coheight uses
an actual successor of maximal available coheight; its maximality
bound proves the successor is a cover. The already constructed
dimension function's unit-step law then gives the additive formula.
No chain-length or subtraction formula is assumed as an input.
The existing support/stalk comparison identifies the same chain
codimension with the dimension of the ambient local ring at the
support's generic point. SP53's carrier comparison gives the equality
in the full extended dimension type.

The integer subtraction \(d-n\) is used for every \(n\in\mathbb N\);
no premise \(n\le d\) is added. When \(n>d\), a nonzero fundamental
cycle satisfies neither side of its displayed equivalence. The full
finite-cycle criterion works over any semiring, including trivial
coefficients; the fundamental-cycle converse retains `Nontrivial R`.
Affineness, quasi-compactness and Noetherianity are not additional
premises, but integrality of \(X\) is retained. The proof introduces
no new dimension function, codimension, carrier, cycle module or
Chow quotient.

SP55 below proves the equivalence reindexing
`PrincipalRelationData δ (d - (n + 1))` by the same actual
codimension-\(n\) carriers and function-field units, with the existing
ambient principal divisor unchanged. It also proves generic-degree
relation-data emptiness in the stronger setting of an arbitrary
integral scheme with a supplied dimension function. The relation-span
and rational-equivalence consequences retain the current Noetherian
premise. These reuse the existing principal divisors, relations and
quotient.

A reducible extension still needs actual pure-dimensional geometry or
componentwise grading; smoothness alone does not supply one uniform
dimension. SP56 supplies the general rational coefficient comparison;
target identification and realization remain separate obligations.

### Actual codimension indexing of principal relations (SP55)

For the field-geometric reindexing, retain integral \(X\), its actual
locally finite-type morphism \(p:X\to\operatorname{Spec}k\),
\(\delta=\delta_{X/k}\), and \(d=\delta(\eta_X)\).
The input is the existing `PrincipalRelationData` in degree
\(d-(n+1)\), for \(n\in\mathbb N\). Its carrier degree is
\((d-(n+1))+1=d-n\); hence it describes relations on
codimension-\(n+1\) cycles using codimension-\(n\) carriers.
For the generic-degree statements, instead let \(X\) be any integral
scheme, supply any dimension function \(\delta\), and write
\(d_\delta=\delta(\eta_X)\). No field or finite-type assumption is
part of those three statements.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `principalRelationDataEquivCodimension` | reindex the existing dependent pair by actual codimension | $(W,f)$ with $\deg_\delta W=d-n\;\longleftrightarrow\;(W,f)$ with $\operatorname{codim}_X W=n$, always $f\in k(W)^\times$ |
| `principalRelationDataEquivCodimension_apply_carrier` | forward reindexing preserves the literal integral closed carrier | prose only; the same $W$ |
| `principalRelationDataEquivCodimension_apply_function` | forward reindexing preserves the literal rational function | prose only; the same $f\in k(W)^\times$ |
| `principalRelationDataEquivCodimension_symm_apply_carrier` | inverse reindexing preserves the literal integral closed carrier | prose only; the same $W$ |
| `principalRelationDataEquivCodimension_symm_apply_function` | inverse reindexing preserves the literal rational function | prose only; the same $f\in k(W)^\times$ |
| `principalRelation_equivCodimension_symm_coe` | the reindexed generator is the existing ambient principal divisor | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^\delta_{\mathrm{fin},d-(n+1)}(X;\mathbf Z)$ |
| `isEmpty_principalRelationData_genericDegree` | generic-degree relation data would require an impossible larger carrier degree | no $(W,f)$ with $\deg_\delta W=d_\delta+1$ |
| `principalRelations_genericDegree_eq_bot` | the existing relation span vanishes in generic degree | $\mathcal R_{d_\delta}^{\delta}(X)=0$ |
| `rationallyEquivalent_genericDegree_iff_eq` | rational equivalence is equality in the existing generic-degree cycle module | $c\sim_{\mathrm{rat}}e\iff c=e$ in $Z^\delta_{\mathrm{fin},d_\delta}(X;\mathbf Z)$ |

The first six endpoints are in
`Cycles/PrincipalRelationCodimension.lean`; the last three extend the
existing `Cycles/PrincipalRelations.lean`. Manuscript Proposition A.26,
`prop:principal-relation-codimension`, records the same scope.
SP54 supplies the degree/codimension equivalence. Reindexing changes
only the proof in the carrier subtype: the carrier and its actual
function field are unchanged, both function projections are
definitionally equal, and the inverse generator's underlying cycle is
the existing ambient principal divisor by `rfl`. The index equivalence
requires no Noetherian or quasi-compact premise; forming the actual
principal relation retains `IsNoetherian X`.

For generic-degree emptiness, every carrier's ambient generic point
specializes from \(\eta_X\). Actual specialization antisymmetry
handles equality of points; strict monotonicity of the supplied
dimension function handles the strict case. Thus every carrier has
degree at most \(d_\delta\), excluding degree \(d_\delta+1\).
This argument uses neither a field nor finite type nor Noetherianity.
Under the existing Noetherian premise, the span of the empty generator
range is zero, and its rational-equivalence relation is literal equality.

The shift at \(n=0\) is different: relation data in degree \(d-1\)
include the whole integral carrier and its unit function. A negative
cycle degree alone does not imply an empty relation-data type. At
\(n=d\), the carriers have degree zero and the relation degree is
\(-1\). No new carrier type, function-field transport, dimension
function, relation operation, cycle module or Chow quotient is introduced.

SP56 below constructs rational coefficient extension of the existing
homogeneous cycles and the representative-preserving comparison
\[
 \mathbb Q\otimes_{\mathbb Z}\operatorname{CH}_m^\delta(X)
 \;\cong\;
 Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)
 \big/\operatorname{span}_{\mathbb Q}
 \{(\iota_W)_*\operatorname{div}_W(f):\deg_\delta W=m+1\}.
\]
The displayed rational generators are the coefficient extensions of the
same actual integer principal divisors. Its class maps retain their
cycle representatives, and the quotient retains the existing Noetherian
premise. General Chow rationalization is not asserted to be injective:
torsion may be killed, and the earlier finite-split injectivity theorem
is not a general comparison.

### Rational coefficient extension of the existing cycle and Chow constructions (SP56)

Keep the same actual integral closed carriers, supplied dimension
function \(\delta\), degree \(m\in\mathbb Z\), and homogeneous
cycle modules \(Z^\delta_{\mathrm{fin},m}(X;R)\). Write
\(z_{\mathbb Q}\) for the coefficientwise cast of an integer cycle.
Use \(\mathcal R_m^\delta(X;\mathbb Q)\) for the rational span of
the same actual principal generators and
\(\operatorname{CH}_m^\delta(X;\mathbb Q)\) for its quotient.
These are coefficient extensions of the existing construction, not
replacement geometric cycle or relation data.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `cyclesOfDegreeRationalize` | coefficient extension on the existing homogeneous submodule | $z\mapsto z_{\mathbb Q}:Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)\to Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)$ |
| `cyclesOfDegreeRationalize_apply` | literal coefficient cast at the same support | $z_{\mathbb Q}(W)=(z(W):\mathbb Q)$ |
| `cyclesOfDegreeRationalize_injective` | coefficient injectivity before any relation quotient | prose only; injectivity of $z\mapsto z_{\mathbb Q}$ |
| `cyclesOfDegreeRationalize_single` | the same integral support, with its coefficient cast | $a[W]\mapsto(a:\mathbb Q)[W]$ |
| `cyclesOfDegreeRationalizationEquiv` | rational homogeneous cycles are scalar extension of the integer module | $\mathbb Q\otimes_{\mathbb Z}Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)\simeq Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)$ |
| `cyclesOfDegreeRationalizationEquiv_tmul` | scalar extension preserves actual cycle representatives | $q\otimes z\mapsto qz_{\mathbb Q}$ |
| `cyclesOfDegreeRationalizationEquiv_one_tmul` | the tensor unit recovers the coefficient cast | $1\otimes z\mapsto z_{\mathbb Q}$ |
| `scalarExtensionQuotientEquiv` | universal-property quotient comparison for an existing scalar-extension model $E:S\otimes_R M\simeq N$ | $S\otimes_R(M/\langle r_i\rangle_R)\simeq N/\langle f(r_i)\rangle_S$ when $E(s\otimes m)=s f(m)$ |
| `scalarExtensionQuotientEquiv_tmul_mk` | the generic comparison retains quotient representatives | $s\otimes[m]\mapsto[s f(m)]$ |
| `rationalPrincipalRelations` | rational span of coefficient-extended actual principal divisors | $\mathcal R_m^\delta(X;\mathbb Q)=\operatorname{span}_{\mathbb Q}\{((\iota_W)_*\operatorname{div}_W(f))_{\mathbb Q}:\deg_\delta W=m+1\}$ |
| `RationalChowGroup` | rational cycles modulo that same generator prescription | $\operatorname{CH}_m^\delta(X;\mathbb Q)=Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)/\mathcal R_m^\delta(X;\mathbb Q)$ |
| `rationalClassMap` | quotient class map on rational homogeneous cycles | $z\mapsto[z]_{\mathbb Q}$ |
| `rationalClassMap_eq_zero_iff` | the actual rational relation space is the class-map kernel | $[z]_{\mathbb Q}=0\iff z\in\mathcal R_m^\delta(X;\mathbb Q)$ |
| `rationalClassMap_surjective` | every rational class has an actual finite homogeneous representative | prose only; surjectivity of $z\mapsto[z]_{\mathbb Q}$ |
| `rationalClassMap_principalRelation` | each existing principal generator vanishes after coefficient extension | $[((\iota_W)_*\operatorname{div}_W(f))_{\mathbb Q}]_{\mathbb Q}=0$ |
| `chowRationalizationEquiv` | tensor extension of the integer Chow quotient equals the rational quotient | $\mathbb Q\otimes_{\mathbb Z}\operatorname{CH}_m^\delta(X)\simeq\operatorname{CH}_m^\delta(X;\mathbb Q)$ |
| `chowRationalizationEquiv_tmul_classMap` | the Chow comparison preserves scalar-weighted representatives | $q\otimes[z]\mapsto[qz_{\mathbb Q}]_{\mathbb Q}$ |
| `chowRationalize` | canonical coefficient extension on integral Chow classes | $\operatorname{CH}_m^\delta(X)\to\operatorname{CH}_m^\delta(X;\mathbb Q)$; ordinary arrow |
| `chowRationalize_classMap` | the canonical rationalization commutes with the existing class map | $[z]\mapsto[z_{\mathbb Q}]_{\mathbb Q}$ |
| `rationalPrincipalRelations_genericDegree_eq_bot` | the rational relation span also vanishes in generic degree | $\mathcal R_{\delta(\eta_X)}^\delta(X;\mathbb Q)=0$ on integral Noetherian $X$ |

The seven coefficient endpoints are in `Cycles/CoefficientExtension.lean`,
the two generic algebraic endpoints in `Cycles/ScalarExtensionQuotient.lean`,
and the eleven rational-quotient endpoints in `Cycles/RationalChow.lean`.
Manuscript Proposition A.27, `prop:rational-chow-coefficients`, records
the same coefficient and representative comparisons.

The coefficient map is the actual integer cast on finitely supported
functions and retains the support-degree proof. Its injectivity uses
injectivity of \(\mathbb Z\to\mathbb Q\) coefficientwise. Restricting
the existing supported-module equivalence to the same set of degree-\(m\)
carriers gives the tensor comparison. No Noetherian, integral, field-base,
finite-type or finite-carrier-set hypothesis is needed; an empty or
infinite set of available carriers still gives finite-support cycles.
Neither the dimension function nor the codimension reindexing changes.

The scalar-extension quotient theorem works over arbitrary commutative
rings \(R,S\) and an \(R\)-algebra \(S\), with compatible module
actions and the displayed existing equivalence \(E\). The forward map
is a quotient lift followed by tensor extension. The inverse is the
existing \(E^{-1}\), followed by tensoring the original quotient map,
then descent through the span of the extended generators. Both inverse
laws are proved on actual representatives. No flatness assumption or
injectivity of the coefficient or quotient map is used.

The geometric rational quotient retains `IsNoetherian X` exactly where
the existing actual principal-relation map requires it. Its generator
index, carrier and rational function are those of SP40/SP55; only the
coefficients and the span's scalar ring change. Applying the generic
comparison gives the Chow tensor equivalence with its pure-tensor formula
by definitional equality. The canonical integer-to-rational Chow map
then uses \(1\otimes[z]\). It is not asserted to be injective: torsion
may be killed. The earlier finite-split Chow injectivity theorem does
not extend to this general quotient. Generic-degree vanishing is a
separate reuse of SP55 for integral Noetherian schemes with any supplied
dimension function, without a field or finite-type premise.

SP57 below proves rational closed-pushforward and isomorphism naturality
for those existing operations. It preserves the actual cycle and class
representatives and compares the descended maps with tensoring the
integral Chow maps, without cancelling the potentially noninjective
integer-to-rational Chow map.

### Rational closed pushforward and isomorphism naturality (SP57)

Let \(i:X\hookrightarrow Y\) be an actual closed immersion, supply
dimension functions \(\delta_X,\delta_Y\), and assume the same
support-degree comparison used by the integer pushforward:
\[
 \deg_{\delta_Y}(i(W))=\deg_{\delta_X}(W)
 \qquad(W\in\operatorname{IntSub}(X)).
\]
Here \(i(W)\) is the already constructed actual closed image, not a
replacement support. For \(\delta_X=i^*\delta_Y\), the existing
restricted dimension function proves this equality. The cycle layer
works over any coefficient semiring \(R\); the rational relation and
Chow layers retain `IsNoetherian X` and `IsNoetherian Y`.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `gradedClosedImmersionPushforwardWithCoefficients` | the existing geometric pushforward restricted to homogeneous cycles over any semiring | $i_{*,\mathrm{cyc}}:Z^{\delta_X}_{\mathrm{fin},m}(X;R)\to Z^{\delta_Y}_{\mathrm{fin},m}(Y;R)$ |
| `gradedClosedImmersionPushforwardWithCoefficients_val` | its underlying finite cycle is the existing actual closed pushforward | prose only; the same $i_{*,\mathrm{cyc}}z$ |
| `gradedClosedImmersionPushforwardWithCoefficients_id` | graded identity over any coefficient semiring | $(\mathrm{id}_X)_{*,\mathrm{cyc}}=\mathrm{id}$ |
| `gradedClosedImmersionPushforwardWithCoefficients_comp` | graded composition is the existing geometric composition | $j_{*,\mathrm{cyc}}i_{*,\mathrm{cyc}}=(j\circ i)_{*,\mathrm{cyc}}$ |
| `closedImmersionPushforward_rationalize` | actual ungraded closed pushforward commutes with coefficient cast | $i_{*,\mathrm{cyc}}(z_{\mathbb Q})=(i_{*,\mathrm{cyc}}z)_{\mathbb Q}$ |
| `gradedClosedImmersionPushforward_rationalize` | the same coefficient square on the existing homogeneous submodules | prose only; the preceding equality in degree $m$ |
| `openRestriction_iso_mem_cyclesOfDegree` | actual open restriction along an isomorphism has the canonical restricted degree | $e^*z\in Z^{e^*\delta}_{\mathrm{fin},m}(X;R)$ for $z\in Z^\delta_{\mathrm{fin},m}(Y;R)$ |
| `rationalPrincipalRelations_le_comap_closedImmersionPushforward` | preservation of the rational span of the same actual principal generators | $i_{*,\mathrm{cyc}}\mathcal R_m^{\delta_X}(X;\mathbb Q)\subseteq\mathcal R_m^{\delta_Y}(Y;\mathbb Q)$ |
| `rationalChowClosedImmersionPushforward` | descent of actual closed pushforward to the rational quotient | $i_*:\operatorname{CH}_m^{\delta_X}(X;\mathbb Q)\to\operatorname{CH}_m^{\delta_Y}(Y;\mathbb Q)$ |
| `rationalChowClosedImmersionPushforward_classMap` | the quotient map preserves the actual cycle formula | $i_*[z]_{\mathbb Q}=[i_{*,\mathrm{cyc}}z]_{\mathbb Q}$ |
| `rationalChowClosedImmersionPushforward_restricted_classMap` | canonical dimension restriction supplies the support-degree premise | prose only; the same formula for $\delta_X=i^*\delta_Y$ |
| `rationalChowClosedImmersionPushforward_id` | rational quotient identity | $(\mathrm{id}_X)_*=\mathrm{id}$ |
| `rationalChowClosedImmersionPushforward_comp` | rational quotient composition | $j_*i_*=(j\circ i)_*$ |
| `rationalChowClosedImmersionPushforward_chowRationalize` | the integral-to-rational class map commutes with actual pushforward | prose only; the coefficient-extension square for $i_*$ |
| `rationalChowClosedImmersionPushforward_chowRationalizationEquiv` | the descended rational map is the scalar extension of integral Chow pushforward | prose only; the tensor-comparison square with $1\otimes i_*$ |
| `rationalChowIsoEquiv` | scalar extension of the existing integral Chow isomorphism in the actual rational quotient models | $e_*:\operatorname{CH}_m^{e^*\delta}(X;\mathbb Q)\xrightarrow{\sim}\operatorname{CH}_m^\delta(Y;\mathbb Q)$ |
| `rationalChowIsoEquiv_chowRationalizationEquiv` | the rational isomorphism agrees with tensoring the existing integral isomorphism | prose only; the same tensor-comparison square |
| `rationalChowIsoEquiv_toLinearMap` | its forward map is the already descended rational closed pushforward | prose only; the same $e_*$ |
| `rationalChowIsoEquiv_classMap` | forward isomorphism preserves actual closed-image representatives | $e_*[z]_{\mathbb Q}=[e_{*,\mathrm{cyc}}z]_{\mathbb Q}$ |
| `rationalChowIsoEquiv_symm_classMap` | inverse isomorphism is actual open restriction on representatives | $e_*^{-1}[z]_{\mathbb Q}=[e^*z]_{\mathbb Q}$ |
| `rationalChowIsoEquiv_chowRationalize` | rationalization commutes with the existing integral Chow isomorphism | prose only; the corresponding class-map square |

The four coefficient-parametric endpoints extend
`Cycles/GradedPushforward.lean`. Its four integer API names keep their
existing signatures as definitional specializations at \(R=\mathbb Z\);
there is only one geometric graded pushforward. The three compatibility
endpoints are in `Cycles/CoefficientPushforward.lean`, the eight rational
closed-pushforward endpoints in `Cycles/RationalChowPushforward.lean`,
and the six rational isomorphism endpoints in
`Cycles/RationalChowIsomorphism.lean`. Manuscript Proposition A.28,
`prop:rational-chow-naturality`, states the same scope and representative
formulas.

The cycle proof uses the existing actual closed-image generator formula
and finite-support linearity. Neither it nor the isomorphism
open-restriction membership proof requires Noetherianity, integrality,
a field base, finite type or a finite set of available supports. The
isomorphism proof uses actual open restriction as closed pushforward
along the inverse scheme isomorphism; the closed-image equivalence
supplies the support-degree equality. Identity and composition therefore
remain the same geometric operations over every semiring, including
trivial coefficients.

For the rational quotient, the integral principal-generator image
identity and coefficient square show that each generator lands in the
target rational relation span. Span preservation then gives quotient
descent. No extra relation-preservation hypothesis is supplied. The
class-map formula is definitional, and identity/composition follow from
the already proved cycle formulas. Naturality with the full tensor
comparison is checked on scalar-weighted class representatives. The
rational isomorphism is constructed by conjugating the scalar extension
of the existing integral Chow equivalence through the two tensor
comparisons. Its actual closed-pushforward formula follows from the
tensor square, and its inverse formula follows from actual inverse
closed pushforward/open restriction. These arguments use equivalences
and quotient representatives; they do not cancel `chowRationalize` or
assert its injectivity. No new carrier, dimension function, relation
prescription or Chow quotient is introduced.

SP58 below generalizes the same actual function-field construction to
integral open immersions, proves its local-stalk compatibility, and
transports divisor points and signed local orders. SP59 supplies the
support and finite principal-cycle comparisons built from those pointwise
results; ambient carrier compatibility and open relation descent remain
separate.

### Actual function fields and local orders under open immersions (SP58)

Let \(j:X\hookrightarrow Y\) be an actual open immersion. The
stalk-dimension and divisor-point assertions apply to arbitrary schemes.
The function-field assertions retain integral \(X\) and \(Y\),
so the source is a nonempty open. The signed-order assertion additionally
requires only that \(Y\) be locally Noetherian; the source's local
Noetherianity is explicitly derived from \(j\).

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `functionFieldIsoOfOpenImmersion` | the actual generic-stalk isomorphism induced by the open immersion | $j^*:k(Y)\xrightarrow{\sim}k(X)$ |
| `functionFieldEquivOfOpenImmersion` | the same map as a ring equivalence, not another field construction | prose only; the same $j^*$ |
| `functionFieldIsoOfOpenImmersion_stalkSpecializes` | the actual generic-stalk map commutes with specialization from each local stalk | prose only; the local-to-generic stalk square |
| `functionFieldEquivOfOpenImmersion_algebraMap` | the same square for the canonical local-ring algebra maps | $j^*(a)=j_x^{\#}(a)$ after the canonical maps into $k(X)$, for $a\in\mathcal O_{Y,j(x)}$ |
| `stalkDimension_openImmersion` | actual local-ring isomorphism preserves Krull dimension | $\dim\mathcal O_{Y,j(x)}=\dim\mathcal O_{X,x}$ |
| `divisorPointEmbedding` | the actual point map embeds the one-dimensional local-ring locus | $j_1:\operatorname{DivPt}(X)\hookrightarrow\operatorname{DivPt}(Y)$ |
| `divisorPointEmbedding_val` | the embedded divisor point has the unchanged actual point image | $j_1(x)=j(x)$ on underlying points |
| `mem_range_divisorPointEmbedding_iff` | exact range of the divisor-point embedding | $y\in\operatorname{im}(j_1)\iff y\in j(X)$ for $y\in\operatorname{DivPt}(Y)$ |
| `divisorPointEmbedding_iso` | the old isomorphism point equivalence has this same forward map | prose only; $j_1=e_1$ when $j=e.\mathrm{hom}$, by definitional equality |
| `divisorOrder_openImmersion` | the same signed local order is preserved through the actual field/stalk maps | $\operatorname{ord}_x(j^*f)=\operatorname{ord}_{j_1(x)}(f)$ |

The four function-field endpoints generalize
`Cycles/FunctionFieldTransport.lean`; the six local endpoints extend
`Cycles/SchemeLocalOrder.lean`. Manuscript Proposition A.29,
`prop:open-function-field-order`, states these same separate hypothesis
levels. The four old function-field API signatures are unchanged and
definitionally specialize the open-immersion construction at
\(j=e.\mathrm{hom}\). The old `stalkDimension_iso` and
`divisorOrder_iso` proofs likewise specialize the new results. The
existing `divisorPointEquiv` remains an equivalence for scheme
isomorphisms, with forward compatibility proved by `rfl`; arbitrary
open immersions give only an embedding with the stated exact range.

The actual open stalk map is an isomorphism at every point. At the
generic point, its source is identified with the target scheme's generic
stalk using the proved generic-point image equality. Naturality of
stalk specialization gives the local-ring/function-field square without
introducing a transported substitute algebra action. The same local
stalk isomorphism gives the dimension equality; actual injectivity on
points gives the divisor-point embedding, and any target divisor point
in the open image pulls back to a one-dimensional stalk. These local
dimension and point assertions need neither integrality nor
Noetherianity.

For signed order, local Noetherianity of \(X\) is derived from the
target by an explicit `letI` in the theorem statement and proof. The
existing length-based fraction-field order comparison is applied to
the actual stalk ring equivalence and actual function-field equivalence,
using their proved algebra-map compatibility. No compactness, finite-type,
base-field, normality or DVR assumption is introduced. Neither the order
function nor the divisor-point type is replaced, and no principal-cycle
or Chow-relation restriction identity is asserted here.

SP59 below proves the actual support comparison, finite-cycle coefficient
formula and principal-divisor restriction identity. The existing
empty-generator branch remains zero. SP60 and SP61 supply graded ambient
principal-relation preservation, and SP62 descends the same operation to
the existing integral and rational Chow quotients.

### Actual open supports and finite principal-divisor restriction (SP59)

Let \(j:U\hookrightarrow X\) be an open immersion. For an actual
integral closed support \(W\subset U\), write
\(\overline{j(W)}_{\mathrm{red}}\) for the existing reduced point
closure at \(j(\xi_W)\). For an ambient integral support \(Z\),
its restricted ideal sheaf is the literal comap along \(j\). When its
subscheme is nonempty it is the existing integral support
`openRestrictionSubscheme j Z`. These are constructions on the original
ideal-sheaf generators, not replacement cycle indices.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `openClosureSubscheme` | reduced ambient closure through the existing point/support construction | $\overline{j(W)}_{\mathrm{red}}=\operatorname{pointSupport}_X(j(\xi_W))$ |
| `openClosureSubscheme_ambientGenericPoint` | its literal ambient generic point | $\xi_{\overline{j(W)}_{\mathrm{red}}}=j(\xi_W)$ |
| `ambientGenericPoint_openRestrictionSubscheme` | the nonempty restricted carrier has the same ambient generic point | $j(\xi_{Z\cap U})=\xi_Z$ |
| `nonempty_openRestrictionSubscheme_iff` | exact criterion for a carrier to meet the open | $Z\cap U\ne\varnothing\iff\xi_Z\in j(U)$ |
| `openClosureSubscheme_comap` | restriction recovers the actual original ideal sheaf | $j^*\mathcal I_{\overline{j(W)}_{\mathrm{red}}}=\mathcal I_W$ |
| `openClosureSubscheme_openRestrictionSubscheme` | ambient reduced closure recovers each carrier meeting the open | $\overline{j(Z\cap U)}_{\mathrm{red}}=Z$ when $Z\cap U\ne\varnothing$ |
| `supportCodimension_openClosureSubscheme` | preservation of actual chain codimension under reduced ambient closure | $\operatorname{codim}_X\overline{j(W)}_{\mathrm{red}}=\operatorname{codim}_U W$ |
| `supportCodimension_openRestrictionSubscheme` | preservation of chain codimension under nonempty open restriction | $\operatorname{codim}_U(Z\cap U)=\operatorname{codim}_X Z$ |
| `openClosureSubscheme_divisorPoint` | on prime supports, reduced closure agrees with the existing divisor-point embedding | prose only; the same $j_1$ through the point/prime-support equivalences |
| `openRestriction_apply` | exact coefficient formula for the existing finite-cycle restriction | $(j^*c)(W)=c(\overline{j(W)}_{\mathrm{red}})$ |
| `primeDivisorOrder_openImmersion` | signed local orders agree on the corresponding actual prime supports | $\operatorname{ord}_W(j^*f)=\operatorname{ord}_{\overline{j(W)}_{\mathrm{red}}}(f)$ |
| `openRestriction_principalDivisor_of_isOpenImmersion` | the existing finite principal divisor commutes with actual open restriction | $j^*\operatorname{div}_X(f)=\operatorname{div}_U(j^*f)$ |

The first ten endpoints are in `Cycles/OpenSupport.lean`; the last two
extend `Cycles/PrincipalDivisorTransport.lean`. Manuscript Proposition
A.30, `prop:open-principal-divisor`, retains the same distinct hypothesis
levels and representative formulas. The old isomorphism specialization
`openRestriction_principalDivisor` keeps its signature and now applies
the general open-immersion result. There is no second principal-divisor
operation.

The Cartesian ideal-comap comparison supplies the actual open morphism
from the restricted support to the original carrier. Its generic-point
image and inclusion equation prove the ambient generic-point identity.
Conversely a preimage of the ambient generic point is an actual point of
the restricted subscheme. The existing point/support equivalence then
proves both support inverse identities, including equality of the actual
ideal sheaves, not merely equality of their underlying sets. The
generic-stalk dimension comparison proves chain-codimension preservation;
no absolute dimension subtraction or global dimension preservation is
claimed. Compatibility with the divisor-point embedding is on the same
point and support data.

The support results and the coefficient formula require no ambient
integrality, Noetherianity, quasi-compactness, normality or field base.
The closure definition and its generic-point identity in fact work for
any scheme morphism; the inverse, codimension and cycle formulas use
the open-immersion premise. The coefficient formula holds over any
semiring, including trivial coefficients, by finite-support linearity.
If an ambient generator misses the open, its existing restriction is
zero. No open immersion is treated as a closed immersion, and no general
closed-image pushforward is applied to it.

The prime-support order comparison additionally assumes integral
\(U,X\) and local Noetherianity of \(X\). Local Noetherianity on
\(U\) is derived explicitly. For the finite principal-cycle identity,
retain quasi-compactness of \(X\). Local Noetherianity makes the open
immersion quasi-compact, so source compactness is derived from the
target; compactness alone is not used to justify compactness of an
arbitrary open. The proof compares coefficients in the unchanged finite
cycle module: prime supports use the order identity, while nonprime
supports have zero coefficient on both sides by the codimension
comparison. Integral \(U\) is nonempty; the empty restriction of an
individual ambient carrier remains the separate zero branch.

SP60 below constructs restriction of an arbitrary supplied dimension
function and proves preservation of the existing homogeneous cycle
submodules. It also proves the actual open/closed carrier cycle square,
including the empty inverse-image case. SP61 uses that square for the
ambient principal-generator identity and relation-span preservation;
SP62 supplies the resulting integral and rational quotient maps, with
their representative and scalar-extension comparisons.

### Open grading and the actual closed-carrier cycle square (SP60)

Let \(j:U\hookrightarrow X\) be an open immersion, supply the existing
dimension-function object \(\delta:X\to\mathbb Z\), and write
\(\delta_U=\delta\circ j\). For an actual integral closed carrier
\(Z\subseteq X\), let \(Z_U\) denote the subscheme of the actual
comapped ideal; its existing canonical comparison identifies it with
\(Z\times_X U\). Write \(j_Z:Z_U\to Z\) for the actual open
support map and \(\iota_{Z_U}:Z_U\hookrightarrow U\) for the closed
inclusion. The carrier \(Z_U\) may be empty.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `openImmersion_covBy` | actual open point maps preserve immediate specialization | $x\mathbin{\lessdot}y\Rightarrow j(x)\mathbin{\lessdot}j(y)$ in the scheme specialization orders |
| `DimensionFunction.comapOpenImmersion` | literal composition with the actual open point map, with both dimension-function laws proved | $\delta_U=\delta\circ j$ |
| `DimensionFunction.comapOpenImmersion_apply` | unchanged pointwise values under the restriction constructor | $\delta_U(x)=\delta(j(x))$ |
| `DimensionFunction.comapOpenImmersion_id` | identity restriction of the supplied dimension function | $\delta\circ\mathrm{id}=\delta$ as dimension-function objects |
| `DimensionFunction.comapOpenImmersion_comp` | composition of actual restrictions | $(\delta\circ j)\circ k=\delta\circ(j\circ k)$ |
| `DimensionFunction.comapOpenImmersion_eq_comapClosedImmersion` | open and closed restriction constructors agree when both apply | prose only; the same restricted $\delta$ for an open-and-closed immersion |
| `supportDegree_openClosureSubscheme` | actual reduced closure preserves the corresponding support degree | $\deg_\delta\overline{j(W)}_{\mathrm{red}}=\deg_{\delta_U}W$ |
| `supportDegree_openRestrictionSubscheme` | a nonempty restricted integral carrier retains its degree | $\deg_{\delta_U}(Z_U)=\deg_\delta Z$ when $Z_U\ne\varnothing$ |
| `openRestriction_mem_cyclesOfDegree` | the already defined finite-cycle restriction preserves homogeneity | $j^*Z^\delta_{\mathrm{fin},m}(X;R)\subseteq Z^{\delta_U}_{\mathrm{fin},m}(U;R)$ |
| `gradedOpenRestriction` | restriction of that same geometric cycle map to the existing degree submodules | $j^*:Z^\delta_{\mathrm{fin},m}(X;R)\to Z^{\delta_U}_{\mathrm{fin},m}(U;R)$ |
| `gradedOpenRestriction_val` | the underlying finite cycle is unchanged by homogeneous packaging | prose only; the existing $j^*c$ |
| `gradedOpenRestriction_id` | identity on the same homogeneous representatives | $(\mathrm{id}_X)^*=\mathrm{id}$ |
| `gradedOpenRestriction_comp` | contravariant composition of the same graded restriction | $(j\circ k)^*=k^*j^*$ |
| `openRestrictionSubschemeMap_subschemeι` | the existing actual carrier maps commute with their closed inclusions | $\iota_Z\circ j_Z=j\circ\iota_{Z_U}$ |
| `openRestriction_closedImmersionPushforward_subscheme` | the actual Cartesian square commutes on all finite cycles | $j^*(\iota_Z)_*=(\iota_{Z_U})_*j_Z^*:Z_{\mathrm{fin}}(Z;R)\to Z_{\mathrm{fin}}(U;R)$ |

The thirteen grading endpoints are in `Cycles/OpenGrading.lean`. The
Cartesian inclusion equation is the existing proof in
`Cycles/OpenSupport.lean`, now public rather than duplicated. The full
cycle square is in `Cycles/OpenClosedBaseChange.lean`. Manuscript
Proposition A.31, `prop:open-grading-base-change`, records the same
grading and actual carrier square. The previous
`openRestriction_iso_mem_cyclesOfDegree` signature continues to use the
closed-restricted dimension function; its proof now specializes the
general open theorem, using the definitional equality of the two
restriction constructions.

The actual open point map reflects specialization and has image stable
under generization. Its image is therefore order-convex, and an immediate
specialization inside the open stays immediate in the ambient scheme.
This proves both strict monotonicity and the unit-step law for literal
composition with \(j\); neither is supplied as a new hypothesis. No
existence of an arbitrary ambient dimension function is asserted: the
existing \(\delta\) is explicitly supplied. The support-degree identities
follow from the actual generic-point formulas, and the reduced-closure
coefficient formula then proves homogeneous membership. Identity and
composition use the existing finite-cycle restriction laws and
definitionally compatible restricted dimension functions.

For the carrier square, the existing ideal-comap comparison and the
fiber-product point-image formula show that each integral generator in
\(Z\) has nonempty inverse image exactly when its actual closed image
in \(X\) does. In the nonempty case, the Cartesian inclusion equation
and generic-point identities identify the two actual integral supports;
the point/support equivalence gives equality of their ideal-sheaf
generators. In the empty case both cycle images are zero. Finite-support
linearity proves the full semiring-linear square. It does not treat the
open immersion as a closed pushforward or introduce a new pullback
carrier model. The inclusion equation itself holds for any scheme
morphism \(j\); the cycle square requires \(j\) open.

All the new assertions allow arbitrary ambient schemes, without
Noetherianity, quasi-compactness, ambient integrality, normality or a
field base. The cycle assertions work over every semiring, including
trivial coefficients. The carrier-square API retains its actual
`IntegralClosedSubscheme X` input; it does not assert a general
arbitrary-ideal base-change theorem. No nonemptiness premise on
\(Z_U\), relation prescription or Chow map is introduced.

SP61 below applies the actual square to `ambientPrincipalDivisor`,
retaining the nonempty function-field branch and the empty zero branch.
It transports the graded generator and proves relation-span preservation.
SP62 then defines the existing integer and rational Chow quotients' open
restriction maps from those proved identities.

### Ambient principal-generator restriction and relation preservation (SP61)

Let \(j:U\hookrightarrow X\) be an open immersion. For an actual
integral closed carrier \(W\subseteq X\), retain the actual comapped
carrier \(W_U\), its open morphism \(j_W:W_U\to W\), and its
closed inclusion into \(U\). The raw ambient principal-divisor
identities assume only local Noetherianity and quasi-compactness of
\(W\), not of \(U\) or \(X\). For relation data, supply the existing
dimension function \(\delta\), write \(\delta_U=\delta\circ j\),
and retain degree \(m\in\mathbb Z\). The additional `IsNoetherian X`
premise is used only at the existing graded principal-relation and
relation-span layer, where Noetherianity of \(U\) is proved from it.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `openRestriction_ambientPrincipalDivisor_of_nonempty` | the actual ambient principal divisor restricts to the actual nonempty carrier's principal divisor | $j^*((\iota_W)_*\operatorname{div}_W(f))=(\iota_{W_U})_*\operatorname{div}_{W_U}(j_W^*f)$ |
| `openRestriction_ambientPrincipalDivisor_of_isEmpty` | an empty inverse-image carrier contributes zero | $j^*((\iota_W)_*\operatorname{div}_W(f))=0$ when $W_U=\varnothing$ |
| `openImmersion_isNoetherian` | derive source Noetherianity from the actual open immersion and target Noetherianity | prose only; $X$ Noetherian implies $U$ Noetherian |
| `PrincipalRelationData.openRestriction` | restrict the existing degree-one-higher datum on a nonempty carrier, with no Noetherian premise | $(W,f)\mapsto(W_U,j_W^*f)$ with $\deg_{\delta_U}W_U=m+1$ |
| `PrincipalRelationData.openRestriction_carrier` | retain the literal ideal-comap integral carrier | prose only; the same $W_U$ |
| `PrincipalRelationData.openRestriction_function` | retain the actual forward contravariant function-field map | prose only; the literal $j_W^*f\in k(W_U)^\times$ |
| `gradedOpenRestriction_principalRelation_of_nonempty` | the existing graded map sends the nonempty generator to its actual restricted generator | prose only; the preceding nonempty ambient principal-divisor identity inside the degree-$m$ homogeneous module |
| `gradedOpenRestriction_principalRelation_of_isEmpty` | the empty carrier gives the zero homogeneous cycle | prose only; the preceding empty ambient principal-divisor identity inside the degree-$m$ homogeneous module |
| `principalRelations_le_comap_openRestriction` | preservation of the span is a consequence of the proved generator identities | $j^*\mathcal R_m^\delta(X)\subseteq\mathcal R_m^{\delta_U}(U)$ |
| `rationallyEquivalent_openRestriction` | the existing rational-equivalence predicate on integral cycles is preserved | $c\sim_{\mathrm{rat}}e\Rightarrow j^*c\sim_{\mathrm{rat}}j^*e$ for $c,e\in Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)$ |

The two ambient identities are in
`Cycles/PrincipalDivisorRestriction.lean`; the eight remaining endpoints
are in `Cycles/PrincipalRelationRestriction.lean`. Manuscript Proposition
A.32, `prop:open-principal-relations`, retains these same hypothesis
levels. All generators, carriers, function fields, dimension functions
and finite-cycle modules are the existing objects. The quotient maps are
constructed separately in SP62 below from this relation-span preservation.

For the nonempty ambient identity, apply SP60's actual cycle square to
the principal divisor on \(W\), then SP59's principal-divisor identity
to \(j_W\). The restricted integral carrier is literally the subscheme
of the comapped ideal, so its function field needs no comparison with a
replacement carrier. Its integrality, local Noetherianity and compactness
are installed explicitly from the existing carrier construction and
actual open map. The function is the forward `Units.map` of the actual
contravariant function-field equivalence. In the empty branch, there are
no integral closed supports on the empty carrier and its finite-cycle
module is zero. No function field or principal-relation datum is assigned
to that empty scheme.

For a nonempty relation datum, the already proved support-degree formula
retains degree \(m+1\). Both its carrier and function projections are
definitionally the announced actual constructions; this dependent-pair
operation needs no Noetherian or compactness premise. When \(X\) is
Noetherian, the existing closed-carrier inheritance supplies the
principal-divisor finiteness hypotheses. The actual open map supplies
source local Noetherianity and compactness, packaged as the proved
`openImmersion_isNoetherian` theorem, not a new assumption or global
instance. Passing to the existing homogeneous subtypes turns the two
ambient equalities into graded generator equalities.

The relation-span proof tests each original principal generator and
splits on nonemptiness of its actual inverse image. The nonempty image
is an existing target generator, and the empty image is zero. Linear
span preservation therefore follows without a relation-preservation
input. Applying it to \(c-e\) proves preservation of the existing
rational-equivalence predicate. Here rational equivalence still concerns
integer cycles. SP62 extends this proved compatibility to the
rational-coefficient relation span and quotient.

### Integral and rational Chow open restriction (SP62)

Retain the actual open immersion \(j:U\hookrightarrow X\), the
supplied dimension function \(\delta\), its literal restriction
\(\delta_U=\delta\circ j\), and the existing homogeneous degree
\(m\in\mathbb Z\). Write \(z_{\mathbf Q}\) for the existing
coefficient extension and \([z]\) for the existing quotient class.
Both quotient maps use the same \(j^*\) notation as the cycle operation;
their domains and coefficient types distinguish them.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `chowOpenRestriction` | descend the actual graded integral cycle map using the proved relation-span inclusion | $j^*:\operatorname{CH}_m^\delta(X)\to\operatorname{CH}_m^{\delta_U}(U)$ |
| `chowOpenRestriction_classMap` | preserve the actual integral cycle representative | $j^*[z]=[j^*z]$ |
| `chowOpenRestriction_id` | the identity immersion induces the identity on the existing quotient | $\operatorname{id}^*=\operatorname{id}$ |
| `chowOpenRestriction_comp` | preserve contravariant composition with the literal composed dimension function | $(j\circ i)^*=i^*\circ j^*$ |
| `openRestriction_rationalize` | coefficient extension commutes with the existing finite-cycle operation | $j^*(z_{\mathbf Q})=(j^*z)_{\mathbf Q}$ |
| `gradedOpenRestriction_rationalize` | the same coefficient equality in the existing homogeneous submodules | prose only; the preceding identity in degree $m$ |
| `rationalPrincipalRelations_le_comap_openRestriction` | preserve the rational span of the same actual principal generators | $j^*\mathcal R_m^\delta(X;\mathbf Q)\subseteq\mathcal R_m^{\delta_U}(U;\mathbf Q)$ |
| `rationalChowOpenRestriction` | descend the actual rational cycle restriction to the existing quotient | $j^*:\operatorname{CH}_m^\delta(X;\mathbf Q)\to\operatorname{CH}_m^{\delta_U}(U;\mathbf Q)$ |
| `rationalChowOpenRestriction_classMap` | preserve the actual rational cycle representative | $j^*[z]=[j^*z]$ for rational $z$ |
| `rationalChowOpenRestriction_id` | retain the identity on the rational quotient | $\operatorname{id}^*=\operatorname{id}$ |
| `rationalChowOpenRestriction_comp` | retain contravariant composition on the rational quotient | $(j\circ i)^*=i^*\circ j^*$ |
| `rationalChowOpenRestriction_chowRationalize` | commute with the existing integral-to-rational Chow class map | $j^*(c_{\mathbf Q})=(j^*c)_{\mathbf Q}$ for integral Chow classes $c$ |
| `rationalChowOpenRestriction_chowRationalizationEquiv` | identify the rational quotient map with scalar extension of the integral map on all tensors | prose only; the full square under the existing comparisons $q\otimes[z]\mapsto[qz_{\mathbf Q}]$ |

The four integral endpoints are in `Cycles/ChowOpenRestriction.lean`,
the two coefficient endpoints in `Cycles/CoefficientRestriction.lean`,
and the seven rational endpoints in
`Cycles/RationalChowOpenRestriction.lean`. Manuscript Proposition A.33,
`prop:open-chow-restriction`, uses the same objects, hypotheses and
representative formulas. The coefficient comparisons require no
Noetherianity, integrality, quasi-compactness or field base on the ambient
schemes. The quotient assertions assume only `IsNoetherian X`;
Noetherianity of the open source and every intermediate open is derived
explicitly by `openImmersion_isNoetherian`, not added as a separate
premise or global instance.

The reduced-closure coefficient formula proves raw coefficient
compatibility directly, and restriction to the existing homogeneous
submodules proves its graded form. SP61's actual relation-span inclusion
then gives the integral quotient map by the quotient universal property.
For the rational span, coefficient compatibility sends a cast principal
generator to the cast of its actual nonempty restricted generator, or
to zero when its carrier misses the open. The rational quotient map is
therefore induced by the same geometric cycle operation. Neither map
uses an assumed relation-preservation or descent hypothesis.

The representative formulas are definitional. Quotient extensionality
reduces identity and composition to the existing graded cycle identities,
with definitionally compatible dimension functions. Integral class-map
surjectivity reduces the ordinary rationalization comparison to its
cycle coefficient identity. Tensor induction and actual cycle
representatives prove the full tensor square, not just its tensor-one
part. No injectivity of general Chow rationalization is asserted or used;
torsion may be killed by coefficient extension. No new Chow quotient,
cycle carrier, dimension function or independent comparison symbol is
introduced.

SP63 below proves surjectivity of the existing raw and graded cycle
restrictions by extending each actual integral support to its reduced
ambient closure and preserving its degree. Surjectivity of the integral
and rational Chow restriction maps follows through their representative
formulas. The actual closed-complement image/kernel identification and
localization exactness require later proofs; they do not follow just
from these surjectivity assertions. Proper
pushforward's norm comparison, flat/Gysin operations, general Chow
convolution and prescribed target identification/realization/coverage
remain separate, as recorded in `GAP_MAP.md` and `TARGET_BRIDGE.md`.

### Surjectivity of the existing open restrictions (SP63 / A11av)

Let \(j:U\hookrightarrow X\) be an open immersion, let
\(\delta\) be a supplied dimension function on \(X\), and retain
\(\delta_U=\delta\circ j\). The degree \(m\) is any integer.
The maps below are the existing finite-cycle and Chow restriction maps.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `openRestriction_surjective` | lift every actual finite cycle, over an arbitrary semiring | $j^*:Z_{\mathrm{fin}}(X;R)\twoheadrightarrow Z_{\mathrm{fin}}(U;R)$ |
| `gradedOpenRestriction_surjective` | lift in the same supplied degree, without ambient finiteness premises | $j^*:Z_{\mathrm{fin},m}^{\delta}(X;R)\twoheadrightarrow Z_{\mathrm{fin},m}^{\delta_U}(U;R)$ |
| `chowOpenRestriction_surjective` | lift every integral Chow class through an actual homogeneous cycle representative | $j^*:\operatorname{CH}_m^\delta(X)\twoheadrightarrow\operatorname{CH}_m^{\delta_U}(U)$ |
| `rationalChowOpenRestriction_surjective` | lift every rational Chow class through the existing rational cycle quotient | $j^*:\operatorname{CH}_m^\delta(X;\mathbf Q)\twoheadrightarrow\operatorname{CH}_m^{\delta_U}(U;\mathbf Q)$ |

The first two endpoints are in `Cycles/OpenRestrictionSurjectivity.lean`.
The quotient endpoints extend `Cycles/ChowOpenRestriction.lean` and
`Cycles/RationalChowOpenRestriction.lean`, respectively. Raw and graded
surjectivity require only an actual open immersion and a semiring of
coefficients, including trivial coefficients. No Noetherianity,
compactness, integrality, nonemptiness or field base is supplied.
For the two quotient endpoints only the target `IsNoetherian X` is a
premise; source Noetherianity is derived with the existing
`openImmersion_isNoetherian` theorem.

For each actual integral closed support \(W\subset U\), its reduced
ambient closure \(\overline W\subset X\) has ideal-comap exactly
\(W\). The private linear combination of these fundamental cycles
therefore gives a right inverse of the existing finite-cycle restriction.
The existing support-degree identity
\(\deg_\delta\overline W=\deg_{\delta_U}W\) and the supported
span description of the homogeneous submodule show that the same cycle
lift preserves degree. This is an actual construction, not a supplied
lifting or surjectivity hypothesis.

To lift a Chow class, choose a homogeneous cycle representative using
the existing class-map surjectivity and apply the graded cycle theorem.
The existing restriction/class-map formula identifies its restricted
class with the original class. The rational proof uses the rational
class map directly; it does not cancel Chow rationalization or assume
that rationalization is injective. Reduced closure is not asserted to
preserve principal relations, and no closure operation on Chow classes
is defined. No new cycle carrier, homogeneous module, quotient or
comparison symbol is introduced.

The next bounded step is the closed-complement image/kernel comparison
on the existing finite cycles. Localization exactness on the quotients
also needs a proved lifting argument for principal relations. These
remain separate from surjectivity, and from general proper, flat or
Gysin operations, convolution, and prescribed target realization.

SP63 validation (September 17, 2026): the focused replay using exactly
the verification file's original four imports passes all four new
declaration checks, four axiom reports and sixteen regressions without
warnings or errors. Each new report uses exactly `propext`,
`Classical.choice` and `Quot.sound`. The tests cover arbitrary-semiring
and same-degree lifting without ambient finiteness, literal reduced
closure recovery, raw and graded identity/composition, target-only
Noetherian quotient surjectivity, actual integral/rational cycle
representatives, quotient composition, empty opens and trivial
coefficients. The full integrated `research/Verification.lean` replay
completes with exit code zero, without warnings or errors: 626 axiom
reports, 734 declaration checks and 565 examples. The 626 unique reports
match the expected inventory exactly, with no missing, extra or duplicate
entries and no disallowed axioms. Of these, 624 use exactly the standard
three axioms. The two unchanged historical exceptions are
`HodgeConjecture.SchemeCycles.polynomialDimensionBound` (no axioms) and
`HodgeConjecture.CommutativeAlgebra.genericFiber_isScalarTower_base`
(`propext` and `Quot.sound`).
The pre-SP63 6831-line verification prefix and historical SP18--SP62
validation record are byte-identical. The full 3149-job build passes
with only the two existing intentional `Challenge.lean` warnings;
the six primary and two supporting dependency checks pass. The single
66-page PDF builds with a clean log; root visual inspection covers
Proposition A.34 on page 41 and its API map on page 55. All 84 labels
are unique and all references resolve.

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
