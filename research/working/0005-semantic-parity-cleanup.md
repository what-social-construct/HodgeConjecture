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

### Construction and input checkpoints (SP17--SP26)

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
| `MatrixRestrictionObstruction.no_ringHom_to_commutative` | exclusion of unital maps from full matrices to a nontrivial commutative ring | prose only |
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
| `UniversalIdempotentAlgebra.mapOfIdempotent` | canonical algebra map determined by an idempotent $e$ | $\varphi_e:\mathcal U\to C$, $(r,s)\mapsto re+s(1-e)$ |
| `UniversalIdempotentAlgebra.RepresentationMorphism` | linear intertwiner between two one-idempotent representations | $T:(V,\varphi_{e_V})\to(W,\varphi_{e_W})$ |
| `MarkedSelectorAlgebraPresentation` | optional stronger full component-algebra presentation; not required by the active Galois route | $\iota_H:F_{\mathbf Q}(H)\to\Gamma_\eta$ |
| `SchemeCorrespondence.sheetLinearization H` | auxiliary direct-import-only linear coset-average comparison, not an algebra map | $\ell_H(gH)=[g]e_H$ |
| generic graph operator | graph projector attached to $\alpha$ | $P_\alpha(t,x)=(t,t\alpha)$ |
| generic diagonal operator | projector onto the marked rational line | $P_0(t,x)=(t,0)$ |
| generic shear | change from diagonal to graph splitting | $U_\alpha(t,x)=(t,x+t\alpha)$ |
| `MarkedProjectorActionComparison` | canonical residual map and action square for a chosen projector, without ambient restriction | $\mathscr R_{\Pi}$ |
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
| `IsRationalHodgeClass M alpha` | rational Hodge membership | $\alpha\in V_{\mathrm{Hdg}}$ |
| `IsAlgebraicHodgeClass M alpha` | cycle-class membership | $\alpha\in\operatorname{im}(\operatorname{cl})$ |
| `RationalHodgeConjectureAt M` | modeled rational Hodge target | $\mathrm{HC}_{\mathbf Q}(\mathscr H)$ |
| `EveryHodgeClassHasPalomarTargetSquare` | equality-of-composites presentation of graph-projector coverage | $\forall\alpha\in V_{\mathrm{Hdg}},\ \exists\Pi:\rho\circ\varphi_\Pi=\varphi_{P_\alpha}$ |
| `ClassDependentMarkedGaloisSelectorCoverage` | classwise marked-selector coverage | $\operatorname{Cov}_{\mathrm{Gal}}(\mathscr H,\rho)$ |

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
