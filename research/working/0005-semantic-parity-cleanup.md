# Semantic parity, pruning, and notation queue

Status: OBJECT ROLES AND NOTATION UPDATED; HISTORICAL CHECKPOINTS RETAINED; HUMAN RELEASE GATES OPEN.

Object-registry refresh: 2026-10-27. Historical validation statements below
describe their named checkpoints. SP107 finite norm/Chow descent is complete
as recorded below. SP108 adds conditional boundary correction on the existing
Chow groups. SP109 constructs a marked Chow map from supplied actual cycles;
geometric selection for a prescribed class remains open.
SP110 completes the actual open/closed Chow localization sequence and its
two-lift consumer; this auxiliary machinery now has proved status.
SP111 proves conditional supported-class extraction using the existing
cycle and Chow objects. General Betti localization and the component-basis
comparison remain supplied; class-dependent support construction stays open.
SP112 tests Chern characters within the same induction. Algebraic complexes
and their extension remain research objects; finite-monodromy bundles give
zero positive rational Chern character. Only the transfer cancellation is
newly formalized, using the existing degree-transfer object.
SP113 proves identity and composition of the existing finite cycle and
integral/rational Chow maps, with multiplication of their actual residue
degrees. These are compatibility theorems, **prose only**: no new map,
quotient, independent notation or public object declaration is introduced.
The subsequent open-representative calculation records a classical partial
construction and the remaining primitive-class problem; it adds no Lean
objects or theorem claims.
Proof-role classification and name coverage are separate from
the Lean checks recorded for each checkpoint; neither is a release audit.

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

### Proof-role index: core objects and objects under investigation

Read **proof role** independently of **implementation status**:

- **CORE** means the fixed Hodge target, the user's fixed correspondence
  action, or the existing concrete cycle/Chow foundations used to state it.
  It does not assert that the general geometric realization is implemented.
- **ROUTE** means an auxiliary construction, optional proof mechanism,
  example, or adapter whose use depends on the selected geometric proof.
  This includes proved Galois and norm results as well as open research
  objects. It does not mean that a proved result has become conjectural,
  deprecated, or a deletion candidate.

The two groups below are the current reading order. Detailed notation tables
retain their historical organization and carry the same proof-role column;
roles there describe the use in that row. Shared foundations can also occur
inside a route-specific comparison. Existing checkpoint status and source
hypotheses remain authoritative for what is proved.

#### Core: fixed target and concrete Chow foundations

| Object / mathematical role | LaTeX notation | Lean representation | Implementation status / source | Proof role |
| --- | --- | --- | --- | --- |
| Fixed smooth projective complex target, dimension and codimension | $X/\mathbf C,\ n=\dim X,\ p\geq0$ | `X : Scheme`, structural morphism to `Spec ℂ`; local dimension/codimension objects below; `p : ℕ` | Actual scheme and dimension foundations exist; no general smooth-projective Betti/Hodge instantiation is supplied by `RationalHodgeCycleClassModel` | CORE |
| Integral supports, cycles, principal relations and rational equivalence | $W\subset X,\ Z^p(X),\ \operatorname{div}_W(g),\ \sim_{\mathrm{rat}}$ | `SchemeCycles.IntegralClosedSubscheme`, `Cycles`, `principalDivisor`, `PrincipalRelationData`, `RationallyEquivalent` | Constructed; detailed cycle and local-order tables below | CORE |
| Rational Chow group and quotient map | $CH^p(X)_{\mathbf Q}=CH_{n-p}(X)_{\mathbf Q},\ c\mapsto[c]$ | `SchemeCycles.RationalChowGroup δ ((n : ℤ) - (p : ℤ))`, `rationalClassMap`; the stated equidimensional interpretation | Constructed quotient; the quotient map is distinct from Betti cycle class | CORE |
| Rational Betti space, Hodge structure and independently specified Hodge subspace | $H^{2p}(X,\mathbf Q),\ H^{p,p}(X),\ \operatorname{Hdg}^p(X)$ | `HX`, `M.hodgeClasses`, `IsRationalHodgeClass M α` | General geometric realization remains to be constructed; these are supplied data in the current model | CORE |
| Fixed Chow-to-Betti realization and its Hodge compatibility | $\operatorname{cl}_X:CH^p(X)_{\mathbf Q}\to H^{2p}(X,\mathbf Q)$ | `M.cycleClass`, `M.cycleClass_lands` for `M : RationalHodgeCycleClassModel ChowX HX` | Active interface; actual degree-zero split instance exists; higher-dimensional instance is unfinished | CORE |
| Prescribed class, output cycle and required comparison | $\alpha\in\operatorname{Hdg}^p(X),\ z_\alpha\in CH^p(X)_{\mathbf Q},\ \operatorname{cl}_X(z_\alpha)=\alpha$ | `α : HX`, `z : ChowX`, `M.cycleClass z = α`; `IsAlgebraicHodgeClass M α` | The Hodge subspace is independent of the cycle-class image; the representative is an output | CORE |
| Fixed ambient correspondence algebra and action | $\Gamma,\ \rho:\Gamma\to\operatorname{End}_{\mathbf Q}(\mathbf Q\oplus H)$ | `Gamma`, `rho : RationalCorrespondenceAction Gamma (ℚ × HX)`, `rho.action` | Fixed by the user's specification; using a particular projector or marked source remains optional | CORE |
| Fixed-pair, all-codimension and all-variety targets | $\mathrm{HC}(X,p),\ \forall p\ \mathrm{HC}(X,p),\ \forall X,p\ \mathrm{HC}(X,p)$ | `RationalHodgeConjectureAt`, `RationalHodgeConjectureForModel` (alias `RationalHodgeConjecture`), `RationalHodgeConjectureForFamily` | Active schemas; the last ranges over a supplied family, not an already constructed type of all smooth projective complex varieties | CORE |

#### Route: auxiliary geometry, induction and projector candidates

| Object / mathematical role | LaTeX notation | Lean representation | Implementation status / source | Proof role |
| --- | --- | --- | --- | --- |
| Prescribed family of auxiliary covers, degree and class-dependent choice | $\{f_j:Y_j\to X\}_{j\in J},\ d_j>0,\ j=j(\alpha)$ | `Index`, `ChowY`, `HY`, `Coeff`, `recipe`, `clY`, `pull`; actual maps are separate scheme data | Abstract indexed recipe exists; a geometric family with the required coverage has not been constructed | ROUTE |
| Upstairs cycle and same-cover class identity | $Z_\alpha,\ \operatorname{cl}_{Y_j}(Z_\alpha)=f_j^*\alpha$ | `ClassDependentChowBettiGeneration`; `recipe j c` | Explicit generation obligation; not an inhabited geometric instance | ROUTE |
| Supplied sheet-indexed homogeneous cycle family | $C_s\in Z_n(X)_{\mathbf Q},\ s\in G/H,\ s_0=H$ | `C : CollisionFoundations.GaloisSheets H → SchemeCycles.cyclesOfDegree ℚ δ n`; `baseSheet H` | SP109 input of actual cycles; no current construction supplies this family from the collision fiber product or the normal-closure tensor component with the required Betti image | ROUTE |
| Residual coefficients assembled into an actual cycle | $t_C:E_H\to Z_n(X)_{\mathbf Q},\ x\mapsto\sum_s x(s)C_s$ | `MarkedSheetChow.cycleMap` | SP109 constructed; fixed ambient scheme and degree, arbitrary dimension; [source](../../HodgeConjecture/Realization/Chow/MarkedCycleMap.lean) | ROUTE |
| Chow class of the assembled cycle | $\eta_C:E_H\to CH_n(X)_{\mathbf Q},\ \eta_C(x)=[t_C(x)]$ | `MarkedSheetChow.chowMap`; `chowMap_residualClass`; `chowMap_congr` | SP109 constructed on the existing quotient; principal-relation invariance and actual open/finite naturality proved | ROUTE |
| Realization of the supplied cycle recipe and exact image | $\theta_C=\operatorname{cl}\circ\eta_C,\ \operatorname{im}\theta_C=\operatorname{span}_{\mathbf Q}\{\operatorname{cl}[C_s]:s\ne s_0\}$ | `cl.comp (MarkedSheetChow.chowMap H δ n C)`; `range_chowMap`; `range_cycleClass_chowMap` | SP109 image formula proved for a supplied linear realization; prescribed Hodge-class coverage remains open | ROUTE |
| Reweighted family evaluated at the canonical marked vector | $C'_s=-x(s)C_s,\ \eta_{C'}(q_H-1)=\eta_C(x)$ | `MarkedSheetChow.chowMap_residualClass_reweight` | SP109 proved; only rational coefficients change; this does not select cycles from a Hodge class | ROUTE |
| Finite norm, cycle/Chow pushforward, transfer and normalized descent | $N_f,\ f_*,\ f_*f^*=d\,\mathrm{id},\ d^{-1}f_*Z_\alpha$ | `functionFieldNorm`, `rationalChowFinitePushforward`, `RationalDegreeTransfer`, `normalizedPushforward_cycleClass` | Actual finite Chow map proved in SP107; identity and composition proved in SP113; same-cover Betti degree law and cycle-class square still need geometric instantiation | ROUTE |
| Open locus and boundary inclusion in a smooth projective auxiliary variety | $j:U\hookrightarrow Y,\ i:D=Y\setminus U\hookrightarrow Y$ | `j`, `i` as scheme morphisms; `SchemeCycles.rationalChowOpenRestriction` | Chow restriction and its surjectivity are constructed; smoothness of $D$ is an additional hypothesis, not automatic | ROUTE |
| Actual reduced closed complement and its ideal | $I_Z=\mathcal I((X\setminus U)_{\mathrm{red}}),\ Z=V(I_Z),\ i:Z\hookrightarrow X$ | `SchemeCycles.openComplementIdeal j`; `(openComplementIdeal j).subscheme`; `(openComplementIdeal j).subschemeι` | **PROVED / CONSTRUCTED, SP110**; reducedness and complementary point image proved; no ambient reducedness or finiteness needed; [source](../../HodgeConjecture/Cycles/OpenClosedLocalization.lean) | ROUTE |
| Boundary-supported cycle submodule and restriction kernel | $Z_{*,Z}(X;R)=\operatorname{im}i_*=\ker j^*$, also in degree $n$ | `Finsupp.supported R R {W \| ambientGenericPoint W ∉ Set.range j.base}`; `range_openComplementPushforward_eq_ker` | **PROVED, SP110**; actual raw and graded maps, any coefficient semiring, actual restricted dimension functions | ROUTE |
| Class-dependent algebraic support and vanishing target | $Z_\alpha\subset X,\ \operatorname{codim}_X Z_\alpha\geq p,\ \alpha\vert_{X\setminus Z_\alpha}=0$ | Actual closed/open scheme maps `i`, `j`; `hcomp`, `hα` in `SupportedClass.exists_supported_cycle_of_vanishing` | **RESEARCH / OPEN CONSTRUCTION**; the consumer accepts a chosen support; it does not find one or establish its codimension bound | ROUTE |
| Supported cohomology, support lift and localization | $H_Z^{2p}(X,\mathbf Q),\ \gamma\mapsto\alpha,\ \operatorname{im}(\mathrm{forget})=\ker j^*$ | Supplied `HZ`, `forgetSupport`, `restrictH`, `hExact` | **GEOMETRIC INSTANCE OPEN**; SP111 keeps localization explicit, separate from proved cycle/Chow exactness | ROUTE |
| Top-component basis and fundamental-class comparison | $b_k=[W_k]_{\mathrm{supp}},\ \deg_\delta W_k=n=\dim X-p$ | `W : ι → SchemeCycles.IntegralClosedSubscheme Z`, `hW`, `b : Module.Basis ι ℚ HZ`, `hBasis` | **GEOMETRIC INSTANCE OPEN**; deriving this basis from codimension remains unformalized; singular/reducible support is allowed by the consumer | ROUTE |
| Extracted component cycle and its actual ambient Chow class | $c_\gamma=\sum_k(b.\mathrm{repr}\,\gamma)_k[W_k],\ z_\gamma=i_{*,\mathrm{cyc}}c_\gamma,\ \operatorname{cl}[z_\gamma]=\alpha$ | Existing `Module.Basis.constr`, `gradedClosedImmersionPushforwardWithCoefficients`, `rationalClassMap`; `SupportedClass.cycleClass_componentExpansion`, `exists_supported_cycle_of_vanishing`, `vanishing_iff_supported_cycle` | **CONDITIONAL / PROVED, SP111**; finite expansion and actual cycle-level zero restriction proved; converse uses `hRestrict`; [source](../../HodgeConjecture/Realization/Chow/SupportedClass.lean) | ROUTE |
| Lifted relation carrier and rational function | $\bar W\subset X,\ \bar f\in K(\bar W)^\times,\ (\bar W,\bar f)\vert_U=(W,f)$ | `SchemeCycles.exists_openRestriction_principalRelationData`; `openClosureSubscheme`; inverse `functionFieldEquivOfOpenImmersion` | **PROVED, SP110**; carrier degree $n+1$ retained, data lifting needs no Noetherianity; [source](../../HodgeConjecture/Cycles/PrincipalRelationLifting.lean) | ROUTE |
| Integral and rational relation-span images | $j^*\mathcal R_n(X;\mathbf Z)=\mathcal R_n(U;\mathbf Z),\ j^*\mathcal R_n(X;\mathbf Q)=\mathcal R_n(U;\mathbf Q)$ | `SchemeCycles.principalRelations_map_openRestriction`; `rationalPrincipalRelations_map_openRestriction` | **PROVED, SP110**; actual principal generators, ambient Noetherianity; closure is not asserted to descend to Chow | ROUTE |
| Cycle on the open and a closure lift | $z_U\in CH^p(U)_{\mathbf Q},\ \bar z\in CH^p(Y)_{\mathbf Q},\ j^*\bar z=z_U$ | `SchemeCycles.rationalChowOpenRestriction_surjective`; `zU`, `z` in `BoundaryCorrection.isAlgebraicHodgeClass_of_openRestriction` | SP108 uses proved Chow lifting; construction with $\operatorname{cl}(z_U)=j^*f^*\alpha$ is unresolved | ROUTE |
| Auxiliary polarization and smooth ample boundary | $A,\ h=c_1(A),\ L=h\cup-,\ D\in\vert A^{\otimes m}\vert,\ m>0$ | No general geometric Chern-class/Lefschetz operator or Bertini construction here; scheme maps `i`, `j` remain supplied | **CLASSICAL CANDIDATE**; sufficiently large $m$ permits a smooth divisor; auxiliary choices do not change the fixed target or correspondence action | ROUTE |
| Primitive open target and killed Lefschetz summand | $P_h^{2p}(Y)=\ker L^{d-2p+1},\ \beta=\beta_{\mathrm{prim}}+L\gamma,\ j^*\beta=j^*\beta_{\mathrm{prim}}$ for $2p\leq d=\dim Y$ | No geometric primitive-cohomology implementation; `restrictH` is supplied in `BoundaryCorrection` | **CLASSICAL DEDUCTION / OPEN CONSTRUCTION**; $\ker j^*=L H^{2p-2}$ and $j^*$ is injective on the primitive summand; its prescribed algebraic open representative is unresolved, including after finite pullback with the pulled-back polarization | ROUTE |
| Zero open representative in the vanishing range | $z_U=0,\ H^{2p}(U,\mathbf Q)=0$ for $2p>\dim Y$ | `0 : SchemeCycles.RationalChowGroup (δ.comapOpenImmersion j) n`; `clU.map_zero`; geometric cohomological vanishing not implemented | **CLASSICAL PARTIAL CONSTRUCTION**; smooth affine complement; completing boundary correction still requires SP108's other inputs; [calculation and sources](../TARGET_BRIDGE.md#open-representative-the-smooth-ample-boundary-calculation) | ROUTE |
| Additive Chow localization and boundary ambiguity | $CH_{n-p}(D)_{\mathbf Q}\to CH_{n-p}(Y)_{\mathbf Q}\to CH_{n-p}(U)_{\mathbf Q}\to0$ | `SchemeCycles.range_rationalChowOpenComplementPushforward_eq_ker`; `ChowLocalization.ofOpenComplement`; `ChowLocalization.two_lifts_differ_by_boundary` | **PROVED FOR ACTUAL MAPS, SP110**; integral and rational exactness, target Noetherianity, both sources derived; generic `ChowLocalizationHypotheses` still requires evidence for other maps; [source](../../HodgeConjecture/Cycles/ChowLocalization.lean) | ROUTE |
| Cohomological discrepancy of a closure | $\delta=f^*\alpha-\operatorname{cl}_Y(\bar z),\ j^*\delta=0$ | `α - M.cycleClass z`, with Hodge membership and zero restriction proved inside `BoundaryCorrection.exists_boundary_correction`; `α` there is the ambient target | SP108 conditional consumer; not the Chow idempotence defect $\Pi^2-\Pi$ | ROUTE |
| Cohomology with support, restriction and Gysin map | $H_D^{2p}(Y,\mathbf Q),\ j^*,\ i_*:H^{2p-2}(D,\mathbf Q)(-1)\to H^{2p}(Y,\mathbf Q)$ | Supplied modules `HX`, `HD`, `HU` and maps `restrictH`, `pushH` in `BoundaryCorrection`; no general supported Betti construction | SP108 keeps cycle-class squares explicit; no pure Hodge structure on the nonproper open is assumed | ROUTE |
| Lower-codimension Hodge lift | $\gamma\in\operatorname{Hdg}^{p-1}(D),\ i_*\gamma=\delta$ | Explicit `hBoundaryLift` premise of `BoundaryCorrection.exists_boundary_correction` and its consumers | Geometric proof still needed in Lean; for smooth projective $D$, follows classically from Gysin exactness and polarizability; does not yet give a cycle | ROUTE |
| Boundary correction cycle and corrected output | $b\in CH^{p-1}(D)_{\mathbf Q},\ \operatorname{cl}_D(b)=\gamma,\ z=\bar z+i_*b,\ \operatorname{cl}_Y(z)=f^*\alpha$ | `BoundaryCorrection.exists_boundary_correction`; `isAlgebraicHodgeClass_of_schemeOpenRestriction` uses actual `rationalChowClosedImmersionPushforward` and open restriction | SP108 proved conditional consumer; [source](../../HodgeConjecture/Realization/Chow/BoundaryCorrection.lean); requires boundary algebraicity, Hodge lift and the two comparison squares | ROUTE |
| Induction parameter, hypothesis and base | $p;\ \forall T/\mathbf C\text{ smooth projective},\ \mathrm{HC}(T,p-1);\ p=0$ | `hBoundary : RationalHodgeConjectureAt MD` in `BoundaryCorrection`; existing family-target schema; no general geometric induction theorem | Conditional consumer accepts the lower-codimension hypothesis, uniformly in dimension. Codimension zero is generated by components; divisor classes use Lefschetz $(1,1)$ | ROUTE |
| Resolution or normal-crossings boundary, if needed | $\widetilde Y\to Y,\ \widetilde D=\bigcup D_a$ | No general implementation of the required supported-cohomology comparison | Further geometric obligation; cannot replace a singular boundary by a smooth divisor silently | ROUTE |
| Parameter space for effective cycles of fixed dimension and degree | $\operatorname{Chow}_{n-p,e}(X)$ | No Chow-variety implementation here; distinct from `SchemeCycles.ChowGroup` | Research candidate; degree $e$ is measured against a fixed polarization; rational cycles require rational combinations | ROUTE |
| Incidence family and fibers | $S,\ \mathcal Z\subset S\times X,\ Z_s$ | No selected general incidence-family construction | On a smooth connected base a flat family's Betti cycle class is constant; selecting relevant components remains substantive | ROUTE |
| Algebraic bundle, regular section, zero locus and Chern class | $E,\ s,\ Z(s),\ c_p(E)$ | No class-dependent bundle/Chern-cycle construction in this repo | Research candidate; fixed $E$ gives fixed zero-locus class under the regularity hypotheses | ROUTE |
| Algebraic perfect complexes, rational virtual class and ambient extension | $E_\alpha^\bullet,\ \xi_\alpha\in K_0^{\mathrm{alg}}(U)_{\mathbf Q},\ \bar E_\alpha^\bullet$ | No geometric perfect-complex or algebraic K-group construction in this repo | **RESEARCH / CLASSICAL EXTENSION**; Stacks 08EC and 08E0 supply extension once the algebraic open object exists; prescribed-class construction remains open | ROUTE |
| Additive Chern-character recipe and required open class | $z_U=\operatorname{ch}^{CH}_p(\xi_\alpha),\ \operatorname{cl}_U(z_U)=j^*\alpha$ | No implemented Chern map; intended output is the existing open `RationalChowGroup` consumed by `BoundaryCorrection` | **RESEARCH / UNCONSTRUCTED**; fixed ambient realization; Stacks 0ESY; no assumed Chern preimage is treated as a construction | ROUTE |
| Finite-monodromy bundle, trace-zero summand and splitting cover | $E_\rho,\ \ker(\operatorname{Tr}_f),\ q:T\to U,\ q^*E_\rho\simeq\mathcal O_T^{\oplus r}$ | Geometric bundles unconstructed; `RationalDegreeTransfer.pull_injective`, `pull_eq_zero_iff` prove the cancellation step | **TESTED CANDIDATE / SP112**; positive rational Chern character is zero; cannot supply a nonzero open target; does not exclude arbitrary bundle idempotents | ROUTE |
| Boundary-supported perfect complex and localized Chern character | $E_D^\bullet,\ \operatorname{ch}_p(D\to X,E_D^\bullet)\cap[X]$ | No localized Chern construction; its proposed pushforward lands in the existing Chow group | **RESEARCH / CLASSICAL**; Stacks 0FB0; supplies boundary corrections and has zero open restriction | ROUTE |
| Separable function-field extension and normal-closure splitting | $L/K,\ N/K,\ N\otimes_KL\simeq\prod_{\sigma:L\hookrightarrow N}N$ | `NormalClosureData`, `normalClosureTensorGenericSheetsEquiv`, `functionFieldNormalClosureSplitFiberIso` | Constructed for the stated hypotheses; labels sheets of an existing cover, not points of a prescribed-class cycle parameter space | ROUTE |
| Collision algebra, diagonal ideal, complementary component and selectors | $C=A\otimes_BA,\ J=\ker\mu,\ C\simeq C/J\times C/\operatorname{Ann}(J)$ | `CollisionAlgebra`, `collisionObstructionIdeal`, `CollisionSelectorPair`, `CollisionSchemeDecomposition` | Proved under explicit hypotheses and used by `collisionSchemeCorrespondence` and its span decomposition; the generation/descent and boundary-correction endpoints do not require this object, and no prescribed Hodge-class cycle is extracted from it | ROUTE |
| Marked sheet algebra, residual corner and algebra decomposition | $A_H=\mathbf Q^{G/H},\ q_H,\ E_H^{\mathrm{corner}},\ A_H\simeq\mathbf Q\times E_H^{\mathrm{corner}}$ | `GenericSheetAlgebra`, `MarkedSheetProjector.selector`, `MarkedAugmentedAlgebra.selectorAlgebraDecomposition` | Proved; multiplicative selector coordinates differ from the linear constant-unit graph coordinates | ROUTE |
| Galois/deck action, group average and Hecke corner | $G,H,\ e_H,\ e_H\mathbf Q[G]e_H$ | `FiniteDeckAction`, `SchemeCorrespondence.subgroupAverage`, `SubgroupHeckeAlgebra` | Constructed algebraic machinery; choice and prescribed geometric action remain under investigation | ROUTE |
| Class graph, algebraic projector, residual realization and action comparison | $P_\alpha,\ \Pi_\alpha,\ \theta:E_H\to H,\ \Theta=\mathrm{id}\oplus\theta$ | `BlockGraphProjector`, `AlgebraicProjectorLift`, `MarkedGaloisSelectorComparison` | Active conditional branch; a linear assignment $\theta(q_H-1)=\alpha$ alone does not supply the geometric comparison | ROUTE |
| Boundary extension of projectors and multiplicative defect | $\operatorname{Ext}_r(e),\ \operatorname{Def}(\Pi)=\Pi^2-\Pi$ | `AlgebraProjectorExtension`, `AlgebraProjectorClosure`, `projectorIdempotenceDefect` | Existing objects; additive boundary correction of a cycle does not prove idempotence of a corrected correspondence | ROUTE |
| Pure motives, Tate object and motivic cycle morphism | $\operatorname{CHM}_{\mathbf Q}(\mathbf C),\ h(X),\ \mathbb T_p,\ z:\mathbb T_p\to h(X)$ | No actual general Chow-motive category/realization instance here; `ClassGraphProjectorConstruction` is an interface, not that category | Optional endpoint language; covariance/Tate conventions must be fixed | ROUTE |
| Structured realization and alternative realization-class spaces | $R,\ \mathcal R,\ \operatorname{Hom}_{\mathcal R}(R\mathbb T_p,Rh(X))$ | No general functor implementation; rational Betti model remains the active target | Motivic research formulation; arithmetic realizations need their own bases and structures | ROUTE |
| Weil-class/abelian auxiliary geometry | $A,\ W_K(A)$, with the CM field and exterior-power convention specified if used | No selected general construction or coverage instance | Candidate source of ideas; no dimension-specific abelian construction or OAI object adopted | ROUTE |

The boundary calculation suggests a **conditional induction**, not a
completed recursive proof. For $p\geq1$, a smooth projective $Y$ and smooth divisor
$D$, the Gysin sequence places $\delta$ in $\operatorname{im}i_*$. The
source and target, after the Tate twist, are polarizable pure Hodge
structures of the same weight. The polarization-orthogonal complement of
$\ker i_*$ maps isomorphically onto $\operatorname{im}i_*$, giving a rational
Hodge lift $\gamma$. The induction hypothesis in codimension
$p-1$ supplies $b$, and cycle-class compatibility gives
$\operatorname{cl}(\bar z+i_*b)=f^*\alpha$. The open-locus representative,
appropriate boundary geometry, and actual comparison maps are still needed.
The splitting is Hodge-theoretic; no algebraic projector lifting it is assumed.
This keeps dimension arbitrary and uses $p$ as the decreasing parameter.
SP108 proves the correction implication on the actual rational Chow groups;
the supported Hodge lift and cohomological comparison squares remain premises.
Only proved open Chow surjectivity is used for the closure lift, so full
Chow localization exactness is not an additional prerequisite for this step.
See [Stacks 02RX](https://stacks.math.columbia.edu/tag/02RX) for Chow
localization, [de Cataldo--Migliorini, §2 and Theorem 4.1](https://arxiv.org/pdf/math/0504560)
for the cohomological formalism and Gysin compatibility, and
[Deligne, §2(iii)](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf)
for the divisor base case. Algebraicity of an arbitrary lower-codimension
Hodge class is the induction input, not a consequence of separability.

SP108 validation (2026-10-13): the full build passes (3266 jobs; only the two
pre-existing `Challenge.lean` warnings). The eight focused checks in
`research/BoundaryCorrectionVerification.lean` pass, as does the standard-three
axiom audit of all three new production theorems. All 77 notation tables
retain their 1030 classified rows; the inline-code name scan covers all 906
public object declarations. Table structure, math delimiters, local links and
the new-file proof-placeholder scan pass. Name coverage is not a semantic
equivalence proof, and the conditional inputs remain explicit.

SP109 registry audit (2026-10-13): 77 notation tables contain 1036 classified
rows (309 CORE, 727 ROUTE). All 908 public object declarations have exact
identifier coverage in inline Lean code. The six added rows distinguish
the supplied cycles, constructed maps, realized image, reweighting and
realization lifecycle. Table widths, math delimiters, local links and the
new-file proof-placeholder scan pass; coverage does not assert geometric
instantiation of the remaining inputs.

#### Realization lifecycle: active, unfinished, example, archived

SP110 validation (2026-10-13): full build passes (3270 jobs; the two existing
`Challenge.lean` warnings only), as do seven focused localization checks and
twenty enforced axiom audits. The registry has 77 tables and 1040 rows
(309 CORE, 731 ROUTE), covering all 909 public object declarations by name.
The new complement object and its support, relation-lifting and exactness
comparisons have explicit LaTeX/Lean entries and proved auxiliary status.
Table structure, local links and new-file placeholder scans pass.

Open-representative registry update (2026-10-13): three research rows record
the auxiliary polarization, primitive target and zero open cycle. There are
at that checkpoint 77 tables and 1043 rows (309 CORE, 734 ROUTE); the 909 public Lean object
declarations are unchanged. These classical calculations are distinguished
from formal implementations and from the unresolved cycle construction.

SP111 registry update (2026-10-13): four rows distinguish the support
construction problem, supplied supported cohomology, supplied component
basis, and proved extraction consumer. At that checkpoint there are 77 tables and 1047
rows (309 CORE, 738 ROUTE). All 909 public object declarations remain
unchanged: the three new production declarations are theorems using the
existing Mathlib basis and scheme-cycle constructions.

Validation: the full `lake build` passes (3271 jobs), with the two existing
`Challenge.lean` placeholder warnings. The focused SP111 verification passes
four examples and three enforced axiom audits. Table structure, local links,
new-file placeholder scans and `git diff --check` also pass.

SP112 registry update (2026-10-14): four research rows distinguish the
algebraic complex, Chern recipe, tested finite-monodromy bundle and localized
boundary class. There are now 77 tables and 1051 rows (309 CORE, 742 ROUTE).
The 909 public object declarations are unchanged; the two new Lean
declarations are cancellation theorems on the existing transfer structure.

SP112 validation: full `lake build` passes (3271 jobs; the two existing
`Challenge.lean` placeholder warnings). Both new theorems pass an enforced
standard-three axiom audit. All 77 table headers, 1051 classified rows,
table widths, math delimiters and 240 local links pass validation, as do
the modified Lean file's placeholder scan and `git diff --check`.

| Object / mathematical role | LaTeX notation | Lean representation | Implementation status / source | Proof role |
| --- | --- | --- | --- | --- |
| General Chow--Betti/Hodge realization | $\operatorname{cl}_X:CH^p(X)_{\mathbf Q}\to H^{2p}(X,\mathbf Q)$ | `RationalHodgeCycleClassModel` | **ACTIVE / GEOMETRIC INSTANCE UNFINISHED**; [HodgeClasses](../../HodgeConjecture/Realization/HodgeClasses.lean), [active umbrella](../../HodgeConjecture/Realization.lean) | CORE |
| Marked map into actual Chow, before Betti realization | $\eta_C:E_H\to CH_n(X)_{\mathbf Q}$ | `MarkedSheetChow.chowMap` | **ACTIVE / PROVED FROM SUPPLIED CYCLES**; [source](../../HodgeConjecture/Realization/Chow/MarkedCycleMap.lean); family selection and general Betti instance remain unfinished | ROUTE |
| Existing conditional correction, descent and marked realization interfaces | $\bar z+i_*b,\ d^{-1}f_*Z,\ \mathscr R_{\alpha,x}$ | `BoundaryCorrection`, `UpstairsGeneration`, `MarkedGaloisSelectorComparison`, `ClassDependentMarkedGaloisSelectorCoverage` | **ACTIVE / CONDITIONAL**; explicit geometry and comparison maps still required | ROUTE |
| Concrete finite split degree-zero realization | $CH_0(Z_I)_{\mathbf Q}\simeq H^0(Z_I(\mathbf C),\mathbf Q)$ | `SplitBetti.cycleClass`, `SplitBettiTateBlock`, `SplitGaloisMarkedComparison` | **ACTIVE / PROVED EXAMPLE**; [Betti umbrella](../../HodgeConjecture/Realization/Betti.lean); not a general higher-codimension realization | ROUTE |
| Earlier commutative selector-realization chain | Historical selector-generated realization; no new notation | Archived `SelectorRealization.lean`, `BoundaryProjector.lean`, `CohomologicalProjector.lean`, `CompactificationProjector.lean` | **ARCHIVED / SUPERSEDED**; [legacy realization directory](../archive/legacy-lean/HodgeConjecture/Realization/); excluded from active library | ROUTE |
| Earlier linear coset-average comparison | $gH\mapsto[g]e_H$ | Archived `SheetLinearization.lean` | **ARCHIVED**; [source](../archive/legacy-lean/HodgeConjecture/Realization/Chow/SheetLinearization.lean); not an algebra map from pointwise multiplication to convolution | ROUTE |

### Current object index: cycles, codimension, and the finite-norm bridge

Every notation table uses separate **Object / mathematical role**,
**LaTeX notation**, and **Lean representation** columns. The tables below
record SP103--SP107, including the completed finite scheme norm/Chow bridge. The later
tables retain the normalization, Galois, graph, split Chow/Betti, projector,
and Hodge objects and their checkpoint history. A comparison theorem gets
an equality or an isomorphism in the LaTeX column, not a new carrier symbol.

Lean expressions in this index use `open AlgebraicGeometry CategoryTheory
HodgeConjecture`; `SchemeCycles` and `CommutativeAlgebra` are the actual
project namespaces. Lettered parameters and their typeclass hypotheses
are local binders, not additional definitions. Source links identify the
module that defines or uses the representation. **Existing** refers to the
established library; **SP103--SP107** refers to the recorded checked checkpoints. SP107 completes
the finite norm/divisor identity and integral/rational Chow descent below;
actual Betti comparison and geometric generation remain separate.

The current local calculation writes the finite dominant map as
$f:X\to Y$, with integral source and target and locally Noetherian $Y$.
Choose a nonempty affine $U\subseteq Y$ and put $V=f^{-1}(U)$.
This orientation is local to this calculation: the normalization tables
use $p:Y\to X$, with base ring $B_U$ and upstairs ring $A_U$.
Thus local $A$ means the **base** ring and local $B$ the **upstairs** ring;
they do not rename the earlier normalization objects globally.

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Ambient scheme | $X$ | `X : Scheme` | Existing Mathlib carrier | CORE |
| Integral closed support | $W\in\operatorname{IntSub}(X)$ | `W : SchemeCycles.IntegralClosedSubscheme X` | Existing; [Basic](../../HodgeConjecture/Cycles/Basic.lean) | CORE |
| Scheme carried by the support | $W$ as a scheme | `W.val.subscheme` | Existing; distinct from its ideal-sheaf datum | CORE |
| Closed inclusion | $\iota_W:W\hookrightarrow X$ | `W.val.subschemeι` | Existing | CORE |
| Ambient generic point of the support | $\xi_W$ | `SchemeCycles.ambientGenericPoint W` | Existing; [PointSupport](../../HodgeConjecture/Cycles/PointSupport.lean) | CORE |
| Reduced point closure | $\overline{\{x\}}_{\mathrm{red}}$ | `SchemeCycles.pointSupport X x` | Existing; same integral-support index | CORE |
| Actual chain codimension | $\operatorname{codim}_X W$ | `SchemeCycles.supportCodimension W : ℕ∞` | Existing; [DivisorSupport](../../HodgeConjecture/Cycles/DivisorSupport.lean) | CORE |
| Prime divisors | $\operatorname{PrimeDiv}(X)$ | `SchemeCycles.PrimeDivisor X` | Existing subtype of integral supports | CORE |
| Divisor points | $X^{(1)}=\{x:\dim\mathcal O_{X,x}=1\}$ | `SchemeCycles.DivisorPoint X` | Existing; [SchemeLocalOrder](../../HodgeConjecture/Cycles/SchemeLocalOrder.lean) | CORE |
| Point/support identification | $X^{(1)}\simeq\operatorname{PrimeDiv}(X)$ | `SchemeCycles.divisorPointEquivPrimeDivisor X` | Existing proved equivalence | CORE |
| Finite cycles with coefficients | $Z_{\mathrm{fin}}(X;\Lambda)$ | `SchemeCycles.Cycles X Λ` | Existing finite-support module | CORE |
| Fundamental cycle of an integral support | $[W]$ | `SchemeCycles.fundamentalCycle Λ W` | Existing cycle, not a quotient class | CORE |
| Dimension function | $\delta:X\to\mathbf Z$ | `δ : SchemeCycles.DimensionFunction X` | Existing; [DimensionFunction](../../HodgeConjecture/Cycles/DimensionFunction.lean) | CORE |
| Canonical field-induced dimension function | $\delta_{X/k}(x)=\operatorname{trdeg}_k\kappa(x)$ | `SchemeCycles.DimensionFunction.ofLocallyOfFiniteType k X pX` | Existing; structural map `pX` locally of finite type | CORE |
| Degree of a support | $\deg_\delta W=\delta(\xi_W)$ | `SchemeCycles.supportDegree δ W` | Existing; dimension degree, not field-extension degree | CORE |
| Homogeneous cycles | $Z^\delta_{\mathrm{fin},n}(X;\Lambda)$ | `SchemeCycles.cyclesOfDegree Λ δ n` | Existing submodule; [CycleDegree](../../HodgeConjecture/Cycles/CycleDegree.lean) | CORE |
| Scheme function field | $K(X)$ | `X.functionField` | Existing actual generic stalk | CORE |
| Nonzero rational function | $g\in K(X)^\times$ | `g : X.functionFieldˣ` | Existing units of that field | CORE |
| Signed order at a divisor point | $\operatorname{ord}_x(g)$ | `SchemeCycles.divisorOrder X x g` | Existing, length-based coefficient | CORE |
| Signed order at a prime support | $\operatorname{ord}_W(g)$ | `SchemeCycles.primeDivisorOrder X W g` | Existing; same coefficient through the point/support equivalence | CORE |
| Scheme principal divisor | $\operatorname{div}_X(g)$ | `SchemeCycles.principalDivisor X g` | Existing; integral, locally Noetherian, quasi-compact scheme; [PrincipalDivisor](../../HodgeConjecture/Cycles/PrincipalDivisor.lean) | CORE |
| Principal divisor on a closed carrier, in ambient cycles | $(\iota_W)_*\operatorname{div}_W(g)$ | `SchemeCycles.ambientPrincipalDivisor W g` | Existing; [PrincipalDivisorImage](../../HodgeConjecture/Cycles/PrincipalDivisorImage.lean) | CORE |
| Principal-relation datum | $(W,g),\ \deg_\delta W=n+1$ | `SchemeCycles.PrincipalRelationData δ n` | Existing actual carrier/function pair | CORE |
| Homogeneous principal-relation generator | $r_{W,g}$ | `SchemeCycles.principalRelation δ n d` | Existing homogeneous ambient divisor | CORE |
| Integral principal-relation submodule | $\mathcal R_n^\delta(X)$ | `SchemeCycles.principalRelations δ n` | Existing span; [PrincipalRelations](../../HodgeConjecture/Cycles/PrincipalRelations.lean) | CORE |
| Rational equivalence | $c\sim_{\mathrm{rat}}c'$ | `SchemeCycles.RationallyEquivalent δ n c c'` | Existing relation defined by that submodule | CORE |
| Integral Chow quotient | $\mathrm{CH}_n^\delta(X)$ | `SchemeCycles.ChowGroup δ n` | Existing quotient; Noetherian scheme hypotheses | CORE |
| Integral quotient class map | $c\mapsto[c]$ | `SchemeCycles.classMap δ n` | Existing; distinct from Betti cycle class | CORE |
| Rational principal-relation submodule | $\mathcal R_n^\delta(X)_{\mathbf Q}$ | `SchemeCycles.rationalPrincipalRelations δ n` | Existing rational span of the same generators | CORE |
| Rational Chow quotient | $\mathrm{CH}_n^\delta(X;\mathbf Q)$ | `SchemeCycles.RationalChowGroup δ n` | Existing; [RationalChow](../../HodgeConjecture/Cycles/RationalChow.lean) | CORE |
| Rational quotient class map | $c\mapsto[c]_{\mathbf Q}$ | `SchemeCycles.rationalClassMap δ n` | Existing | CORE |
| Integral-to-rational Chow map | $\mathrm{CH}_n^\delta(X)\to\mathrm{CH}_n^\delta(X;\mathbf Q)$ | `SchemeCycles.chowRationalize δ n` | Existing | CORE |
| Scalar-extension identification | $\mathbf Q\otimes_{\mathbf Z}\mathrm{CH}_n^\delta(X)\simeq\mathrm{CH}_n^\delta(X;\mathbf Q)$ | `SchemeCycles.chowRationalizationEquiv δ n` | Existing proved equivalence | CORE |
| Actual integral image | $f(W)$ | `SchemeCycles.imageSubscheme f W` | Existing; [FinitePushforward](../../HodgeConjecture/Cycles/FinitePushforward.lean) | ROUTE |
| Support-to-image map | $q_W:W\to f(W)$ | `(W.val.subschemeι ≫ f).toImage` | Existing actual scheme map | ROUTE |
| Finite pushforward weight | $d_f(W)=[K(W):K(f(W))]$ | `SchemeCycles.finitePushforwardDegree f W` | Existing; scalar action is the actual `q_W` pullback | ROUTE |
| Finite cycle pushforward | $f_{*,\mathrm{cyc}}[W]=d_f(W)[f(W)]$ | `SchemeCycles.finitePushforward Λ f` | Existing linear map on the same cycles | ROUTE |
| Homogeneous finite cycle pushforward | $f_{*,\mathrm{cyc}}:Z_n^{\delta_X}\to Z_n^{\delta_Y}$ | `SchemeCycles.gradedFinitePushforward Λ δX δY f hdeg n` | Existing; [GradedFinitePushforward](../../HodgeConjecture/Cycles/GradedFinitePushforward.lean) | ROUTE |
| Norm on an actual image carrier | $N_{q_W}:K(W)^\times\to K(f(W))^\times$ | `SchemeCycles.finiteImageNorm f W` | SP107; [FinitePrincipalDivisorImage](../../HodgeConjecture/Cycles/FinitePrincipalDivisorImage.lean) | ROUTE |
| Image principal-relation datum | $(f(W),N_{q_W}g)$ | `SchemeCycles.PrincipalRelationData.finiteImage δX δY f hdeg n d` | SP107; actual carrier and constructed norm | ROUTE |
| Integral finite Chow pushforward | $f_*:\mathrm{CH}_n(X)\to\mathrm{CH}_n(Y)$ | `SchemeCycles.chowFinitePushforward k pY f n` | SP107 constructed; SP113 `chowFinitePushforward_id`, `chowFinitePushforward_comp` proved; [FiniteChowPushforward](../../HodgeConjecture/Cycles/FiniteChowPushforward.lean), [composition](../../HodgeConjecture/Cycles/FiniteChowPushforwardComposition.lean) | ROUTE |
| Rational finite Chow pushforward | $f_*:\mathrm{CH}_n(X;\mathbf Q)\to\mathrm{CH}_n(Y;\mathbf Q)$ | `SchemeCycles.rationalChowFinitePushforward k pY f n` | SP107 constructed; SP113 `rationalChowFinitePushforward_id`, `rationalChowFinitePushforward_comp` proved; [RationalFiniteChowPushforward](../../HodgeConjecture/Cycles/RationalFiniteChowPushforward.lean), [composition](../../HodgeConjecture/Cycles/FiniteChowPushforwardComposition.lean) | ROUTE |

Codimension is already established: `supportCodimension_eq_stalkDim`
identifies it with the local-ring dimension, and
`supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType`
identifies codimension $r$ with degree $\delta(\eta_X)-r$ in the integral
locally finite-type field setting. `FiniteGrading` already proves
preservation of the canonical dimension grading. These are existing
results to reuse; no new codimension object or definition is required.
Grading preservation alone is not an unconditional codimension theorem
for arbitrary finite morphisms.

#### Local algebra and the actual finite affine chart

In the next table $y\in U$ is a target divisor point when local orders
are used, $R=\mathcal O_{Y,y}$, $\mathfrak p$ is its chart prime,
$S=A\setminus\mathfrak p$, and $T=S^{-1}B$. For
$q\in\operatorname{MaxSpec}(T)$, write $x_q$ for its actual fiber point.
The general semilocal length results also apply to finite algebras that
are not domains; the norm formula adds its stated domain hypotheses.

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Finite dominant scheme map | $f:X\to Y$ | `f : X ⟶ Y`, with `[IsFinite f] [IsDominant f]` | Existing morphism and properties | ROUTE |
| Target affine chart | $U\subseteq Y$ | `U : Y.Opens`, `hU : IsAffineOpen U` | Existing open, not a replacement scheme | ROUTE |
| Whole inverse-image chart | $V=f^{-1}(U)$ | `f ⁻¹ᵁ U` | Affine under finite `f` | ROUTE |
| Base section ring | $A=\Gamma(U,\mathcal O_Y)$ | `Γ(Y, U)` | Actual sections | ROUTE |
| Upstairs section ring | $B=\Gamma(V,\mathcal O_X)$ | `Γ(X, f ⁻¹ᵁ U)` | Actual sections; finite over `A` | ROUTE |
| Section pullback | $f_U^\#:A\to B$ | `(f.app U).hom` | Original scheme map | ROUTE |
| Chart prime of the target point | $\mathfrak p\subset A$ | `(hU.primeIdealOf y).asIdeal` for `y : U` | Existing affine point/prime correspondence | ROUTE |
| Target stalk | $R=\mathcal O_{Y,y}$ | `Y.presheaf.stalk y.val` | Actual local ring | ROUTE |
| Denominator submonoid | $S=A\setminus\mathfrak p$ | `p.primeCompl` | Existing Mathlib submonoid | ROUTE |
| Whole localized finite algebra | $T=S^{-1}B$ | `CommutativeAlgebra.finiteLocalization A B p` | SP107; [FiniteLocalization](../../HodgeConjecture/CommutativeAlgebra/FiniteLocalization.lean) | ROUTE |
| Canonical base action on that algebra | $R\to T$ | `CommutativeAlgebra.finiteLocalization_baseAlgebra A B p R` | SP107; actual localization action, [FiniteLocalizationFractionField](../../HodgeConjecture/CommutativeAlgebra/FiniteLocalizationFractionField.lean) | ROUTE |
| Target maximal ideal | $\mathfrak m_R$ | `IsLocalRing.maximalIdeal R` | Existing Mathlib object | ROUTE |
| Maximal ideals of the semilocal algebra | $\operatorname{MaxSpec}(T)$ | `MaximalSpectrum T` | Finiteness derived in SP106 from finite algebra over a local ring | ROUTE |
| Primes of the upstairs ring over the chart prime | $\{\mathfrak q\subset B:\mathfrak q\cap A=\mathfrak p\}$ | `p.primesOver B` | Existing Mathlib subtype | ROUTE |
| Semilocal maximal-ideal/prime identification | $\operatorname{MaxSpec}(T)\simeq\{\mathfrak q:\mathfrak q\cap A=\mathfrak p\}$ | `CommutativeAlgebra.finiteLocalization_maximalEquiv A B p` | SP107 | ROUTE |
| Double-localization identification | $B_{q\cap B}\simeq_B T_q$ | `CommutativeAlgebra.finiteLocalization_localRingEquiv A B p q` | SP107 | ROUTE |
| Actual point fiber | $f^{-1}(y)$ as a finite set of points | `{x : X // f.base x = y.val}` | SP107; not the scheme-theoretic fiber | ROUTE |
| Upstairs-prime/point-fiber identification | $\{\mathfrak q:\mathfrak q\cap A=\mathfrak p\}\simeq f^{-1}(y)$ | `SchemeCycles.finiteAffine_primesOverEquivFiber f U hU y` | SP107 | ROUTE |
| Maximal-ideal/fiber identification | $\operatorname{MaxSpec}(T)\simeq f^{-1}(y)$ | `SchemeCycles.finiteAffineFiberEquiv f U hU y` | SP107; [FiniteAffineFiber](../../HodgeConjecture/Cycles/FiniteAffineFiber.lean) | ROUTE |
| Source point represented by a maximal ideal | $x_q$ | `(SchemeCycles.finiteAffineFiberEquiv f U hU y q).val` | Same actual point of `X` | ROUTE |
| Source stalk | $P_q=\mathcal O_{X,x_q}$ | `X.presheaf.stalk xq` | Actual local ring; not asserted module-finite over `R` | ROUTE |
| Maximal localization of the semilocal algebra | $T_q$ | `Localization.AtPrime q.asIdeal` | Existing Mathlib localization | ROUTE |
| Actual source-stalk identification | $\mathcal O_{X,x_q}\simeq_B T_q$ | `SchemeCycles.finiteAffineFiber_stalkEquiv f U hU y q` | SP107; section action retained | ROUTE |
| Divisor point above a target divisor point | $x\in X^{(1)},\ f(x)=y\in Y^{(1)}$ | `SchemeCycles.divisorPointOfFiniteFiber k pY f y x` | SP107; existing codimension theory, [FiniteDivisorPoints](../../HodgeConjecture/Cycles/FiniteDivisorPoints.lean) | ROUTE |
| Base function field | $K=K(Y)$ | `Y.functionField` | Original generic stalk | ROUTE |
| Upstairs function field | $L=K(X)$ | `X.functionField` | Original generic stalk | ROUTE |
| Generic pullback | $f^*:K(Y)\hookrightarrow K(X)$ | `SchemeCycles.functionFieldMapOfDominant f` | Existing actual generic-stalk map | ROUTE |
| Base-section germ | $A\to\mathcal O_{Y,y}$ | `(Y.presheaf.germ U y.val y.property).hom` | Existing actual germ | ROUTE |
| Source-section germ | $B\to\mathcal O_{X,x}$ | `(X.presheaf.germ (f ⁻¹ᵁ U) x hx).hom` | Existing actual germ, with `hx : x ∈ f ⁻¹ᵁ U` | ROUTE |
| Canonical stalk embedding in the function field | $\mathcal O_{X,x}\hookrightarrow K(X)$ | `algebraMap (X.presheaf.stalk x) X.functionField` | Existing generic-specialization action | ROUTE |
| Semilocal embedding in the original field | $T\hookrightarrow L$ | `CommutativeAlgebra.FiniteLocalizationFractionField.algebra A B p L` | SP107 scoped algebra instance | ROUTE |
| Prime-local embedding in the original field | $B_{\mathfrak q}\hookrightarrow L$ | `CommutativeAlgebra.AtPrimeFractionField.algebra B L q` | SP106 scoped algebra instance; `q : Ideal B` | ROUTE |
| Scheme function-field norm on units | $N_f:K(X)^\times\to K(Y)^\times$ | `SchemeCycles.functionFieldNorm f` | SP107; [FunctionFieldNorm](../../HodgeConjecture/Cycles/FunctionFieldNorm.lean) | ROUTE |
| Residue field of a local ring | $\kappa(R)=R/\mathfrak m_R$ | `IsLocalRing.ResidueField R` | Existing Mathlib quotient field | ROUTE |
| Maximal quotient upstairs | $T/q$ | `T ⧸ q.asIdeal` | Field because `q` is maximal | ROUTE |
| Actual scheme residue field | $\kappa_X(x)$ | `X.residueField x` | Residue field of the actual stalk | ROUTE |
| Actual residue-field pullback | $f_x^\#: \kappa_Y(fx)\to\kappa_X(x)$ | `(f.residueFieldMap x).hom` | Original scheme residue map | ROUTE |
| Quotient-field weight | $[T/q:\kappa(R)]$ | `Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ q.asIdeal)` | Canonical lying-over action; finite in SP106 | ROUTE |
| Scheme residue degree | $[\kappa_X(x):\kappa_Y(fx)]$ | `SchemeCycles.residueFieldDegree f x` | SP107; uses `(f.residueFieldMap x).hom.toAlgebra`; natural finrank, used as a finite extension degree here | ROUTE |
| Module length | $\ell_R(M)$ | `Module.length R M : ℕ∞` | Existing extended-natural length; SP103--SP106 prove needed finiteness before integer conversion | ROUTE |
| Principal quotient | $B/(b)$ | `B ⧸ Ideal.span {b}` | Actual quotient module/ring | ROUTE |
| Localized principal quotient | $S^{-1}(B/(b))$ | `LocalizedModule S (B ⧸ Ideal.span {b})` | Existing localized module | ROUTE |
| Principal quotient of the localized ring | $(S^{-1}B)/(b/1)$ | `Localization S ⧸ Ideal.span {algebraMap B (Localization S) b}` | Existing quotient of the localized ring | ROUTE |
| Canonical principal-quotient comparison | $S^{-1}(B/(b))\simeq_{S^{-1}B}(S^{-1}B)/(b/1)$ | `CommutativeAlgebra.localizedPrincipalQuotientEquiv B S b` | SP105; [LocalizedPrincipalQuotient](../../HodgeConjecture/CommutativeAlgebra/LocalizedPrincipalQuotient.lean) | ROUTE |
| Local order in a specified fraction field | $\operatorname{ord}_R(g)$ | `SchemeCycles.localOrder R g` | Existing signed order on `g : Kˣ`; domain, Noetherian, dimension-at-most-one hypotheses | ROUTE |
| Lattice in a fraction-field vector space | $M\subset E$ | `M : Submodule R E`, with `[Submodule.IsLattice K M]` | Existing Mathlib lattice predicate | ROUTE |
| Quotient length for two submodules | $\ell_R(M/(M\cap N))$ | `CommutativeAlgebra.submoduleQuotientLength M N` | SP104; quotient is `M ⧸ N.comap M.subtype` | ROUTE |
| Signed relative lattice index | $[M:N]=\ell_R((M+N)/N)-\ell_R((M+N)/M)$ | `CommutativeAlgebra.latticeIndex M N` | SP104; finite-length lattice setting; [LatticeIndex](../../HodgeConjecture/CommutativeAlgebra/LatticeIndex.lean) | ROUTE |
| Automorphism lattice-index homomorphism | $e\mapsto[M:eM]$ | `CommutativeAlgebra.latticeIndexHom R K E M` | SP104; codomain `Multiplicative ℤ` packages additivity | ROUTE |
| Determinant of a field-linear automorphism | $\det_K(e)\in K^\times$ | `LinearEquiv.det e` | Existing Mathlib determinant; [LocalOrderDeterminant](../../HodgeConjecture/Cycles/LocalOrderDeterminant.lean) | ROUTE |
| Field norm | $N_{L/K}:L\to K$ | `Algebra.norm K` | Existing norm for the specified `Algebra K L` | ROUTE |
| Norm restricted to nonzero field elements | $N_{L/K}:L^\times\to K^\times$ | `Units.map (Algebra.norm K)` | Same norm on units | ROUTE |
| Maximal quotient/residue identification | $T/q\simeq\kappa(T_q)$ | `CommutativeAlgebra.maximalQuotientResidueEquiv T (Localization.AtPrime q.asIdeal) q.asIdeal` | SP107; [LocalizedResidueDegree](../../HodgeConjecture/CommutativeAlgebra/LocalizedResidueDegree.lean) | ROUTE |
| Generic stalk/residue identification | $K(X)\simeq\kappa_X(\eta_X)$ | `SchemeCycles.functionFieldResidueEquiv X` | SP107; [FunctionFieldResidue](../../HodgeConjecture/Cycles/FunctionFieldResidue.lean) | ROUTE |
| Residue isomorphism for a map surjective on stalks | $\kappa_Y(fx)\simeq\kappa_X(x)$ | `SchemeCycles.residueFieldEquivOfSurjectiveOnStalks f x` | SP107; requires `[SurjectiveOnStalks f]` | ROUTE |
| Ambient residue/support function-field identification | $\kappa_X(\xi_W)\simeq K(W)$ | `SchemeCycles.supportFunctionFieldResidueEquiv W` | SP107; actual closed inclusion | ROUTE |

The `Algebra` and `IsScalarTower` instances retain the indicated maps.
In particular, `AtPrimeFractionField.algebra` and
`FiniteLocalizationFractionField.algebra`, both in
`HodgeConjecture.CommutativeAlgebra`, embed localizations into the same
original field $L$. They do not introduce replacement function fields.
`finiteLocalization_maximalEquiv` and `finiteLocalization_localRingEquiv`
are the intermediate prime and local-ring comparisons used by the actual
scheme fiber/stalk equivalences above.

#### Comparison statements and finite Chow descent

Here the algebraic norm row uses a finite domain algebra $B/R$, with
$R$ Noetherian local of dimension at most one and the stated fraction-field
scalar towers. The stalk-order rows use the actual finite dominant map and affine chart.
The global divisor identity assumes integral, locally Noetherian,
quasi-compact schemes locally of finite type over a field. The final Chow
maps apply to finite maps of Noetherian schemes with the canonical field
grading; they require neither ambient integrality nor dominance.

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Residue-degree restriction of length | $\ell_R(M)=[\kappa(B):\kappa(R)]\ell_B(M)$ | `CommutativeAlgebra.length_restrictScalars_of_localHom` | SP103; local-map and finite residue-degree hypotheses in [LocalLength](../../HodgeConjecture/CommutativeAlgebra/LocalLength.lean) | ROUTE |
| Semilocal length sum | $\ell_R(M)=\sum_q[B/q:\kappa(R)]\ell_{B_q}(M_q)$ | `CommutativeAlgebra.length_restrictScalars_eq_sum_residueDegree` | SP104; finite support/length hypotheses in [SemilocalLength](../../HodgeConjecture/CommutativeAlgebra/SemilocalLength.lean) | ROUTE |
| Determinant/index comparison | $[M:eM]=\operatorname{ord}_R(\det e)$ | `SchemeCycles.latticeIndex_eq_localOrder_det` | SP104; finite-dimensional vector space and lattice | ROUTE |
| Norm/index comparison | $[M:aM]=\operatorname{ord}_R(N_{L/K}(a))$ | `SchemeCycles.latticeIndex_eq_localOrder_norm` | SP104; finite field extension | ROUTE |
| Full algebraic norm-order identity | $\operatorname{ord}_R(N_{L/K}g)=\sum_q[B/q:\kappa(R)]\operatorname{ord}_{B_q}(g)$ | `SchemeCycles.localOrder_norm_eq_sum` | SP106; [LocalOrderNormFormula](../../HodgeConjecture/Cycles/LocalOrderNormFormula.lean), Stacks 02MJ | ROUTE |
| Norm sum over the actual target stalk | $\operatorname{ord}_y(N_f g)=\sum_q[T/q:\kappa(y)]\operatorname{ord}_{T_q}(g)$ | `SchemeCycles.divisorOrder_norm_eq_sum_finiteAffine` | SP107; [FiniteAffineLocalOrder](../../HodgeConjecture/Cycles/FiniteAffineLocalOrder.lean) | ROUTE |
| Actual stalk-map compatibility | $e_q\circ f_y^\#=(R\to T_q)$, with the point equality inserted | `SchemeCycles.finiteAffineFiber_stalkEquiv_stalkMap` | SP107; [FiniteAffineStalkMap](../../HodgeConjecture/Cycles/FiniteAffineStalkMap.lean) | ROUTE |
| Actual residue-degree comparison | $[T/q:\kappa(y)]=[\kappa_X(x_q):\kappa_Y(fx_q)]$ | `SchemeCycles.finiteAffineFiber_residueDegree` | SP107; [FiniteAffineResidue](../../HodgeConjecture/Cycles/FiniteAffineResidue.lean) | ROUTE |
| Actual source-order comparison | $\operatorname{ord}_{T_q}(g)=\operatorname{ord}_{\mathcal O_{X,x_q}}(g)$ | `SchemeCycles.finiteAffineFiber_localOrder` | SP107; [FiniteAffineStalk](../../HodgeConjecture/Cycles/FiniteAffineStalk.lean) | ROUTE |
| Finite dominant codimension comparison | $\operatorname{codim}_Y f(W)=\operatorname{codim}_X W$ | `SchemeCycles.supportCodimension_finite_dominant k pY f W` | SP107; consequence of existing finite-type dimension formula | ROUTE |
| Norm order over the actual fiber | $\operatorname{ord}_y(N_fg)=\sum_{f(x)=y}[\kappa(x):\kappa(y)]\operatorname{ord}_x(g)$ | `SchemeCycles.divisorOrder_norm_eq_sum_fiber` | SP107; [FiniteAffineLocalOrder](../../HodgeConjecture/Cycles/FiniteAffineLocalOrder.lean) | ROUTE |
| Existing weight equals the residue degree | $d_f(W)=[\kappa_X(\xi_W):\kappa_Y(f\xi_W)]$ | `SchemeCycles.finitePushforwardDegree_eq_residueFieldDegree` | SP107; [FinitePushforwardResidue](../../HodgeConjecture/Cycles/FinitePushforwardResidue.lean) | ROUTE |
| Point coefficient of finite pushforward | $(f_*c)_y=\sum_{f(x)=y}[\kappa(x):\kappa(y)]c_x$ | `SchemeCycles.finitePushforward_apply_pointSupport` | SP107; [FinitePushforwardCoefficients](../../HodgeConjecture/Cycles/FinitePushforwardCoefficients.lean) | ROUTE |
| Finite pushforward of scheme principal divisors | $f_{*,\mathrm{cyc}}\operatorname{div}_X(g)=\operatorname{div}_Y(N_fg)$ | `SchemeCycles.finitePushforward_principalDivisor k pY f g` | SP107; integral, locally Noetherian, quasi-compact schemes locally of finite type over a field | ROUTE |
| Finite pushforward on the existing Chow quotient | $f_*:\mathrm{CH}_n(X)\to\mathrm{CH}_n(Y)$ | `SchemeCycles.chowFinitePushforward k pY f n` | SP107; Noetherian ambient schemes locally of finite type over a field; canonical grading | ROUTE |
| Compatibility with closed carrier inclusions | $f_*\circ i_*=j_*\circ q_*$ when $f\circ i=j\circ q$ | `SchemeCycles.finitePushforward_closedImmersion_square` | SP107; [FinitePushforwardSquare](../../HodgeConjecture/Cycles/FinitePushforwardSquare.lean) | ROUTE |
| Actual image relation identity | $f_*r_{W,g}=r_{f(W),N_{q_W}g}$ | `SchemeCycles.gradedFinitePushforward_principalRelation` | SP107; proved generator identity | ROUTE |
| Integral and rational relation preservation | $f_*\mathcal R_n(X)\subseteq\mathcal R_n(Y)$ | `SchemeCycles.principalRelations_le_comap_finitePushforward`; `SchemeCycles.rationalPrincipalRelations_le_comap_finitePushforward` | SP107; proved span preservation | ROUTE |
| Integral and rational representative squares | $f_*[c]=[f_{*,\mathrm{cyc}}c]$ | `SchemeCycles.chowFinitePushforward_classMap`; `SchemeCycles.rationalChowFinitePushforward_classMap` | SP107; existing quotient class maps | ROUTE |
| Closed-immersion Chow comparison | $i_{*,\mathrm{finite}}=i_{*,\mathrm{closed}}$ | `SchemeCycles.chowFinitePushforward_eq_closedImmersionPushforward` | SP107; same integral Chow map | ROUTE |
| Compatibility with rationalization | $f_*\operatorname{rat}(c)=\operatorname{rat}(f_*c)$ | `SchemeCycles.rationalChowFinitePushforward_rationalize` | SP107; existing integral-to-rational Chow map | ROUTE |

Sources for these comparisons remain [Stacks 02M0](https://stacks.math.columbia.edu/tag/02M0),
[02MI](https://stacks.math.columbia.edu/tag/02MI),
[02MJ](https://stacks.math.columbia.edu/tag/02MJ),
[02C8](https://stacks.math.columbia.edu/tag/02C8), and the finite-map coefficient
reduction in [02RT](https://stacks.math.columbia.edu/tag/02RT). Their citations
are also present in the corresponding Lean module documentation. The
general proper-morphism statement of 02RT is not claimed here.

#### Fixed target and class-dependent construction

The ambient variety, codimension, Chow realization and correspondence
action are fixed before $\alpha$. The index and coefficient of an auxiliary
recipe may depend on $\alpha$ within the prescribed family. The existing
abstract interfaces record that distinction; their interpretation on the
intended smooth projective geometry is a separate obligation.

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Fixed cycle/Hodge model | $\mathscr H=(A,H,H_{\mathrm{Hdg}},\operatorname{cl})$ | `M : RationalHodgeCycleClassModel ChowX HX` | Existing interface, not a completed smooth-projective instantiation | CORE |
| Fixed Hodge subspace | $H_{\mathrm{Hdg}}$ | `M.hodgeClasses` | Supplied independently of cycles | CORE |
| Fixed cycle-class map | $\operatorname{cl}:A\to H$ | `M.cycleClass` | Existing interface field | CORE |
| Varying target class | $\alpha\in H_{\mathrm{Hdg}}$ | `α : HX`, `IsRationalHodgeClass M α` | Class-dependent input | CORE |
| Fixed correspondence action | $\rho:\Gamma\to\operatorname{End}_{\mathbf Q}(\mathbf Q\oplus H)$ | `rho : RationalCorrespondenceAction Gamma (ℚ × HX)`; `rho.action` | Existing interface; held fixed | CORE |
| Graph projector for the class | $P_\alpha(t,x)=(t,t\alpha)$ | `BlockGraphProjector.operator (R := ℚ) α` | Existing linear operator | ROUTE |
| Distinguished-line projector | $P_0(t,x)=(t,0)$ | `BlockGraphProjector.diagonalOperator (R := ℚ) (M := HX)` | Existing linear operator | ROUTE |
| Linear shear | $U_\alpha(t,x)=(t,x+t\alpha)$ | `BlockGraphProjector.shear (R := ℚ) α` | Existing linear equivalence | ROUTE |
| Prescribed auxiliary recipe family | $c\mapsto z_j(c)$ | `recipe : ∀ j, Coeff j →ₗ[ℚ] ChowY j` | Existing parameters; chosen before the class | ROUTE |
| Class-dependent coverage condition | $\forall\alpha\in H_{\mathrm{Hdg}},\ \exists j,c:\operatorname{cl}_j(z_j(c))=\pi_j^*\alpha$ | `ClassDependentChowBettiGeneration M clY pull recipe` | Existing proposition; [UpstairsGeneration](../../HodgeConjecture/Realization/Chow/UpstairsGeneration.lean); not an established geometric generation theorem | ROUTE |
| Normalized downstairs representative | $\deg(\pi_j)^{-1}(\pi_j)_*z_j(c)$ | `((T j).degree : ℚ)⁻¹ • pushCH j (recipe j c)` | Conditional descent theorem with explicit transfer and cycle-class compatibility | ROUTE |

### Construction and input checkpoints (SP17--SP107)

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
| SP83 | Coherent actual affine inverse-image opens | COMPOSE / REFINE / IDENTIFY | Prove actual restriction identities and common-refinement diamonds; identify arbitrary nonempty affine subcharts with their genuine open inverse images using common principal neighborhoods. | PROVED / VALIDATED |
| SP84 | Actual affine normalization diagram and glued scheme | INDEX / REFINE / GLUE | Prove locally directedness for the original inclusion-indexed chart diagram; construct its scheme colimit, original-chart open cover and structural map with exact chart and common-refinement identities. | PROVED / VALIDATED |
| SP85 | Original charts as actual global inverse-image schemes | IDENTIFY / COMPARE / RESTRICT | Prove the global chart image and equality of opens; construct the actual inverse-image scheme isomorphism with both inclusion identities, original structural map to the base chart and restriction naturality. | PROVED / VALIDATED |
| SP86 | Target-local properties and actual finite-etale global normal closure | TRANSFER / SPECIALIZE / RETAIN | Prove the nonempty affine basis covers the base, transfer target-local properties through the exact chart comparisons, derive global affineness, and prove finite etaleness for the original marked normal closure from SP81's explicit normal-stalk inputs. | PROVED / VALIDATED |
| SP87 | Descent of the original marked refinement | FORM COCONE / DESCEND / IDENTIFY | Glue the original marked chart refinements to a map to the actual `Y`; prove its marked chart formulas, global triangle and uniqueness from those chart formulas under finite dominance and normal stalks of `Y` only. | PROVED / VALIDATED |
| SP88 | Finite etaleness of the actual global marked refinement | CANCEL / TRANSFER / RETAIN | Prove finite cancellation for a separated second morphism and use the exact global triangle with SP86 to prove the original marked refinement finite etale under the actual finite-etale and explicit normal-stalk inputs. | PROVED / VALIDATED |
| SP89 | Surjectivity of the original global normalization and marked refinement | LIE OVER / LIFT / RETAIN | Prove global normalization surjectivity for any original function-field extension and directly lift points through the existing marked chart refinements under finite dominance and normal stalks of `Y` only. | PROVED / VALIDATED |
| SP90 | Compatible global normalization and marked-subgroup actions | COMMUTE / DESCEND / PRESERVE | Glue the original inverse-ring chart automorphisms to the same global normalization and prove that the subgroup fixing the marked intermediate field preserves the original refinement, with the same underlying automorphisms. | PROVED / VALIDATED |
| SP91 | Normal local rings of the original glued normalization | CLOSE / LOCALIZE / TRANSFER | Prove integral closedness of the original coordinate rings and affine stalks, then transfer domain and integral-closedness properties through the original chart open immersions to every global local ring. | PROVED / VALIDATED |
| SP92 | Integrality of the original glued normalization | OVERLAP / REDUCE / UNITE | Prove that original chart images intersect, transfer reducedness from the proved domain stalks, and derive irreducibility and integrality of the same global scheme. | PROVED / VALIDATED |
| SP93 | Marked function-field comparison and action faithfulness | IDENTIFY / COMPARE / RETAIN | Compare the original generic stalk with the finite ambient extension independently of charts; preserve the base map and marked refinement, prove inverse-pullback action compatibility and faithfulness. | PROVED / VALIDATED |
| SP94 | Specified upstairs recipes and arbitrary-class generation condition | SPECIFY / NORMALIZE / DESCEND | State fixed and class-dependent recipe generation over the independently supplied Hodge subspace; prove normalized Chow descent using the existing positive-degree transfer and an explicit cycle-class/pushforward square. | PROVED / VALIDATED |
| SP95 | Generic extensionality and the full original deck group | RESTRICT / RECONSTRUCT / IDENTIFY | Detect dominant morphisms by actual generic pullback under relative separatedness; reconstruct every deck transformation through the original finite-extension marking and existing action. | PROVED / VALIDATED |
| SP96 | Full stabilizer of the original marked refinement | FIX / RECONSTRUCT / IDENTIFY | Detect exactly which original field automorphisms preserve the marked refinement; identify its original subgroup action with the full deck group over the cover. | PROVED / VALIDATED |
| SP97 | Actual generic fiber of the original finite dominant map | LOCALIZE / DUALIZE / COMPOSE | Prove the original affine function-field pushout, pass to spectra, and compose with the actual chart pullback to identify the original generic-stalk square. | PROVED / VALIDATED |
| SP98 | Tensor base change of the actual generic fiber | TENSOR / PASTE / RETAIN | Compose the tensor-spectrum square with the actual generic-stalk pullback, preserving the original scalar map, tensor order and both projections for any commutative base-field algebra. | PROVED / VALIDATED |
| SP99 | Original marked split generic fiber | SPECIALIZE / COMPOSE / MARK | Apply the existing normal-closure tensor/sheet equivalence to the actual generic base change, retaining both projections and the original marked point. | PROVED / VALIDATED |
| SP100 | Sheet points and the original normalization action | EVALUATE / LABEL / COMPARE | Identify individual coset evaluations in the existing split fiber with the original generic normalization orbit, preserving both pullback projections and the inverse convention. | PROVED / VALIDATED |
| SP101 | Degree-weighted finite cycle pushforward | IMAGE / WEIGHT / RESTRICT | Use the actual mapped ideal and positive function-field degree to extend closed-immersion pushforward to finite morphisms, retaining compatible existing gradings and coefficient extension. | PROVED / VALIDATED |
| SP102 | Canonical finite-map grading | IDENTIFY / COMPARE / DISCHARGE | Identify the actual residue extension as algebraic, preserve structural transcendence degrees, and discharge the existing finite pushforward's canonical grading premise. | PROVED / VALIDATED |
| SP103 | Local residue-degree length comparison | COMPARE / RESTRICT SCALARS | Identify restricted module length with local length weighted by the actual residue degree. | PROVED / VALIDATED; source and checks in CLAIM_LEDGER |
| SP104 | Semilocal lengths and determinant/norm comparison | LOCALIZE / INDEX / COMPARE | Prove the semilocal length sum, signed lattice index, determinant comparison and norm/principal-quotient length formula. | PROVED / VALIDATED; source and checks in CLAIM_LEDGER |
| SP105 | Localized principal quotients | IDENTIFY / TRANSPORT | Compare the actual localized quotient with the quotient of the localized ring and its local order. | PROVED / VALIDATED; source and checks in CLAIM_LEDGER |
| SP106 | Full weighted local norm-order identity | DERIVE / ASSEMBLE | Derive semilocality and finite residue degrees and prove the signed formula for every nonzero fraction. | PROVED / VALIDATED; scheme assembly and Chow descent were open at SP106, completed in SP107 |
| SP107 | Finite scheme norm/divisor identity and integral/rational Chow descent | TRANSPORT / ASSEMBLE / DESCEND | Identify actual fibers, stalk orders and residue weights; reuse codimension; construct image norm relations and descend the existing cycle maps. | PROVED; FULL BUILD (3265 JOBS), ROOT INVENTORY, 67-DECLARATION AXIOM AUDIT AND SP106 REGRESSION PASS; SEE CLAIM LEDGER |

SP102 (2026-09-29): **canonical finite-map grading**.
One public theorem in `Cycles/FiniteResidueField.lean` and four in
`Cycles/FiniteGrading.lean` correspond to `prop:finite-field-grading`;
the ledger checkpoint is A11ch.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Algebraicity through the literal map `f_x^#:κ_Y(fx)→κ_X(x)` | $f_x^\#: \kappa_Y(fx)\to\kappa_X(x)$ is algebraic | `residueFieldMap_isAlgebraic_of_isFinite` | ROUTE |
| Equality of full structural transcendence-degree cardinals | $\operatorname{trdeg}_k\kappa_Y(fx)=\operatorname{trdeg}_k\kappa_X(x)$ | `residueFieldBase_trdeg_eq_of_isFinite` | ROUTE |
| `δ_{X/k}(x)=δ_{Y/k}(f(x))` for the existing functions | $\delta_{X/k}(x)=\delta_{Y/k}(f(x))$ | `DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite` | ROUTE |
| `deg_{δY}(f(W))=deg_{δX}(W)` | $\deg_{\delta_Y}(f(W))=\deg_{\delta_X}(W)$ | `supportDegree_imageSubscheme_ofLocallyOfFiniteType` | ROUTE |
| The existing `f_{*,cyc}` preserves canonical homogeneous cycles without supplied `hdeg` | $f_{*,\mathrm{cyc}}Z_n^{\delta_X}\subseteq Z_n^{\delta_Y}$ for the canonical gradings | `finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType` | ROUTE |

Residue algebraicity uses only finite `f`, with arbitrary ambient schemes.
Structural cardinal equality adds a field and an arbitrary target structural
map, not local finite type. The dimension and cycle statements add local
finite type of that target map; the source uses its actual composite.
The cycle theorem allows any semiring. The actual structural scalar tower
is established before applying the existing transcendence-degree theorem.
No new scalar-action definition, global instance, field, dimension function,
cycle carrier or pushforward is added. Arbitrary independently chosen
gradings still require SP101's explicit compatibility hypothesis.

The proof reuses affine prime-residue algebraicity and transports through
the actual affine/chart residue comparisons. It does not infer finite or
integral stalk maps. It proves algebraicity, not a new finite-dimensionality
or separability endpoint. This is dimension grading, not an unqualified
codimension-preservation theorem. The next obligation remains the general
length-order principal/norm identity on actual relation carriers and then
Chow descent; no such compatibility is assumed here. Composition, Betti
transfer, the cycle-class square and generation remain separate. No object
is moved or removed. Preserve the full SP101 record below from `41f15b3`.

Residue/grading scoped builds pass 2331/2859 jobs without warnings. The
focused suite passes twenty examples, five checks and five axiom audits;
all observed sets are exactly the standard three. The full build passes
3233 jobs with only the unchanged Challenge warnings at lines 33 and 46.
The dependency audit passes six primary contracts and two supporting
reports. Fresh SP101 regression passes thirty examples, twenty checks and
twenty standard-three axiom audits without warnings. No other fresh
neighbor regression or full historical central replay is claimed.

Independent scope/source review and five-API parity pass. The 97-page PDF
(905084 bytes) has a clean final log and visually checked pages 40, 54, 55,
79 and 90. Central static inventory: 1134 checks, 565 examples, 1026 axiom
reports. Both complete historical prefixes and the SP101-to-EOF queue
record are byte-identical to `41f15b3`. SP102 is validated.

SP101 (2026-09-29): **degree-weighted finite cycle pushforward**.
Thirteen public APIs in `Cycles/FinitePushforward.lean` and seven in
`Cycles/GradedFinitePushforward.lean` correspond to
`prop:finite-cycle-pushforward`; the ledger checkpoint is A11cg.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| The actual integral image `f(W)` | $f(W)$ | `imageSubscheme` | ROUTE |
| Its ideal is literally the existing `I_W.map f` | $\mathcal I_{f(W)}=\ker(\mathcal O_Y\to(f\circ\iota_W)_*\mathcal O_W)$ | `imageSubscheme_val` | ROUTE |
| Agreement with the old closed image | $f(W)$; same closed-image object | `imageSubscheme_eq_closedImageSubscheme` | ROUTE |
| `ξ_{f(W)}=f(ξ_W)` | $\xi_{f(W)}=f(\xi_W)$ | `ambientGenericPoint_imageSubscheme` | ROUTE |
| The original map `q_W:W→f(W)` is finite | $q_W:W\to f(W)$ is finite | `finiteImage_toImage_isFinite` | ROUTE |
| `d_f(W)=[K(W):K(f(W))]` using actual `q_W^*` | $d_f(W)=[K(W):K(f(W))]$ | `finitePushforwardDegree` | ROUTE |
| `0<d_f(W)` | $0<d_f(W)$ | `finitePushforwardDegree_pos` | ROUTE |
| `d_f(W)=1` for a closed support map | $d_f(W)=1$ | `finitePushforwardDegree_of_isClosedImmersion` | ROUTE |
| Linear extension `f_{*,cyc}` on existing finite cycles | $f_{*,\mathrm{cyc}}$ | `finitePushforward` | ROUTE |
| `f_*(r[W])=r d_f(W)[f(W)]` | $f_{*,\mathrm{cyc}}(r[W])=r\,d_f(W)[f(W)]$ | `finitePushforward_single` | ROUTE |
| `f_*[W]=d_f(W)[f(W)]` | $f_{*,\mathrm{cyc}}[W]=d_f(W)[f(W)]$ | `finitePushforward_fundamentalCycle` | ROUTE |
| Equality with the old closed-immersion map | $f_{*,\mathrm{cyc}}$; same map for a closed immersion | `finitePushforward_eq_closedImmersionPushforward` | ROUTE |
| Identity morphism gives identity cycles | $(\mathrm{id}_X)_{*,\mathrm{cyc}}=\mathrm{id}$ | `finitePushforward_id` | ROUTE |
| `deg_δ(f(W))=δ(f(ξ_W))` | $\deg_\delta(f(W))=\delta(f(\xi_W))$ | `supportDegree_imageSubscheme` | ROUTE |
| Preservation of explicitly compatible homogeneous degrees | $f_{*,\mathrm{cyc}}Z_n^{\delta_X}\subseteq Z_n^{\delta_Y}$ under degree compatibility | `finitePushforward_mem_cyclesOfDegree` | ROUTE |
| Restriction of `f_{*,cyc}` to existing degree submodules | $f_{*,\mathrm{cyc}}:Z_n^{\delta_X}\to Z_n^{\delta_Y}$ | `gradedFinitePushforward` | ROUTE |
| Literal equality of underlying cycle maps | $f_{*,\mathrm{cyc}}$; unchanged underlying map | `gradedFinitePushforward_val` | ROUTE |
| Graded agreement with the old map | $i_{*,\mathrm{cyc}}$; same homogeneous closed pushforward | `gradedFinitePushforward_eq_closedImmersionPushforward` | ROUTE |
| Raw integer/rational coefficient square | $f_{*,\mathbf Q}\circ\operatorname{rat}=\operatorname{rat}\circ f_{*,\mathbf Z}$ | `finitePushforward_rationalize` | ROUTE |
| The same square on homogeneous cycles | $f_{*,\mathbf Q}\circ\operatorname{rat}=\operatorname{rat}\circ f_{*,\mathbf Z}$ on homogeneous cycles | `gradedFinitePushforward_rationalize` | ROUTE |

The integral image and its generic-point formula apply to any ambient map.
The degree APIs require only the support composite to be finite; the raw
linear map requires the ambient morphism to be finite. No ambient
integrality, dominance, normality, Noetherianity, etaleness or separability
is added. Finiteness and positivity reuse the actual `toImage`, the existing
finite-cancellation lemma and actual function-field finiteness. Any semiring
of coefficients is allowed. The graded map retains an explicit equality
of source/image support degrees, not a hidden canonical-grading or
codimension theorem. No second cycle carrier, field or relation package
is introduced; closed-image and pushforward agreement are proved.

The next comparison is preservation of the existing structural field
grading by a finite map, followed by the general length-order principal/norm
identity on actual relation carriers. Smoothness and etaleness of the
ambient cover do not make those carriers normal. No general finite Chow
pushforward, norm descent, composition, Betti square or generation theorem
is claimed here. No object is moved or removed. Preserve the entire SP100
record below from `85662d0`.

Raw and graded scoped builds pass 2779/2820 jobs. The corrected focused
suite passes thirty examples, twenty checks and twenty axiom audits;
all observed sets are exactly the standard three, without warnings.
The full build passes 3231 jobs with only the unchanged Challenge warnings
at lines 33 and 46. The dependency audit passes six primary contracts and
two supporting reports. Fresh SP72/SP88 regressions pass 18/20 examples
and eleven/two axiom audits respectively, each observed set exactly the
standard three, without warnings. No other fresh regression or full
historical central replay is claimed.

Independent scope review and twenty-API parity pass. The 96-page PDF
(901510 bytes) has a clean final log and visually checked pages 40, 41,
75 and 88. The central static inventory is 1129 checks, 565 examples and
1021 axiom reports. Both complete historical prefixes and the SP100-to-EOF
queue suffix remain byte-identical to `85662d0`. SP101 is validated.

SP100 (2026-09-29): **sheet points and the original normalization action**.
Four public theorems in `Boundary/Normalization/GenericSplitFiberAction.lean`
correspond to `prop:split-fiber-sheet-action`; the ledger checkpoint is A11cf.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Evaluation point's original cover projection | $\operatorname{pr}_Y \circ \xi _{p,s} = \iota _{\eta _Y} \circ \operatorname{Spec}(\iota _s)$ | `functionFieldNormalClosureSplitFiberIso_eval_fst` | ROUTE |
| Evaluation point's original base projection | $\operatorname{pr}_{N_p} \circ \xi _{p,s} = \operatorname{id}$ | `functionFieldNormalClosureSplitFiberIso_eval_snd` | ROUTE |
| Original sheet embedding equals the inverse-labelled geometric orbit | $\iota _{\eta _Y} \circ \operatorname{Spec}(g \circ \iota ) = \lambda \circ a_{N_p}(g^{-1}) \circ \gamma _{N_p}$ | `functionFieldNormalClosureSheetPoint_eq_normalizationOrbit` | ROUTE |
| Full equality of points in the existing actual pullback | $\xi _{p,gH} = \langle \lambda \circ a_{N_p}(g^{-1}) \circ \gamma _{N_p},id\rangle$ | `functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit` | ROUTE |

The evaluation point is `ξ_{p,s}=ψ_p ∘ Spec(ε_s^{N_p})`, using the
existing `Pi.evalAlgHom`, sheet algebra and SP99 isomorphism. Its projection
formulas need finite dominant formally unramified `p` and integral `X/Y`,
but no normality. The map `γ_{N_p}=ι_{η_Z} ∘ Spec(e_{N_p})` uses the
old function-field comparison; it is an abbreviation, not a new carrier.
It deliberately does not reuse the ring-inclusion notation `j_N`.

The orbit identity into `Y` uses the existing normal-stalk input on `Y`
for `λ`, finite dominance and integrality, but no formal unramifiedness.
Its proof reuses generic-stalk naturality, the old inverse-action field
comparison and the marked field comparison. The original fixing subgroup
removes dependence on the chosen coset representative. The full pullback
identity combines this with the two evaluation formulas and thus uses
formal unramifiedness for SP99's splitting.

No field, evaluator, action, normalization model, comparison isomorphism
or target package is reconstructed. The two module-local instance bridges
reuse existing surjectivity and the actual function-field algebra; there
is no global instance or new separability proof. No base-normality,
Noetherian or perfect-field hypothesis is added. No object is moved or
removed; the full SP99 record below is preserved from `5b0572c`.

This is an individual sheet/orbit comparison, not an unspecified action
on the whole fiber, a `G`-deck action on `Y` for nonnormal `H`, an arbitrary
geometric-fiber classification or a torsor theorem. Next follow the existing
same-cover Chow--Betti work order. The current closed-immersion Chow
pushforward and finite-discrete degree-zero Betti transfer are not the
missing positive-dimensional finite-cover maps. First identify the actual
graded cycle pushforward and its principal/norm descent obligation;
introduce additional fiber machinery only for a named consumer.

Validation passes: scoped build (2795 jobs); corrected focused suite
(18 examples, four checks and four axiom audits); full build (3229 jobs,
only the unchanged Challenge warnings at lines 33 and 46); dependency audit
(six primary contracts and two supporting reports). Fresh SP99/SP93 suites
pass 18/35 examples, four/19 checks and four/19 axiom audits respectively;
SP99's two dependency-direction checks also pass. Every audited declaration
in these three focused suites has exactly the standard three axioms, with
no warnings. No additional neighbor-suite pass or full central replay is
claimed.

Independent scope review and all four API parity checks pass. The final
96-page PDF (898680 bytes) has a clean log and visually checked pages 23,
24, 71 and 84. The central static inventory is 1109 checks, 565 examples
and 1001 axiom reports. The complete central-verification and geometric-audit
prefixes, and the SP99-to-EOF queue suffix, remain byte-identical to
`5b0572c`. SP100 is validated.

SP99 (2026-09-29): **original marked split generic fiber**.
Four public APIs in `Boundary/Normalization/GenericSplitFiber.lean`
correspond to `prop:marked-split-generic-fiber`; the ledger checkpoint is A11ce.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Existing sheet spectrum compared with the actual base change | $\psi _p = \theta _{p,N_p} \circ \operatorname{Spec}(\sigma _{\mathcal N} )$ | `functionFieldNormalClosureSplitFiberIso` | ROUTE |
| Original projection to the cover | $\operatorname{pr}_Y \circ \psi _p = \iota _{\eta _Y} \circ \operatorname{Spec}(j_p)$ | `functionFieldNormalClosureSplitFiberIso_hom_fst` | ROUTE |
| Original projection to the normal-closure base | $\operatorname{pr}_{N_p} \circ \psi _p = \operatorname{Spec}(c_p)$ | `functionFieldNormalClosureSplitFiberIso_hom_snd` | ROUTE |
| Base-sheet point is the lift of the original embedding and identity | $\psi _p \circ b_H = \langle y_\iota ,id\rangle$ | `functionFieldNormalClosureSplitFiberIso_baseSheet` | ROUTE |

Here `p:Y→X` is finite dominant formally unramified, with integral `X/Y`.
The original field map `κ_p` and `D=functionFieldNormalClosureData p` fix
`N_p`, `ι`, `G` and `H`. The tensor splitting is the existing
`D.normalClosureTensorGenericSheetsEquiv`; actual separability is derived.
The maps are `j_p(ℓ)(gH)=g(ι(ℓ))`, `c_p(n)(gH)=n`,
`b_H=Spec(ε_H^{N_p})` and `y_ι=ι_{η_Y} ∘ Spec(ι)`.
The augmentation identity and pullback universal property identify the
marked point, not just its underlying field extension.

There is no second field, tensor algebra, evaluator, splitting, cover,
marking or action. The new isomorphism is precisely the geometric
consumer of SP98 and the old splitting; its projection laws retain the
same maps. No scheme-normality, Noetherian or perfect-base premise is added.
No module is moved or removed. The complete SP98 record below is retained
byte-for-byte from `4cf7b71`.

Next compare individual coset evaluation points with the original
normalization maps and inverse-pullback action. This does not assert a
`G`-deck action on `Y` for nonnormal `H`. Arbitrary geometric fibers,
torsors, actual Chow--Betti maps and generation remain separate; the
target and its explicit construction/detection/factorization inputs are
unchanged.

Separability dependency audit: the original formally unramified cover
supplies both the diagonal construction and separability of its finite
generic extension. `SeparableFunctionField.lean` does not import or use
the project's collision decomposition or sheet-splitting module. A
normalized diagonal element with the multiplication/annihilation laws
does characterize separability for this finite field extension, by the
existing Mathlib criteria; a bare diagonal or arbitrary idempotent does
not. Recovering a hypothesis from an element chosen using that same
hypothesis is not an independent proof. No separability gap is claimed
closed in SP99: it consumes the established actual-map theorem.

SP99 validation: scoped build 2753 jobs; corrected focused suite 18 examples,
four declaration checks, four exact standard-three axiom audits and two
transitive dependency-direction checks. The full build passes 3228 jobs
with only the unchanged Challenge warnings at lines 33 and 46. The endpoint
dependency audit passes six primary contracts and two supporting reports.
Fresh SP98/separability regressions pass 19 examples/one axiom audit and
16 examples/three axiom audits respectively, each observed set exactly the
standard three, without warnings. No other fresh neighbor pass is claimed.

Independent scope review and four-API Lean--TeX parity pass. The 94-page
PDF (893990 bytes) has a clean final log and passes visual review of pages
23, 24, 70 and 82. The central static inventory is 1105 checks, 565 examples
and 997 axiom reports; its historical prefix was not fully re-elaborated.
Both complete historical prefixes and the SP98-to-EOF queue record are
byte-identical to `4cf7b71`. SP99 is validated.

SP98 (2026-09-29): **tensor base change of the actual generic fiber**.
The single public API in `Boundary/Normalization/GenericFiberBaseChange.lean`
matches `cor:generic-fiber-base-change`; the ledger checkpoint is A11cd.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Actual tensor spectrum and base change with both original projections | $\theta _{p,E}: \operatorname{Spec}(E\otimes _K L) \simeq Y \times _X \operatorname{Spec} E$ | `functionFieldMapOfDominant_baseChange_isPullback` | ROUTE |

Here `p:Y→X` is finite dominant with integral source and target;
`K=K(X)`, `L=K(Y)` via `κ_p`, and `E` is any commutative `K`-algebra.
The tensor is `T_E=E⊗_K L`, with `u_E(e)=e⊗1` and `v_E(ℓ)=1⊗ℓ`.
Writing `α_E:K→E` for the structure map and
`β_E=ι_{η_X} ∘ Spec(α_E)`, the first projection is
`ι_{η_Y} ∘ Spec(v_E)` and the second is `Spec(u_E)`.
`θ_{p,E}` denotes the existing `IsPullback.isoPullback`, not another
public Lean object. There is no field, finiteness, separability,
reducedness or nontriviality requirement on `E`.

The proof directly pastes the tensor-spectrum pullback with SP97's
actual generic-stalk square. It adds no replacement carrier, marking,
action, private helper or global instance. Normal-closure specialization,
splitting and the marked augmentation comparison are the next step;
arbitrary geometric fibers, torsors and Chow--Betti generation remain
separate. No object is deleted or archived. The complete SP97 record
below remains unchanged.

SP98 reuse / target-consumer audit (2026-09-29): the new proof only applies
Mathlib's tensor pushout, its spectrum pullback and SP97. It proves a
predicate on the existing maps; it defines no tensor algebra, field,
fiber carrier, evaluator or isomorphism wrapper.

| Existing object or presentation | Owner and role | Audit disposition |
| --- | --- | --- |
| `Y ×_X Spec E` | Existing categorical pullback of the original scheme map | Canonical geometric object; SP98 identifies its tensor presentation |
| `S[image R⁰]` | `GenericFiberAlgebra.lean`, used by the affine dimension/localization branch | Existing localization carrier, not a second `K(Y)` or scheme fiber |
| `⨂_σ L` and its integral-coordinate analogue | `NormalClosureTensor.lean` and `NormalizationTensor.lean` | Many-factor evaluation into the already chosen normal closure and its normalization; not the binary base-change tensor |
| `N⊗_K L ≃ N^{G/H}` | `SelectorComparison.lean` | Reuse the existing splitting and augmentation identity for SP98's next consumer |
| `L⊗_K L` | Existing collision algebra and its evaluation on sheets | Different domain from `N⊗_K L`; do not introduce a third evaluator |

One older consolidation candidate is the comparison of
`collisionToGenericSheets` with the restriction of
`normalClosureTensorToGenericSheets` along `D.embedding ⊗ id`. They have
different domains, so they are not competing objects; any later definition
sharing must first check their consumers and prove compatibility. No removal
or refactor is made in this checkpoint. This is a bounded overlap audit,
not a claim that the entire repository is free of redundancy.

The next consumer is still to be implemented: specialize SP98 to the original
normal closure and apply `Spec` to the existing tensor/sheet equivalence,
preserving the marked augmentation. A new generic algebra theory or a second
coverage witness package is not part of that step. The target equivalences'
construction/detection and prescribed-coverage factorization inputs remain
explicit obligations, not consequences of this fiber comparison.

SP98 validation: scoped build 2738 jobs; corrected focused suite 19 examples,
one declaration check and one exact standard-three axiom audit; full build
3227 jobs with only the unchanged Challenge warnings at lines 33 and 46.
The dependency audit passes six primary contracts and two supporting reports.
The fresh SP97 regression passes 18 examples, two checks and two exact
standard-three axiom audits. No other fresh neighbor-suite pass is claimed.
Production/manuscript/API parity and the bounded overlap audit pass.

The 94-page PDF (891430 bytes) has a clean final log and passes visual review
of pages 9, 10, 11, 70 and 82. The static central inventory is 1101 checks,
565 examples and 993 axiom reports; its historical prefix was not fully
re-elaborated. Both complete historical prefixes and the SP97-to-EOF queue
record are byte-identical to `cd3341a`. SP98 is validated.

SP97 (2026-09-21): **actual generic fiber and affine function-field pushout**.
Two public APIs in `Boundary/Normalization/FiniteFunctionField.lean` and
`Boundary/Normalization/GenericFiber.lean` match
`prop:actual-generic-fiber`; the ledger checkpoint is A11cc.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Original section rings and generic fields form the affine pushout | $A_U \otimes _{B_U} K(X) \simeq K(Y)$ | `functionFieldMapOfDominant_isPushout_of_affine` | ROUTE |
| The actual generic-stalk square is cartesian | $\operatorname{Spec} K(Y) \simeq Y \times _X \operatorname{Spec} K(X)$ | `functionFieldMapOfDominant_isPullback` | ROUTE |

The assumptions are finite dominant `p:Y→X` and integral `X,Y`.
For nonempty affine `U`, the section map and generic germs supply all
algebra structures; their scalar towers are proved. Finiteness, faithful
scalar action and the actual fraction fields give the algebra pushout.
Passing to spectra and composing with the original affine-preimage square
gives the generic-stalk pullback. Its orientation makes the existing
`IsPullback.isoPullback` the comparison to the actual generic fiber, with
the original generic-stalk map and `Spec(κ_p)` as projections. No public
fiber carrier or isomorphism package is added; chart transport is private.

Generic points retain `η_X`; their canonical maps are `ι_{η_X}`.
The manuscript's existing generic-extensionality proof uses the same map
notation. Historical dated records below are preserved unchanged.
No normality, etaleness, separability, Noetherianity or additional degree
input is assumed. This does not yet identify the split generic fiber over
the original normal-closure field, coset labels, all geometric fibers or
a torsor. Those comparisons remain distinct from same-cover Chow--Betti
realization and cycle generation. No object is deleted or archived.

The scoped builds pass 2736 jobs for the affine pushout and 2737 for the
scheme square. The focused suite passes 18 examples, two declaration
checks and two axiom audits, each observed set exactly the standard three,
without warnings. Independent production, manuscript and documentation
scope reviews and both API parity checks pass. The 93-page PDF (887663
bytes) has a clean final log and passes visual review of pages 8, 9, 10,
20, 69 and 81. The central static inventory is 1100 checks, 565 examples
and 992 axiom reports, not a fresh historical central replay. The central
and geometric-audit prefixes and the complete SP96 dated queue record
through end-of-file remain byte-identical to `e6b06a7`.

The full build passes 3226 jobs with only the two unchanged Challenge
warnings at lines 33 and 46. The unchanged dependency audit passes six
primary contracts and two supporting reports. Fresh finite-function-field
and SP96 regressions pass 18 examples/11 axiom audits and 22 examples/six
axiom audits respectively, all actual sets exactly the standard three,
without warnings. No other fresh neighbor-suite pass is claimed.
SP97 is validated.

SP96 (2026-09-20): **full marked stabilizer and marked deck-group comparison**.
Six public APIs in `Boundary/Normalization/GluedNormalClosureStabilizer.lean`
match `thm:normalization-marked-stabilizer`; the ledger checkpoint is A11cb.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Exact stabilizer of the original marked refinement | $\lambda \circ a_N(\sigma ) = \lambda \iff \sigma \in H$ | `gluedNormalizationAutomorphism_comp_toCover_iff` | ROUTE |
| Detect preservation for an arbitrary deck transformation over the base | $\lambda \circ d = \lambda \iff b_N(d) \in H$ | `gluedNormalClosureDeckTransformation_comp_toCover_iff` | ROUTE |
| Faithfulness of the existing marked action | $a_N\restriction_H$ is injective | `gluedNormalClosureMarkedDeckAction_injective` | ROUTE |
| Reconstruct every deck transformation over the original cover | $a_N\restriction_H$ is onto $\operatorname{Aut}_Y(Z_N)$ | `gluedNormalClosureMarkedDeckAction_surjective` | ROUTE |
| Full marked deck group with the original action | $H \simeq \operatorname{Aut}_Y(Z_N)$ | `gluedNormalClosureMarkedDeckEquiv` | ROUTE |
| Same explicit inverse-deck pullback as over the base | $b_N(d)(x) = e_N((d^{-1})^*(e_N^{-1}(x)))$ | `gluedNormalClosureMarkedDeckEquiv_symm_apply` | ROUTE |

Here `p : Y → X` is finite dominant, both schemes are integral and
the stalks of `Y` are integrally closed. The field, embedding, refinement
and action are unchanged. Pulling back `λ ∘ a_N(σ) = λ` and applying
the existing comparison shows that `σ⁻¹` fixes the original embedded
`K(Y)` pointwise, hence so does `σ`. The forward inclusion is SP90.
The full marked equivalence reuses SP95's reconstruction, viewing a
deck transformation over `Y` as one over `X` through `p ∘ λ = μ`.
Viewing the same automorphism over `X` is a private implementation detail,
not another public comparison package or action. No new source input is introduced.

No etaleness, separability, base normality, Noetherianity or finiteness
of `μ` is added to this statement. The full marked deck group does not
by itself identify a geometric fiber with a coset space or prove a
torsor assertion. That is the next geometric checkpoint, before actual
same-cover Chow--Betti transfer and recipe generation. No object is
deleted or archived. The complete SP95 record below remains unchanged.

The 2783-job scoped and 3225-job full builds pass; the full build has
only the two unchanged Challenge warnings at lines 33 and 46. The focused
suite passes 22 examples, six declaration checks and six axiom audits;
each observed axiom set is exactly the standard three, with no warnings.
The 93-page PDF (885899 bytes) has a clean final log and passes visual
review of pages 20, 21, 22, 71 and 84. Independent scope reviews and all
six API parity checks pass. The central static inventory is 1098 checks,
565 examples and 990 axiom reports, not a fresh full central replay.
The central and geometric-audit prefixes and the full SP95 dated queue
record through end-of-file remain byte-identical to `864100b`.

The unchanged dependency audit passes six primary contracts and two
supporting reports. A fresh SP95 regression passes 27 examples, eight
declaration checks and eight exact standard-three axiom audits without
warnings; no other fresh neighbor-suite pass is claimed. SP96 is validated.

SP95 (2026-09-20): **generic extensionality and full deck-group comparison**.
Eight public APIs in `Cycles/FunctionFieldExtensionality.lean` and
`Boundary/Normalization/GluedNormalizationDeckComparison.lean` match
`lem:generic-pullback-extensionality` and
`thm:normalization-full-deck-group`; the ledger checkpoint is A11ca.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| Actual field pullback describes the generic-stalk restriction | $f \circ \eta _V = \eta _W \circ \operatorname{Spec}(f^*)$ | `functionFieldMapOfDominant_fromSpecStalk` | ROUTE |
| Equality of dominant maps over a common base, with relatively separated target | $f^* = g^* \Longrightarrow f = g$ | `eq_of_functionFieldMapOfDominant_eq` | ROUTE |
| Generic pullback determines a deck transformation for arbitrary ambient extension | $d^* = e^* \Longrightarrow d = e$ | `gluedNormalizationDeckTransformation_ext` | ROUTE |
| Recover the base-field automorphism from inverse deck pullback | $b_N(d)$ | `gluedNormalizationDeckFieldAutomorphism` | ROUTE |
| Preserve the actual field marking and inverse convention | $b_N(d)(x) = e_N((d^{-1})^*(e_N^{-1}(x)))$ | `gluedNormalizationDeckFieldAutomorphism_apply` | ROUTE |
| The existing action recovers the original deck map | $a_N(b_N(d)) = d$ | `gluedNormalizationDeckAction_fieldAutomorphism` | ROUTE |
| Every deck transformation comes from the field action | $a_N$ is onto | `gluedNormalizationDeckAction_surjective` | ROUTE |
| Explicit equivalence with the full deck group | $\operatorname{Aut}_{K(X)}(N) \simeq \operatorname{Aut}_X(Z_N)$ | `gluedNormalizationDeckEquiv` | ROUTE |

The generic extensionality theorem retains the common-base square,
integral source/target, dominance and relative separatedness. The
normalization is already integral and affine over its base, so uniqueness
needs neither a finite extension nor separatedness of the base. Finite
`N/K(X)` is used for the original field equivalence and reconstruction;
there is no normality, separability, etaleness or Noetherianity addition.
The full group equivalence uses exactly the old forward action, not a
replacement action or new cover. Its inverse is explicit, not a supplied
comparison witness. The original inverse-ring convention is retained.

The next marked step is the full stabilizer of `λ` under this identified
group. Fiber/coset and torsor comparisons, genuine Chow--Betti maps and
recipe generation are not conclusions of this checkpoint. The pruning
inventory remains dependency-based: the new reverse map has a direct
consumer in the full equivalence, the old action and field comparison
remain its inputs, and no object is deleted or archived.

Production scoped builds pass (2327 jobs for generic extensionality,
2780 for the deck comparison). The focused suite passes 27 examples,
eight declaration checks and eight axiom audits, all actual sets exactly
the standard three. The full build passes 3224 jobs with only the two
unchanged Challenge warnings at lines 33 and 46. The unchanged dependency
audit passes six primary contracts and two supporting reports. A fresh
SP94 rerun passes 26 examples, seven standard-three audits and two
direct-descent dependency assertions; no other fresh neighbor-suite
pass is claimed. Scoped, focused and regression logs have no new warnings.

The single 92-page PDF (882837 bytes) has a clean final log and passes
visual review of pages 19, 20, 21, 70 and 83. Independent production,
manuscript and six-document scope reviews pass. All eight API parity
checks pass; the central static inventory is 1092 checks, 565 examples
and 984 axiom reports, not a fresh full central replay. The central and
geometric-audit prefixes and the complete SP94 dated queue record through
end-of-file remain byte-identical to `05d8601`. SP95 is validated.

SP94 (2026-09-20): **specified upstairs recipes and normalized descent**.
The seven public APIs are in `Realization/Chow/UpstairsGeneration.lean`.
The manuscript counterparts are `def:upstairs-generation` and
`thm:upstairs-generation-descent`; the ledger checkpoint is A11bz and the
target-bridge checkpoint is G2a.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| A fixed linear cycle recipe contains the pullbacks of the independently specified downstairs Hodge subspace | $p_i(\operatorname{Hdg}_X) \subseteq \operatorname{im}(\operatorname{cl}_i \circ r_i)$ | `HodgePullbackGeneratedBy` | ROUTE |
| The Hodge class is prescribed before choosing its recipe coefficient | $\forall \alpha \in \operatorname{Hdg}_X, \exists c, \operatorname{cl}_i(r_i(c)) = p_i(\alpha )$ | `hodgePullbackGeneratedBy_iff` | ROUTE |
| The actual normalized Chow pushforward of an upstairs representative has the prescribed class | $\operatorname{cl}_X(d_i^{-1} s_i(z)) = \alpha$ | `normalizedPushforward_cycleClass` | ROUTE |
| Fixed-recipe generation implies the existing fixed-codimension Hodge target under the explicit transfer laws | $\operatorname{Hdg}_X \subseteq \operatorname{im}(\operatorname{cl}_X)$ | `rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy` | ROUTE |
| A supplied indexed family allows the index and coefficient to vary with the prescribed class | $\forall \alpha \in \operatorname{Hdg}_X, \exists i,c, \operatorname{cl}_i(r_i(c)) = p_i(\alpha )$ | `ClassDependentChowBettiGeneration` | ROUTE |
| One successful fixed recipe supplies the indexed condition | Choose the same $i$ for every $\alpha$ | `classDependentChowBettiGeneration_of_fixed` | ROUTE |
| Class-dependent generation descends through the selected positive-degree transfer | $z_X = d_i^{-1} s_i(r_i(c))$ | `rationalHodgeConjectureAt_of_classDependentChowBettiGeneration` | ROUTE |

The recipe and maps for each index are fixed before quantifying over the
class. Only the pulled-back downstairs Hodge subspace must be generated;
there is no requirement that the recipe, pullback, or a residual realization
be surjective onto the full upstairs space. The upstairs cycle-class map is
a supplied linear map, without an unused upstairs Hodge model. The descent
proof reuses `RationalDegreeTransfer HY HX`: its `pull` goes from downstairs
to upstairs, its `push` goes back, and its positive degree satisfies
`push ∘ pull = d · id`. The separate comparison is
`cl_X ∘ pushCH = push ∘ cl_Y`. The output is the displayed normalized Chow
cycle, not just an abstract projector or range assertion.

No scheme, cover, deck group, correspondence algebra, or projector is added
as a phantom parameter. This checkpoint formalizes and consumes a precise
generation obligation; it does not prove that obligation for arbitrary
smooth projective varieties, construct the requisite Chow--Betti maps, or
turn the desired Hodge conclusion into an axiom. Taking the recipe to be
all upstairs Chow classes is a conditional algebraicity criterion, not an
independent geometric generation mechanism.

The requested order is now: (1) this arbitrary-class condition and its
descent theorem; (2) surjectivity onto the full deck-automorphism group for
the existing normalization action, beyond SP93 faithfulness; (3) genuine
Chow--Betti realization and proof of the generation condition on the chosen
geometric targets. The second task concerns deck automorphisms, not
surjectivity of the recipe or residual map. An actual-cover adapter must
identify its maps with those of a genuine morphism and prove the degree and
cycle-class squares; finite etaleness attached to arbitrary maps would not
do so. This ordering does not make deck-group reconstruction a prerequisite
of the direct normalized-descent theorem.

SP94 scoped and focused validation passes: the production build completes
2466 jobs with a clean log, and the focused file completes with exit zero,
26 examples, seven declaration checks and seven axiom audits, without
warnings or errors. Every actual axiom set is exactly `propext`,
`Classical.choice` and `Quot.sound`. The examples cover fixed and genuinely
class-dependent recipes (all line recipes together generate the rational
plane, but no single line does), non-surjective recipes and pullback, the
strict pulled-back subspace, degree-two normalization, a zero-pullback
counterexample without transfer, and empty-index failure. Both new
sufficient-Hodge endpoints also pass the declaration-level dependency
boundary: they consume the positive-degree law without the normalized
projector or declarations originating in `LinearAlgebra`, `Boundary`, or
`Correspondence` modules. The unchanged six-primary/two-support dependency
regression passes with a clean log. The full build passes 3222 jobs with
only the two unchanged Challenge placeholder warnings at lines 33 and 46;
there are no new production warnings. No fresh neighbor-suite pass is claimed.

The single PDF builds with exit zero to 92 pages and 880675 bytes, with a
clean final LaTeX log; root visual review passes pages 3, 4, 67, 80 and 81.
Read-only review confirms the definition, descent proof and seven-name
registry match the Lean statements. Central verification has static counts
1084 checks, 565 examples and 976 axiom reports; this is not a fresh full
central replay. The complete SP93 dated record through end-of-file remains
byte-identical to `9539dc6`, and whitespace checks pass. The central and
geometric-audit historical prefixes also remain byte-identical to that
commit. Independent scope review of the six current documentation
additions passes; SP94 is validated.

### SP94 bounded pruning inventory: preserve now, prune only with evidence

- **Consumed by direct descent:** `RationalHodgeCycleClassModel`, its
  independently specified Hodge submodule and cycle-class map, the existing
  `RationalDegreeTransfer` degree law, the specified recipe, and the explicit
  cycle-class/pushforward square. No second transfer record or new marked
  coverage object is introduced.
- **Active optional branches, not deletion candidates:** graph-projector
  construction/detection, marked action comparisons and their stronger
  surjective-cancellation endpoints, the two existing Galois coverage
  interfaces, and reverse fixed-deck factorization/replacement. They have
  existing consumers and verification contracts; in particular,
  `research/ProofDependencies.lean` explicitly audits both fixed-deck
  sufficient and iff endpoints. Their stronger hypotheses are not imported
  into the new descent statements.
- **Deferred geometric work, not redundant objects:** global deck-group
  reconstruction, actual positive-dimensional Chow--Betti operations and
  their comparisons, and arbitrary-class generation. Boundary extension,
  idempotence-defect correction and projector realization remain optional
  mechanisms for a selected route, not assumptions of normalized descent.
- **Safe review candidates:** obsolete current-plan prose naming already
  completed localization/gluing/action checkpoints as the next action, and
  future aliases shown by a declaration-level caller audit to have no
  active consumers. Historical dated records and the existing archive are
  provenance, not current next-step instructions. No Lean declaration or
  historical record is moved, archived, or deleted in SP94. Absence from the
  two new endpoint dependency closures alone is not evidence of global
  dead code.

This inventory is deliberately bounded: the existing six-primary/two-support
dependency diagnostic is unchanged. The new focused diagnostic checks
declaration dependencies, not imports, and tests that direct descent uses
the degree law without the normalized projector or declarations originating
in `LinearAlgebra`, `Boundary`, or `Correspondence` modules. A future pruning
change must separately enumerate consumers, preserve mathematical roles and
rerun the affected contracts.

SP93 (2026-09-20): **marked function-field comparison and action faithfulness**.
The 19 public APIs are in `Cycles/FunctionFieldComparison.lean`,
`GluedNormalizationFunctionField.lean`, `GluedNormalizationFunctionFieldAction.lean`
and `GluedNormalClosureFunctionField.lean`. The manuscript counterparts are
`prop:normalization-function-field-comparison` and
`cor:normalization-marked-function-field`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| nonempty open immersion into an irreducible target is dominant | prose only | `openImmersion_isDominant_of_nonempty` | ROUTE |
| actual generic pullback extends the original affine ring map | prose only | `functionFieldMapOfDominant_spec_algebraMap` | ROUTE |
| actual chart pullback identifies generic germs with affine fractions | prose only | `functionFieldMapOfDominant_fromSpec_germ` | ROUTE |
| injective ring map supplies spectrum-map dominance | prose only | `specMap_isDominant_of_injective` | ROUTE |
| canonical fraction-field identification of the original normalization chart | $K(Z_U) \simeq N$ | `affineNormalizationFunctionFieldEquiv` | ROUTE |
| integral coordinates retain their ambient value | prose only | `affineNormalizationFunctionFieldEquiv_algebraMap` | ROUTE |
| chart generic pullback followed by affine fraction comparison | chart computation of $e_N$ | `gluedNormalizationFunctionFieldEquivAt` | ROUTE |
| exact factorization through the original chart pullback | prose only | `gluedNormalizationFunctionFieldEquivAt_apply_chart` | ROUTE |
| comparison unchanged under actual affine restriction | prose only | `gluedNormalizationFunctionFieldEquivAt_restriction` | ROUTE |
| comparison independent of any two original charts | prose only | `gluedNormalizationFunctionFieldEquivAt_eq` | ROUTE |
| comparison preserves the actual structural field embedding | $e_N \mu_N^*$ is the original inclusion | `gluedNormalizationFunctionFieldEquivAt_toBase` | ROUTE |
| canonical algebra equivalence over the actual structural field map | $e_N : K(Z_N) \simeq _{K(X)} N$ | `gluedNormalizationFunctionFieldEquiv` | ROUTE |
| canonical equivalence agrees with every chart computation | prose only | `gluedNormalizationFunctionFieldEquiv_apply_chart` | ROUTE |
| original chart pullback is the inverse field automorphism | prose only | `affineNormalizationFunctionFieldEquiv_automorphism` | ROUTE |
| inverse pullback through every original chart | prose only | `gluedNormalizationFunctionFieldEquivAt_automorphism` | ROUTE |
| canonical equivalence intertwines pullback and inverse action | $e_N a_N(\sigma)^* e_N^{-1} = \sigma^{-1}$ | `gluedNormalizationFunctionFieldEquiv_automorphism` | ROUTE |
| existing global deck action is faithful | $a_N$ is injective | `gluedNormalizationDeckAction_injective` | ROUTE |
| chart comparison retains the original marked embedding | prose only | `gluedNormalClosureFunctionFieldEquivAt_toCover` | ROUTE |
| canonical comparison preserves the actual marked refinement | $e_{N_p} \lambda^* = \iota$ | `gluedNormalClosureFunctionFieldEquiv_toCover` | ROUTE |

For integral `X` and finite `N/K(X)`, retain the actual generic-stalk
map of every original chart and the canonical fraction-field equivalence.
The comparison `e : K(Z_N) ≃ N` is chart-independent, preserves
`mu^*`, and satisfies `e(a_sigma^* b) = sigma^{-1}(e(b))` for the
existing inverse-ring action. Faithfulness follows from this comparison.
The original marked specialization uses finite dominant `p`, integral
`X/Y` and normal stalks of `Y` only, and gives
`e(lambda^* c) = (functionFieldNormalClosureData p).embedding c`.
No normality of `X`, etaleness, separability or Noetherianity is added.

SP93 is validated: all 19 production APIs compile in the 2779-job
scoped build. The focused suite passes 35 examples, 19 declaration checks
and 19 axiom audits; every observed axiom set is exactly the standard
three, with no warnings. The full build passes 3221 jobs with only the
two unchanged Challenge placeholder warnings at lines 33 and 46 and
no new production warnings. The unchanged dependency audit passes six
primary contracts and two support reports without warnings. Fresh
SP92 and SP90 focused reruns pass 24 examples/four audits and 30
examples/15 audits respectively, all with exactly the standard three
axioms and no warnings; no other fresh neighbor-suite pass is claimed.
The 90-page PDF (874726 bytes) has a clean final log and passes visual
review of pages 18, 19, 69, 81 and 82. All 19 API parity checks and
independent Lean--TeX scope review pass. The static central inventory
is 1077 checks, 565 examples and 969 axiom reports; its historical
prefix is unchanged and was not re-elaborated in full.

Next address full deck-group reconstruction and comparison; fiber/torsor
comparison, the full stabilizer of `lambda`, normal stalks from smooth
geometry and Chow--Betti generation remain separate. The complete SP92
dated record and all following history remain byte-identical to `cffbb9e`.

SP92 (2026-09-20): **integrality of the original glued normalization**.
Four APIs in `GluedNormalizationIntegrality.lean` supply integral
structure on the original carrier; the manuscript counterpart is
`prop:normalization-global-integral`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual common refinements witness intersection of original chart images | $\jmath_U(Z_U) \cap \jmath_V(Z_V)$ is nonempty | `normalizationChartToGlued_range_inter_nonempty` | ROUTE |
| domain stalks imply global reducedness | $Z_N$ is reduced | `gluedNormalizationModel_isReduced` | ROUTE |
| overlapping irreducible open chart images give global irreducibility | $Z_N$ is irreducible | `gluedNormalizationModel_irreducibleSpace` | ROUTE |
| reducedness and irreducibility supply the global integral instance | $Z_N$ is integral | `gluedNormalizationModel_isIntegral` | ROUTE |

All four APIs require integral `X` and arbitrary `N/K(X)`, without
algebraicity, finite degree, separability, base normality, Noetherianity
or separatedness. Nonemptiness is proved from an original chart.
The same chart carriers, maps, germs, markings and colimit are retained;
the actual `N_p` specialization needs no normal-stalk premise on either
scheme. The global instance makes the intrinsic function field
available without identifying it with arbitrary `N`.

SP92 is validated: all four production APIs compile in the 2744-job
scoped build. The focused suite passes 24 examples and four exact
standard-three axiom audits without warnings. The full build passes
3217 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings. A fresh rerun of the unchanged SP91
focused suite passes its 24 examples and four exact standard-three
axiom audits without warnings; no other fresh neighbor-suite pass is
claimed. The 89-page PDF (867807 bytes) has a clean final log and passes
visual review of pages 15, 16, 67, 68, 80 and 87. All four exact API
parity checks and independent Lean--TeX review pass. The static central
inventory is 1058 checks, 565 examples and 950 axiom reports; its
historical prefix is unchanged and was not re-elaborated in full.

Next address marked function-field comparison. Faithfulness,
fiber/torsor comparison, normal stalks from smooth geometry and
Chow--Betti generation remain separate. The complete queue suffix
beginning with SP91 below remains byte-identical to `44d8fec`.

SP91 (2026-09-20): **normal local rings of the original glued normalization**.
Four public APIs in `GluedNormalizationNormality.lean` prove normality
of the same scheme through its actual local rings. The manuscript
counterpart is `prop:normalization-global-normal`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| integral closure in a field is integrally closed in its own fraction field | $\operatorname{IntCl}_B(N)$ is integrally closed | `normalizedCoordinateRing_isIntegrallyClosed` | ROUTE |
| prime-localized original affine stalks are integrally closed | $\mathcal O_{\operatorname{Spec}(\operatorname{IntCl}_B(N)),z}$ is integrally closed | `normalizedAffineModel_stalk_isIntegrallyClosed` | ROUTE |
| original chart stalk isomorphisms transfer the domain property globally | $\mathcal O_{Z_N,z}$ is a domain | `gluedNormalizationModel_stalk_isDomain` | ROUTE |
| original chart stalk isomorphisms transfer integral closedness globally | $\mathcal O_{Z_N,z}$ is integrally closed | `gluedNormalizationModel_stalk_isIntegrallyClosed` | ROUTE |

The affine APIs require only a commutative `B`, a field `N`, and an
algebra map `B -> N`. The global APIs require integral `X` and any
extension `N/K(X)`, without algebraicity, finite degree, separability,
normality of `X`, Noetherianity or separatedness. Normality combines
the last two local-ring properties; it introduces no new scheme class
or geometric carrier. The fraction field of the integral closure
embeds into `N` and is not claimed to equal `N`.

The proof uses original spectrum stalk comparisons and chart
open-immersion stalk isomorphisms. Original germs, fields, markings,
chart carriers and the scheme colimit remain fixed. The actual `N_p`
specialization needs no normal-stalk hypotheses on either base or
cover for this normality assertion.

SP91 is validated: all four production APIs compile in the 2743-job
scoped build. The focused suite passes 24 examples and four exact
standard-three axiom audits without warnings. The full build passes
3216 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings; no fresh neighbor-suite pass is claimed.
The 89-page PDF (866193 bytes) has a clean final log and passes visual
review of pages 15, 16, 67, 68 and 80. All four exact API parity checks
and independent Lean--TeX review pass. The static central inventory is
1054 checks, 565 examples and 946 axiom reports; its historical prefix
is unchanged and was not re-elaborated in full.

Next address global integrality and marked function-field comparison.
Faithfulness, fiber comparison, torsor or Galois-cover identification,
normal stalks from smooth geometry and Chow--Betti generation remain
separate. The complete queue suffix beginning with SP90 below remains
byte-identical to `88a5f8b`.

SP90 (2026-09-20): **compatible global normalization and marked-subgroup actions**.
Ten public APIs in `GluedNormalizationAction.lean` descend the
original affine action and package it over the base. Five in
`GluedNormalClosureAction.lean` prove marked compatibility and
package the fixing-subgroup action over the original intermediate
scheme. Manuscript counterparts are
`prop:normalization-global-action` and
`prop:normalization-marked-action`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| original inverse-ring automorphism on an actual chart | $a_U(\sigma)=\operatorname{Spec}(\sigma^{-1}\restriction_{\operatorname{IntCl}})$ | `affineNormalizationChartAutomorphism` | ROUTE |
| compatibility with every actual chart restriction | $a_U(\sigma) j^N_{W,U}=j^N_{W,U} a_W(\sigma)$ | `affineNormalizationChartAutomorphism_naturality` | ROUTE |
| original chart automorphisms form a natural diagram automorphism | $(a_U(\sigma))_U:F_N \simeq F_N$ | `affineNormalizationDiagramAutomorphism` | ROUTE |
| descent to an automorphism of the same scheme colimit | $a_N(\sigma):Z_N \simeq Z_N$ | `gluedNormalizationAutomorphism` | ROUTE |
| exact global-to-chart action comparison | $a_N(\sigma) \jmath_U=\jmath_U a_U(\sigma)$ | `normalizationChartToGlued_comp_automorphism` | ROUTE |
| full action preserves the original base map | $\mu_N a_N(\sigma)=\mu_N$ | `gluedNormalizationAutomorphism_comp_toBase` | ROUTE |
| identity automorphism law | $a_N(1)=\operatorname{id}$ | `gluedNormalizationAutomorphism_one` | ROUTE |
| multiplication with the inverse-ring convention | $a_N(\sigma \tau)=a_N(\sigma) a_N(\tau)$ | `gluedNormalizationAutomorphism_mul` | ROUTE |
| same global maps packaged as an action over `X` | $a_N:\operatorname{Aut}_{K(X)}(N)\to \operatorname{Aut}_X(Z_N)$ | `gluedNormalizationDeckAction` | ROUTE |
| deck packaging retains the underlying global morphism | underlying map of $a_N(\sigma)$ is the constructed $a_N(\sigma)$ | `gluedNormalizationDeckAction_hom` | ROUTE |
| fixing subgroup preserves the original marked affine normalization leg | $c_1\circ\operatorname{Spec}(h^{-1}\restriction_{\operatorname{IntCl}_B(N)})=c_1$ | `normalClosureNormalizationSchemeIso_comp_toIntermediate` | ROUTE |
| marked subgroup preserves each actual affine refinement | $\lambda_U a_U(h)=\lambda_U$ | `affineNormalizationChartAutomorphism_comp_toPreimage` | ROUTE |
| marked subgroup preserves the original global refinement | $\lambda a_{N_p}(h)=\lambda$ | `gluedNormalizationAutomorphism_comp_toCover` | ROUTE |
| fixing-subgroup action over the original `Y` | $a_{N_p}$ restricted to $H$ maps into $\operatorname{Aut}_Y(Z_{N_p})$ | `gluedNormalClosureMarkedDeckAction` | ROUTE |
| marked deck packaging retains the full action's underlying morphism | underlying marked map is $a_{N_p}(h)$ | `gluedNormalClosureMarkedDeckAction_hom` | ROUTE |

All displayed products of maps use ordinary mathematical composition
order. In Lean the multiplication law is written with the `tau` map
followed by the `sigma` map. The inverse-ring convention matches the
existing affine action. Deck packaging and the diagram automorphism
are not new geometric carriers. The same `a_N` notation is used for
the action homomorphism and its evaluated automorphism; no new `rho`
notation competes with the original germs or Betti realization.

The generic ten APIs require integral `X` and any extension `N/K(X)`,
without algebraicity, finite degree or separability. The first marked
API is an affine statement for the existing `NormalClosureData` and
compatible scalar towers; its proof uses inverse fixing and equality
of the original marked ring maps. The four actual marked consumers
need only finite dominant `p`, integral `X` and `Y`, and explicitly
integrally closed stalks of `Y`. They cancel the existing affine
normalization comparison isomorphism and use the exact glued chart
formulas, not cancellation of `p` from the structural triangle.
No etaleness, normal-stalk premise on `X`, Noetherianity or perfectness
is added. Original chart carriers, field markings and germ-derived
scalars are unchanged; no source axiom or geometric input package is
introduced.

SP90 is validated: the generic and combined action scoped builds pass
2743 and 2771 jobs. The focused suite passes 30 examples and 15 exact
standard-three axiom audits without warnings. The full build passes
3215 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings; no fresh neighbor-suite pass is claimed.
The 89-page PDF (864292 bytes) has a clean final log and passes visual
review of pages 17, 18, 19, 67, 68 and 80. All 15 exact API parity
checks and independent Lean--TeX review pass. The static central inventory
is 1050 checks, 565 examples and 942 axiom reports; its historical prefix
is unchanged and was not re-elaborated in full.

Next address global normality. Faithfulness, fiber comparison and a
torsor or Galois-cover identification remain separate. Subgroup
fixing is sufficient for preserving `lambda`, not an exact-stabilizer
or converse theorem. Normal stalks from smooth geometry and
Chow--Betti generation remain separate. The complete queue suffix
beginning at the SP89 block below is preserved byte-for-byte from
`6b2baba`.

SP89 (2026-09-20): **surjectivity of the original global normalization and marked refinement**.
Two public APIs in `GluedNormalizationSurjectivity.lean` prove
surjectivity of the same original global maps with distinct minimal
scopes. The manuscript counterpart is
`prop:normalization-global-surjective`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| normalization over any field extension of the original function field is surjective | $\mu_N:Z_N\to X$ surjective | `gluedNormalizationToBase_surjective` | ROUTE |
| the original marked refinement is surjective by an actual chartwise point lift | $\lambda:Z_{N_p}\to Y$ surjective | `gluedNormalClosureToCover_surjective` | ROUTE |

The first theorem assumes integral `X` and any field extension `N`
of its original `K(X)`. The original chart scalar map
`B -> IntCl_B(N)` is injective and integral. Lying over gives
surjectivity of the chart normalization, and SP86's exact target-local
comparison gives surjectivity of `mu_N`. There is no algebraicity,
finite-degree, normal-base, Noetherian or separatedness premise.
Stacks 00GQ is the existing lying-over citation, not a new source axiom.

The second theorem assumes finite dominant `p : Y -> X`, integral
`X` and `Y`, and explicitly integrally closed stalks of `Y` only.
Each point of `Y` lies in an actual affine inverse image; SP81's
surjective refinement into that whole inverse image lifts the point,
and SP87's exact chart formula gives its image under the original
global `lambda`. No etaleness or normal-stalk hypothesis on `X` is
used. The proof does not infer surjectivity of `lambda` from that of
`p lambda`, which would not be a valid cancellation argument.

The consequence that both global maps are finite etale and surjective
under SP86/SP88's stronger hypotheses uses the existing property
theorems and these two new APIs; it is not a third new public API.
The original field, marked maps, normalization carriers and
germ-derived scalars are unchanged. No source axiom or geometric
input package is introduced.

SP89 is validated: both production APIs compile in the 2772-job scoped
build. The focused suite passes 24 examples and two exact standard-three
axiom audits without warnings on its first run. The full build passes
3213 jobs with only the two unchanged Challenge placeholder warnings.
The unchanged dependency audit passes six primary contracts and two
support reports without warnings. No fresh neighbor-suite pass is
claimed. The 87-page PDF (859905 bytes) has a clean final log and passes
visual review of pages 17, 18, 66, 78 and 86. Both exact API parity
checks and independent Lean--TeX review pass. The static central
inventory is 1035 checks, 565 examples and 927 axiom reports; its
historical prefix is unchanged and was not re-elaborated in full.

Next descend the compatible Galois action. Its full group is over
`X`, and only the subgroup fixing the marked `K(Y)` preserves
`lambda`. Global normality can be a separate bounded follow-up;
normal stalks from smooth geometry and Chow--Betti generation remain
separate. The complete queue suffix beginning at the SP88 block below
is preserved byte-for-byte from `e910f25`.

SP88 (2026-09-20): **finite etaleness of the actual global marked refinement**.
Two public APIs in `FiniteEtaleGluedRefinement.lean` prove a generic
finite-cancellation lemma and its actual finite-etale refinement
consumer. The manuscript counterpart is
`cor:normal-closure-refinement-finite-etale`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| a finite composite with separated second morphism has finite first morphism | $g f$ finite and $g$ separated imply $f$ finite | `isFinite_of_comp_of_isSeparated` | ROUTE |
| the original global marked refinement is finite etale under the stated geometric inputs | $\lambda:Z_{N_p}\to Y$ finite etale | `gluedNormalClosureToCover_finite_etale` | ROUTE |

The generic result does not require `g` finite, integral schemes,
normality, Noetherianity or a field. Its Lean proof uses the graph
closed immersion and the finite base change of the composite; no
generic postcomposition-property instance is added. The manuscript
states and cites this standard input via Stacks 035D rather than
repeating a proof. Stacks 02GW supplies the etale-cancellation citation.

The actual specialization assumes integral `X` and `Y`, dominant
finite etale `p : Y -> X`, and explicitly integrally closed stalks
of both schemes. SP87's exact `p lambda = mu_(N_p)` triangle and
SP86's finite-etale `mu_(N_p)` supply the composite. Finite `p` is
separated, so finite cancellation applies; etaleness follows from
`IsEtale.of_comp`. The definition of `lambda` retains SP87's weaker
finite-dominant and `hY` hypotheses. The proof neither re-glues nor
replaces the original charts, normalization carrier, field marking
or scalar maps, and introduces no source axiom.

SP88 is validated: both production APIs compile cleanly on the first
2773-job scoped build. The focused suite passes 20 examples and two
exact standard-three axiom audits without warnings on its first run.
The full build passes 3212 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. No fresh neighbor-suite
pass is claimed. The 86-page PDF (856518 bytes) has a clean final log
and passes visual review of pages 16, 17, 65, 77 and 84. Both exact
API parity checks and independent Lean--TeX review pass. The static
central inventory is 1033 checks, 565 examples and 925 axiom reports;
its historical prefix is unchanged and was not re-elaborated in full.

Next prove surjectivity and descend the compatible Galois action.
The full group acts over `X`; only the subgroup fixing the marked
`K(Y)` preserves `lambda`. Global normality, normal stalks from smooth
geometry and Chow--Betti generation remain separate. The complete
queue suffix beginning at the SP87 block below is preserved
byte-for-byte from `af73385`.

SP87 (2026-09-20): **descent of the original marked refinement**.
Five public APIs in `GluedNormalClosureRefinement.lean` construct the
cocone of original affine refinements, its colimit map to `Y`, and the
exact marked chart formula, global factorization and uniqueness from
the fixed chart maps. The manuscript counterpart is
`prop:normal-closure-marked-refinement`.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| original marked affine maps, composed with their target-chart inclusions, form a cocone to `Y` | $(\iota_{V_U} \lambda_U)_U$ | `affineNormalClosureRefinementCocone` | ROUTE |
| descent to the actual intermediate scheme | $\lambda:Z_{N_p}\to Y$ | `gluedNormalClosureToCover` | ROUTE |
| exact original marked chart restriction | $\lambda \jmath_U = \iota_{V_U} \lambda_U$ | `normalizationChartToGlued_comp_toCover` | ROUTE |
| original structural map factors through the actual intermediate cover | $p \lambda = \mu_{N_p}$ | `gluedNormalClosureToCover_comp_toBase` | ROUTE |
| uniqueness from the fixed marked chart formulas, not the triangle alone | $(\forall U,\ f\circ\jmath_U=\iota_{V_U}\circ\lambda_U)\Longrightarrow f=\lambda$ | `gluedNormalClosureToCover_unique` | ROUTE |

Here `V_U = p^-1(U)` and `iota_(V_U) : V_U -> Y` is the actual open inclusion. The formulas
use ordinary mathematical composition order, while Lean writes
composition from left to right with `≫`. The original marked normal
closure `N_p`, normalization carriers and germ-derived scalar maps
remain unchanged. The existing restriction square supplies cocone
naturality, and the colimit mapping property supplies its descent;
there is no new source axiom or geometric hypothesis package.

The minimal hypotheses are integral `X` and `Y`, finite dominant
`p : Y -> X`, and explicitly integrally closed stalks of `Y` only.
No etaleness, normal-stalk input on `X`, Noetherianity or perfectness
is assumed. This construction does not assert finite etaleness or
surjectivity of the global refinement.

The manuscript's existing `prop:normalization-localization` geometric
paragraph is aligned with its actual SP82 restriction theorem: finite
dominant `p`, integral `X` and `Y`, and normal stalks of `Y` suffice.
Removing the previously stronger incidental assumptions in that
paragraph introduces no new Lean theorem or duplicate object.

SP87 is validated: all five production APIs compile cleanly in the
2769-job scoped build. The focused suite passes 24 examples and five
exact standard-three axiom audits without warnings on its first run.
The full build passes 3211 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. No fresh older
neighbor-suite pass is claimed. The 86-page PDF (854782 bytes) has a
clean final log and passes visual review of pages 13, 14, 16, 17, 65
and 77. All five exact API parity checks and independent Lean--TeX
review pass. The static central inventory is 1031 checks, 565 examples
and 923 axiom reports; its historical prefix is unchanged and was not
re-elaborated in full.

Next prove the applicable global properties of the refinement and
descend the Galois action. The full group `G` acts over `X`, whereas
only the subgroup `H` fixing the marked `K(Y)` preserves `lambda`.
Global normality and surjectivity, normal stalks from smooth geometry
and Chow--Betti generation remain separate. The complete queue suffix
beginning at the SP86 block below is preserved byte-for-byte from
`30fe0ae`.

SP86 (2026-09-19): **target-local properties and actual global finite-etale normal closure**.
Five public APIs in `GluedNormalizationProperties.lean` prove the
nonempty affine basis cover, the generic target-local property
equivalence, global affineness, and exact finite/etale equivalences.
One public API in `FiniteEtaleGluedNormalClosure.lean` applies the
chartwise SP81 result to the actual marked normal closure and proves
finite etaleness of its already constructed global map.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| all nonempty affine opens cover any scheme, including the empty scheme | $\bigcup_{U\in\mathcal A^\times(X)}U=X$ | `nonemptyAffineChart_iSup_eq_top` | ROUTE |
| transfer a target-local morphism property through the exact original chart comparison | $P(\mu_N)\iff\forall U,\ P(\pi_U)$ | `gluedNormalizationToBase_property_iff` | ROUTE |
| the actual glued structural map is affine | $\mu_N:Z_N\to X$ affine | `gluedNormalizationToBase_isAffineHom` | ROUTE |
| exact finiteness comparison with original normalization chart maps | $\mu_N$ finite iff every $\pi_U$ is finite | `gluedNormalizationToBase_isFinite_iff` | ROUTE |
| exact scheme-etaleness comparison with the same chart maps | $\mu_N$ etale iff every $\pi_U$ is etale | `gluedNormalizationToBase_isEtale_iff` | ROUTE |
| finite etaleness for the actual marked normal-closure global map | $\mu_{N_p}:Z_{N_p}\to X$ finite etale | `functionFieldNormalClosure_glued_finite_etale` | ROUTE |

Here `P` denotes the manuscript's target-local property `mathsf P`,
and `pi_U : Z_U -> U` is the original normalization structural map,
not its composite with `U -> X`. The fixed comparison `e_U` identifies
it with the restriction of `mu_N`. The local scalar helper retains
the original germ-derived algebra map and is not another public
mathematical object. The nonempty affine cover is generic for any
scheme, so no empty-chart normalization is added.

The generic property and affineness results require only integral `X`
and a fixed extension of its original function field. The actual
finite-etale specialization requires dominant finite etale
`p : Y -> X`, integral `X` and `Y`, and explicitly integrally closed
stalks on both schemes. Its `N_p` is the same marked normal closure
in `AlgebraicClosure K(Y)`, with the original generic map from `p`.
SP81 supplies the chart properties; the new target-local equivalences
transport them. No Noetherian, perfect-field or separatedness premise,
new source axiom, or replacement normalization carrier is introduced.

The manuscript counterparts are `prop:normalization-target-local`
and `cor:normal-closure-global-finite-etale`. Stacks 01S8, 01WI and
02GJ provide target-locality background; they do not assert finite
etaleness of an arbitrary field-extension normalization or discharge
the actual specialization's normal-stalk inputs.

SP86 is validated: all six production APIs compile cleanly in the
2770-job scoped build. The focused suite passes 31 examples and six
exact standard-three axiom audits without warnings. The full build
passes 3210 jobs with only the two unchanged Challenge placeholder
warnings. The unchanged dependency audit passes six primary contracts
and two support reports without warnings. No fresh older neighbor-suite
pass is claimed. The 86-page PDF (852527 bytes) has a clean final log
and passes visual review of pages 15, 16, 65, 77, 82, 83 and 84. All
six exact API parity checks and independent Lean--TeX review pass.
The static central inventory is 1026 checks, 565 examples and 918 axiom
reports; its historical prefix is unchanged and was not re-elaborated
in full.

Next descend the marked refinement and compatible Galois action.
Global normality and surjectivity, normal stalks from smooth geometry
and Chow--Betti generation remain separate. The complete queue suffix
beginning at the SP85 block below is preserved byte-for-byte from
`7fca0b4`.

SP85 (2026-09-19): **original normalization charts as global inverse images**.
Seven public APIs in `GluedNormalizationChart.lean` prove the exact
global chart range as sets and opens, construct the corresponding
scheme isomorphism, and retain the actual inclusions, original
normalization map to the base chart and chart restriction maps.

For the reverse range inclusion, the original open cover lifts a global
point into `Z_V`. A common principal neighborhood in `U` and `V` lifts
it to `Z_W` by the exact transition range, and transition naturality
places it in `jmath_U(Z_U)`. The forward inclusion is the original
structural formula. The open-immersion isomorphism onto its range then
gives the actual inverse-image comparison; no replacement chart or
normalization model is introduced.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| exact image of an original chart in the glued scheme | $\operatorname{range}(\jmath_U)=\mu_N^{-1}(U)$ | `normalizationChartToGlued_range` | ROUTE |
| same equality as opens of the glued scheme | $\operatorname{opensRange}(\jmath_U)=\mu_N^{-1}(U)$ | `normalizationChartToGlued_opensRange` | ROUTE |
| actual inverse-image open-subscheme isomorphism | $e_U:Z_U \simeq \mu_N^{-1}(U)$ | `normalizationChartPreimageIso` | ROUTE |
| forward comparison retains the original inclusion | $\kappa_U e_U=\jmath_U$ | `normalizationChartPreimageIso_hom_comp_inclusion` | ROUTE |
| inverse comparison retains the open inclusion | $\jmath_U e_U^{-1}=\kappa_U$ | `normalizationChartPreimageIso_inv_comp_chart` | ROUTE |
| restricted global map is the original normalization map to `U` | $(\mu_N\restriction_U)\circ e_U=\pi_U$ | `normalizationChartPreimageIso_hom_comp_restrict` | ROUTE |
| restriction square for actual inverse-image opens | $e_U j^N_{W,U}=\kappa_{W,U} e_W$ | `normalizationChartPreimageIso_naturality` | ROUTE |

Here `kappa_U` denotes the inclusion of the actual open `mu_N^-1(U)`
in `Z_N`, `kappa_{W,U}` its inclusion for a smaller base chart, and
`pi_U` the original normalization map to `U`. None is a replacement
normalization chart. The local helper algebra instance retains the
original germ-derived scalars and is not another public mathematical
object. Integral `X` and the fixed field extension remain the only
ambient hypotheses. No finite-degree, normality, Noetherianity,
separatedness or affine-intersection premise is added.

The manuscript counterpart is `prop:normalization-global-chart`.
Stacks 01LH supplies relative basis-gluing context; the seven project
APIs are proved for the already constructed scheme using existing
Mathlib open-immersion/range APIs. No source axiom is introduced.

SP85 is validated: all seven production APIs compile cleanly in the
2743-job scoped build. The focused suite passes 29 examples and seven
exact standard-three axiom audits without warnings. The full build
passes 3208 jobs with only the two unchanged Challenge placeholder
warnings. The unchanged dependency audit passes six primary contracts
and two support reports without warnings. No fresh neighbor-suite pass
is claimed. The 84-page PDF (848404 bytes) has a clean final log and
passes visual review of pages 15, 16, 64, 65, 75, 76 and 84. All seven
exact API parity checks and independent Lean--TeX review pass. The
static central inventory is 1020 checks, 565 examples and 912 axiom
reports; its historical prefix is unchanged and was not re-elaborated
in full.

Next use `e_U` and its exact structural formula for target-local
`IsAffineHom` and finite/etale transfer under the appropriate hypotheses,
then descend the marked refinement and compatible Galois action.
Global normality, normal stalks from smooth geometry and Chow--Betti
generation remain separate. No section-ring model on a non-affine
intersection is substituted for its geometric overlap. The SP84 block
and all queue history below are preserved byte-for-byte from `2a4a52a`.

The SP84 neighbor verification was attempted, but its final tool output
was not retained after interruption and no saved log is available.
It is unconfirmed and excluded from this checkpoint's passing counts.
The SP84, SP83 and SP81 verification files are statically byte-identical
to the baseline; their historical results below are not fresh reruns.

SP84 (2026-09-19): **actual affine normalization diagram and glued scheme**.
Seven public APIs in `AffineNormalizationDiagram.lean` index all actual
nonempty affine opens, retain their nonemptiness, construct the original
normalization functor and structural cocone, derive open-immersion maps
and exact ranges, and prove locally directedness. Nine public APIs in
`GluedNormalization.lean` construct the scheme colimit, its original-chart
open cover and descended structural map, with exact restriction,
naturality, point-identification and mapping-extensionality laws.

The nonempty affine index is small and thin by its inherited inclusion
order. Equal images in an upper chart have the same original base point;
a neighborhood principal in both base charts gives a common smaller
chart. SP83's exact range lifts one point, and injectivity in the upper
chart proves the second equality. A global upper affine chart for every
pair is not assumed. Integral `X` and the fixed extension of its original
function field suffice; no normality, finite degree, Noetherianity,
separatedness or affineness of intersections is added.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| inclusion-ordered actual nonempty affine opens | $\mathcal A^\times(X)$ | `NonemptyAffineChart` | ROUTE |
| inherited nonemptiness instance | $U\ne \varnothing$ for $U in \mathcal A^\times(X)$; no new object | `nonemptyAffineChart_nonempty` | ROUTE |
| existing normalization objects and actual restrictions as a functor | $F_N$, $F_N(U)=Z_U$, $F_N(W\leq U)=j^N_{W,U}$ | `affineNormalizationDiagram` | ROUTE |
| original structural maps to `X` | $c_N=(\mu_U)_U$ | `affineNormalizationBaseCocone` | ROUTE |
| open-immersion instance for each transition | existing $j^N_{W,U}$ | `affineNormalizationDiagram_isOpenImmersion` | ROUTE |
| exact transition inverse-image range | $\operatorname{range}(j^N_{W,U})=\mu_U^{-1}(W)$ | `affineNormalizationDiagram_range` | ROUTE |
| proved common-refinement criterion | locally directed $F_N$ | `affineNormalizationDiagram_isLocallyDirected` | ROUTE |
| actual scheme colimit | $Z_N=\operatorname{colim} F_N$ | `gluedNormalizationModel` | ROUTE |
| canonical inclusion of each original chart | $\jmath_U:Z_U\to Z_N$ | `normalizationChartToGlued` | ROUTE |
| canonical chart open-immersion instance | existing $\jmath_U$ | `normalizationChartToGlued_isOpenImmersion` | ROUTE |
| original-chart open cover | $(\jmath_U)_{U\in\mathcal A^\times(X)}$ | `gluedNormalizationOpenCover` | ROUTE |
| structural map induced by the original cocone | $\mu_N:Z_N\to X$ | `gluedNormalizationToBase` | ROUTE |
| exact original structural formula | $\mu_N \jmath_U=\mu_U$ | `normalizationChartToGlued_comp_toBase` | ROUTE |
| restriction compatibility of chart inclusions | $\jmath_U j^N_{W,U}=\jmath_W$ | `normalizationChartToGlued_naturality` | ROUTE |
| chart points agree exactly through a common smaller chart | $\jmath_U(a)=\jmath_V(b)\iff\exists(W,w)$ with the two prescribed images | `normalizationChartToGlued_eq_iff` | ROUTE |
| maps out of the glued scheme are determined on charts | $(\forall U,\ f\circ\jmath_U=g\circ\jmath_U)\Longrightarrow f=g$ | `gluedNormalization_hom_ext` | ROUTE |

The local helper scalar instance only retains the original germ-derived
algebra map; it is not an additional public mathematical object.
The manuscript counterpart is `prop:normalization-gluing`. Stacks 01JB
and 01JC supply standard gluing background; Mathlib's locally directed
scheme gluing is applied to the project-proved instance. The specific
normalization refinement argument is not delegated to those sources.
No input axiom or replacement local normalization is introduced.

SP84 is validated: both production modules compile cleanly in
2741/2742-job scoped builds. The focused suite passes 40 examples and
16 exact standard-three axiom audits. With the unchanged SP83, SP82
and SP81 suites, the total is 125 examples and 73 audits, all clean.
The full build passes 3207 jobs with only the two unchanged Challenge
placeholder warnings. The unchanged dependency audit passes six primary
contracts and two support reports without warnings. The 84-page PDF
(845594 bytes) has a clean final log and passes visual review of pages
14, 15, 63, 64, 75, 76 and 82. All 16 API parity checks and independent
Lean--TeX review pass. The static central inventory is 1013 checks,
565 examples and 905 reports; its historical prefix is unchanged and
was not re-elaborated in full.

Next identify each global chart image with `mu_N^-1(U)`, transfer the
appropriate finite/etale properties, and descend the marked refinement
and compatible Galois action. Global normality, normal stalks from smooth
geometry and Chow--Betti generation remain separate. A section-ring
model on a non-affine intersection is not substituted for the geometric
overlap. The SP83 block and all queue history below are preserved
byte-for-byte from `5e16059`.

SP83 (2026-09-19): **coherent actual affine inverse-image opens**.
Ten production APIs compile without warnings in the 2740-job scoped
build. `AffineNormalizationCoherence.lean` proves actual identity,
composition and common-refinement diamonds, compatibility over `X`,
the principal image over `X`, and two equal-principal-presentation
adapters. `AffineNormalizationOpenImmersion.lean` proves pointwise
injectivity, open immersion and the exact image for every nested
nonempty affine inclusion `W <= U`.

The original `Z_U`, fixed field `N` and germ-derived scalar maps are
unchanged. Common principal neighborhoods give both lifts in the
injectivity argument, local open immersions, and both image inclusions.
There is no separatedness, affine-intersection, normality, Noetherianity
or finite-degree assumption. Identity/composition/diamonds are proved
even on non-affine nonempty opens as identities of the existing models;
the geometric inverse-image conclusion is restricted to affine charts.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual identity, chain and common-refinement equalities | existing $j^N_{W,U}$, $j^N_{W,U} j^N_{T,W}=j^N_{T,U}$ | `affineNormalizationRestriction_self`, `_trans`, `_diamond` | ROUTE |
| original structural square | $\mu_U j^N_{W,U}=\mu_W$; $\mu_U$ is the existing structural map to $X$, not a new carrier | `affineNormalizationRestriction_comp_toX` | ROUTE |
| principal/equal-principal comparison adapters | existing $j^N_{Q,U}$, $\mu_U^{-1}(Q)$; no separate object notation | `affineNormalizationRestriction_basicOpen_range`, `_range_of_eq_basicOpen`, `_isOpenImmersion_of_eq_basicOpen` | ROUTE |
| genuine arbitrary-affine inverse-image identification | $Z_W \simeq \mu_U^{-1}(W)$ via the existing $j^N_{W,U}$ | `affineNormalizationRestriction_injective`, `_isOpenImmersion`, `_range` | ROUTE |

The common-principal-neighborhood input is Stacks 01IW, checked in its
exact scope, and Mathlib `exists_basicOpen_le_affine_inter`. The
manuscript cites its statement without repeating its proof. No input
axiom, geometric package or replacement normalization is introduced.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

Next package the nonempty affine-open diagram and prove its locally
directed common-refinement condition, then glue and descend the marked
maps and Galois action. This checkpoint does not identify a section-ring
model on a non-affine intersection with the geometric overlap or build
a global gluing object. Normal stalks from smooth geometry and
Chow--Betti generation remain separate. The SP82 block and all queue
history below are preserved byte-for-byte.

Exact validation: `AffineNormalizationCoherenceVerification` 21/10,
unchanged `NormalizationLocalizationVerification` 39/28, and unchanged
`FiniteEtaleNormalClosureVerification` 25/19. All runs have zero warnings
or errors. The full build's only warnings are the unchanged Challenge
placeholders at lines 33 and 46. The final PDF log has no warnings,
undefined references/citations or overfull/underfull boxes; visual review
covers pages 14, 15, 62, 63, 74, 80 and 83. Lean--TeX scope and notation
match the ten checked APIs. Each has exactly one appended central check
and axiom report and one entry in the duplicate-free enforced audit.
No new production axioms, placeholders or native-decision escapes occur.
The central verification and audit 0018 prefixes and the SP82-to-end
queue suffix are byte-identical to `817bee2`. `ProofDependencies` and
both neighboring diagnostic files are unchanged. All earlier validation
records retain their original scope.

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| existing integral-closure inclusion and strict same-ambient laws | \(\rho^E_{B,C}:T_B(E)\to T_C(E)\); \(T_B(E)=\operatorname{IntCl}_B(E)\) is local shorthand, not a second object | `normalizationBaseChangeMap`, `_coe`, `_injective`, `_self`, `_trans`, `_naturality` | ROUTE |
| actual localization and tensor comparison preserving ambient scalars | \(C\otimes_B T_B(E)\simeq T_C(E)\) | `normalizedCoordinateRing_isLocalization`, `normalizationLocalizationBaseChangeEquiv`, `_tmul` | ROUTE |
| contravariant map and structural/naturality/composition laws | \(j^E_{B,C}=\operatorname{Spec}(\rho^E_{B,C})\); laws are prose only | `normalizationBaseChange`, `_comp_toBase`, `_naturality`, `_self`, `_trans` | ROUTE |
| principal localization and exact original-basic-open inverse-image range | existing \(j^E_{B,B_f}\), \(\mu_E^{-1}(D(f))\) | `normalizedCoordinateRing_isLocalizationAway`, `normalizationBaseChange_isOpenImmersion`, `_range` | ROUTE |
| derived compatibility of actual restrictions, germs and ambient actions | existing section maps and ambient fields; prose only | `sectionRestriction_functionFieldScalarTower`, `sectionRestriction_ambientScalarTower`, `finiteAffinePreimageRestriction_functionFieldScalarTower` | ROUTE |
| actual normalization restriction and principal-open specialization | \(j^N_{W,U}:Z_W\to Z_U\), using the same \(N\) | `affineNormalizationRestriction`, `_comp_toBase`, `_comp_toChart`, `_basicOpen_isLocalization`, `_basicOpen_isOpenImmersion` | ROUTE |
| naturality of the existing whole-preimage normalization isomorphism | existing \(\nu_{p,U},\nu_{p,W}\); inclusions \(\iota,\widetilde\iota\) | `finiteAffinePreimageNormalizationIso_restriction` | ROUTE |
| actual structural and marked-refinement restriction squares | \(\pi_U\circ j^N_{W,U}=\iota\circ\pi_W\), \(\lambda_U\circ j^N_{W,U}=\widetilde\iota\circ\lambda_W\) | `finiteEtaleAffineNormalClosureToChart_restriction`, `finiteEtaleAffineNormalClosureToPreimage_restriction` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| generic finite-tensor stability and actual scheme-etale source | existing \(P_B\); prose only | `piTensorProduct_ringHomProperty`, `piTensorProduct_isEtale` | ROUTE |
| selected open component and its scheme-etale structural composite | existing \(\operatorname{Spec}(\operatorname{ev}_B)\) and normalization structural map | `NormalClosureData.normalizationTensorEvaluation_isOpenImmersion`, `.normalizationToBase_isEtale_of_etaleModel` | ROUTE |
| finite-etale normal-closure ring of the actual chart | existing \(B_U,A_U,\widetilde B_N\) | `functionFieldNormalClosure_normalization_finite_etale` | ROUTE |
| existing cover, original marked datum and full-visible separation | existing \(C_U,\mathcal N,\operatorname{Sep}_{\partial}(C_U)\) | `finiteEtaleAffinePreimageNormalizedCover`, `_normalClosure`; `conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover` | ROUTE |
| finite-etale structural map to the actual section-ring spectrum | existing \(Y_N\to\operatorname{Spec}(B_U)\), with \(Z_U=Y_N\) on this chart | `finiteEtaleAffineNormalClosureToBase_finite_etale` | ROUTE |
| structural morphism to the actual affine open, its original-base equality and surjectivity | \(\pi_U:Z_U\to U\) | `finiteEtaleAffineNormalClosureToChart`, `_comp_inclusion`, `_finite_etale`, `_surjective` | ROUTE |
| actual finite-etale surjective refinement, original marked leg and exact factorization | \(\lambda_U:Z_U\to V\), \(\nu_{p,U}\circ\lambda_U=\operatorname{Norm}(\mathcal N.\mathit{embedding})\), \(p\|_V\circ\lambda_U=\pi_U\) | `finiteEtaleAffineNormalClosureToPreimage`, `_comp_normalizationIso`, `_comp_toBase`, `_comp_restrict`, `_finite_etale`, `_surjective` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| contraction of a central separability tensor by the algebra trace | prose only; trace-contraction identity | `traceContraction`, `_tmul`, `_eq_lmul_of_central`, `_eq_one_of_central`, `_one_tmul_mul` | ROUTE |
| generic integral trace section, source-action law and derived surjectivity | prose only; $r$ within the generic lemma | `unramifiedIntegralSection`, `_mul`, `_rightInverse`; `unramifiedIntegralEvaluation_surjective` | ROUTE |
| integral selector, scalar-extension action, idempotence and complementary kernel | prose only; $E=r(1)$ within the generic lemma | `unramifiedIntegralIdempotent`, `_map`, `_mul`, `_baseChange_mul`, `_isIdempotentElem`, `_mul_eq_zero_iff`; `unramifiedIntegralEvaluation_ker_eq_span_one_sub` | ROUTE |
| derive generic spanning for the original integral evaluation | existing \(\operatorname{ev}_B\), \(\beta_\Sigma\) and \(\operatorname{ev}_K\); no independent notation | `NormalClosureData.normalizationTensorEvaluation_span` | ROUTE |
| actual normalization trace section and original evaluation | \(r_B:T\to P_B\), \(\operatorname{ev}_B r_B=\operatorname{id}_T\) | `.normalizationTensorSection`, `_mul`, `_rightInverse`; `.normalizationTensorEvaluation_surjective` | ROUTE |
| integral selecting idempotent and exact generic comparison | \(E_{\mathfrak m}=r_B(1)\), \(\ker(\operatorname{ev}_B)=(1-E_{\mathfrak m})\), \(\beta_\Sigma(1\otimes E_{\mathfrak m})=e_{\mathfrak m}\) | `.normalizationTensorIdempotent`, `_spec`, `_baseChange` | ROUTE |
| actual complementary quotient and evaluator-preserving comparison | \(P_B/(1-E_{\mathfrak m})\simeq_B T\); no second symbol for the comparison | `.normalizationTensorQuotientEquiv`, `_mk` | ROUTE |
| finite etale structure on the existing normalization | existing \(T=\widetilde B_N\) | `.normalization_finite_of_etaleModel`, `.normalization_etale_of_etaleModel` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| generic selected field-quotient decomposition | prose only; the generic algebra lemma | `fieldQuotientProductEquiv` and its pointwise / homomorphism first-projection laws | ROUTE |
| generic selecting element and complementary principal kernel | prose only; $e$ within the generic lemma | `fieldQuotientIdempotent` and its idempotence / map / annihilator / uniqueness laws; `fieldQuotient_ker_eq_span_one_sub` | ROUTE |
| finite / separable-etale properties of the existing tensor source | existing \(P_K\) | `NormalClosureData.tensorSource_finite` / `.tensorSource_etale` | ROUTE |
| selected generic product equivalence and exact first projection | \(\Phi_{\mathfrak m}:P_K\simeq_K N\times Q_{\mathfrak m}\), \(Q_{\mathfrak m}=\prod_{I\ne\mathfrak m}P_K/I\), \(\operatorname{pr}_1\Phi_{\mathfrak m}=\operatorname{ev}_K\) | `.tensorEvaluationProductEquiv` / `.fst_comp_tensorEvaluationProductEquiv` | ROUTE |
| the canonical algebra-factor selector and its characterization | \(e_{\mathfrak m}=\Phi_{\mathfrak m}^{-1}(1,0)\), \(\mathfrak m=(1-e_{\mathfrak m})\) | `.tensorEvaluationIdempotent` / `_spec` / `_unique` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| finite split scheme | $Z_I=\operatorname{Spec}(k^I)$ | `SplitPointGeometry.scheme` | ROUTE |
| selected component inclusion | $s_i:\operatorname{Spec}k\to Z_I$ | `SplitPointGeometry.pointInclusion` | ROUTE |
| actual ideal-sheaf data whose associated closed subscheme is integral | $\operatorname{IntSub}(Z_I)$ | `SplitPointGeometry.IntegralClosedSubscheme` | ROUTE |
| ideal sheaf of the reduced point component, and its canonical integral subscheme | $\mathcal I(s_i)$ / $[s_i]\in\operatorname{IntSub}(Z_I)$ | `SplitPointGeometry.pointIdealSheaf` / `pointIntegralSubscheme` | ROUTE |
| exact identification of labels with integral closed subschemes | $I\xrightarrow{\sim}\operatorname{IntSub}(Z_I)$ | `SplitPointGeometry.labelEquivIntegralClosedSubscheme` | ROUTE |
| finitely supported coefficients on actual integral closed subschemes | $Z_0(Z_I;R)=\bigoplus_{W\in\operatorname{IntSub}(Z_I)}R[W]$ | `SplitZeroCycles.Cycles` | ROUTE |
| fundamental cycle of the actual reduced point subscheme | $[s_i]\in Z_0(Z_I;R)$ | `SplitZeroCycles.pointCycle` | ROUTE |
| coefficients indexed by the classified point subschemes | $Z_0(Z_I;R)\xrightarrow{\sim}R^I$ | `SplitZeroCycles.coordinates` | ROUTE |
| actual dimension-one integral closed subschemes, paired with units in their actual scheme function fields; proved empty | $(W,f)$ with $\dim W=1$ and $f\in k(W)^\times$ | `SplitZeroCycles.IntegralCurve` / `PrincipalDivisorData` | ROUTE |
| the unique ambient principal-divisor cycle assignment on the empty geometric indexing type | $(W,f)\mapsto(\iota_W)_*\operatorname{div}_W(f)$ | `SplitZeroCycles.principalDivisor` | ROUTE |
| submodule generated by principal-divisor cycles, proved zero | $\operatorname{Rat}_0(Z_I;R)$ | `SplitZeroCycles.relations` | ROUTE |
| difference lies in the relation submodule; proved equivalent to equality | $z\sim_{\mathrm{rat}}w$ | `SplitZeroCycles.RationallyEquivalent` | ROUTE |
| quotient of the actual cycle module by rational equivalence, and its class map | $\mathrm{CH}_0(Z_I;R)=Z_0/\operatorname{Rat}_0$, $z\mapsto\overline z$ | `SplitZeroCycles.Chow` / `classMap` | ROUTE |
| quotient-by-zero and point-coordinate linear equivalences | $\mathrm{CH}_0(Z_I;R)\xrightarrow{\sim}Z_0(Z_I;R)\xrightarrow{\sim}R^I$ | `SplitZeroCycles.chowEquivCycles` / `chowCoordinates` | ROUTE |
| integral-to-rational coefficient extension on actual cycles | $Z_0(Z_I;\mathbf Z)\hookrightarrow Z_0(Z_I;\mathbf Q)$ | `SplitZeroCycles.rationalize` | ROUTE |
| rational cycle coefficients are scalar extension of the integral module | $\mathbf Q\otimes_{\mathbf Z}Z_0(Z_I;\mathbf Z)\xrightarrow{\sim}Z_0(Z_I;\mathbf Q)$ | `SplitZeroCycles.rationalizationEquiv` | ROUTE |
| coefficient extension induced on the Chow quotient, proved injective | $\mathrm{CH}_0(Z_I;\mathbf Z)\hookrightarrow\mathrm{CH}_0(Z_I;\mathbf Q)$ | `SplitZeroCycles.chowRationalize` | ROUTE |
| canonical rational scalar extension of the integral Chow group, preserving point generators | $\mathbf Q\otimes_{\mathbf Z}\mathrm{CH}_0(Z_I;\mathbf Z)\xrightarrow{\sim}\mathrm{CH}_0(Z_I;\mathbf Q)$ | `SplitZeroCycles.chowRationalizationEquiv` | ROUTE |
| actual scheme-theoretic image and restricted point map | $f(W)$ / $W\to f(W)$ | `SplitPointGeometry.imageIntegralSubscheme` / `imageIntegralSubschemeMap` | ROUTE |
| actual product and inverse-image comparisons respecting their maps | $Z_{I\times J}\simeq Z_I\times_kZ_J$ / $Z_{f^{-1}(i)}\simeq f^{-1}(s_i)$ | `SplitPointGeometry.productIso` / `pointFiberIso` | ROUTE |
| equality of the actual inverse-image ideal sheaf | $f^*\mathcal I(s_i)=\mathcal I(f^{-1}(s_i))$; theorem only | `SplitPointGeometry.pointIdealSheaf_comap_mapOfFunction` | ROUTE |
| actual stalk identifications and degree/multiplicity-one computations | $\mathcal O_{Z_I,s_i}\simeq k$, $m=1$, $[\kappa(s):\kappa(f(s))]=1$; proof adapters | `SplitPointGeometry.pointStalkIso` / `stalkMap_length_of_isOpenImmersion` / `residueFieldMap_finrank_of_isIso` | ROUTE |
| proper pushforward, on cycles and their quotient | $f_*$ | `SplitZeroCycles.pushforward` / `chowPushforward` | ROUTE |
| flat pullback, on cycles and their quotient | $f^*$ | `SplitZeroCycles.pullback` / `chowPullback` | ROUTE |
| external product on actual product points | $z\times w$ | `SplitZeroCycles.externalProduct` / `chowExternalProduct` | ROUTE |
| diagonal pullback of external product | $z\cdot w=\Delta^*(z\times w)$ | `SplitZeroCycles.intersection` / `chowIntersection` | ROUTE |
| actual fiber ambient-stalk length and point-image residue-field degree, both proved one | $m_x(f^{-1}(s_i))$ / $\deg(W/f(W))$ | `SplitZeroCycles.pointFiberMultiplicity` / `imageDegree` | ROUTE |
| fundamental cycle of the actual point fiber, initially weighted by its actual local lengths | $[f^{-1}(s_i)]_0$; identified with $f^*[s_i]$ | `SplitZeroCycles.fiberCycle` | ROUTE |
| rational Chow cycles on the actual product, in its proved split presentation | $\operatorname{Corr}^0(Z_I,Z_J)=\mathrm{CH}_0(Z_I\times_k Z_J;\mathbf Q)$ | `SplitChowCorrespondence.Correspondence` | ROUTE |
| geometric pull--intersection--push composition | $b\circ a=(p_{13})_*(p_{12}^*a\cdot p_{23}^*b)$ | `SplitChowCorrespondence.comp` | ROUTE |
| point-pair coordinates, with outputs in rows | $\kappa_{JI}:\operatorname{Corr}^0(Z_I,Z_J)\xrightarrow{\sim}M_{J\times I}(\mathbf Q)$ | `SplitChowCorrespondence.matrixCoordinates` | ROUTE |
| the existing Chow endomorphisms with actual geometric composition and diagonal unit | $\Gamma_I^{\mathrm{CH}}=\operatorname{Corr}^0(Z_I,Z_I)$ | `SplitChowCorrespondence.EndAlgebra` | ROUTE |
| endomorphism coordinates upgraded to an algebra equivalence by the proved composition law | $\kappa_{II}:\Gamma_I^{\mathrm{CH}}\xrightarrow{\sim}M_I(\mathbf Q)$; same coordinate map | `SplitChowCorrespondence.matrixAlgEquiv` | ROUTE |
| generator-compatible algebra equivalence from the additive span quotient to the actual Chow algebra | $\Psi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}^{\mathrm{add}}\xrightarrow{\sim}\Gamma_I^{\mathrm{CH}}$, with $\kappa_{II}\circ\Psi_{\mathrm{sp}}=\overline\chi_{\mathrm{sp}}$ | `SplitChowCorrespondence.spanQuotientEquiv` | ROUTE |
| actual Chow correspondence action on zero-cycle Chow classes | $c_*z=(p_2)_*(c\cdot p_1^*z)$ | `SplitChowCorrespondence.action` | ROUTE |
| proper pushforward of an actual finite split carrier's fundamental cycle along the pair map, proved to equal the image of its additive span class | $(\ell,r)_*[Z_S]_0=\sum_s[(\ell(s),r(s))]$; no second realization map | `SplitChowCorrespondence.ofSplitSpan` | ROUTE |
| actual complex-algebra points with the regular-function evaluation topology | $X_I=Z_I(\mathbf C)=\operatorname{Hom}_{\mathbf C\text{-alg}}(\mathbf C^I,\mathbf C)$ | `SplitComplexPoints.Point` | ROUTE |
| actual evaluation point / proved homeomorphism from the discrete labels | $\operatorname{ev}_i$ / $I\xrightarrow{\sim}X_I$ | `SplitComplexPoints.evalPoint` / `labelHomeomorph` | ROUTE |
| actual over-base scheme point, continuous functorial point map, and projection-compatible product adapter | no independent symbols; use the existing point and projection maps | `SplitComplexPoints.schemeMorphism` / `mapContinuous` / `productHomeomorph` | ROUTE |
| actual continuous singular simplex | $S_n(X)=C(\Delta^n,X)$ | `SingularDegreeZero.Simplex` | ROUTE |
| actual singular cochains and two-face differential | $C^0(X;\mathbf Q)$ / $C^1(X;\mathbf Q)$ / $\delta^0$ | `SingularDegreeZero.ZeroCochain` / `OneCochain` / `coboundary` | ROUTE |
| unreduced degree-zero singular cohomology, then its actual complex-point specialization | $H^0_{\mathrm B}(X;\mathbf Q)=\ker\delta^0$ / $H^0_{\mathrm B}(X_I;\mathbf Q)$ | `SingularDegreeZero.H0` / `SplitBetti.Cohomology` | ROUTE |
| actual-point evaluation and its discrete-space/label coordinate equivalences | $u\mapsto(x\mapsto u(x))$ / $u\mapsto(u_i)_{i\in I}$; no new realization symbol | `SingularDegreeZero.eval` / `equivFunctions` / `SplitBetti.coordinates` | ROUTE |
| point-normalized cycle-class map, proved a linear equivalence | $\operatorname{cl}_I:\mathrm{CH}_0(Z_I;\mathbf Q)\xrightarrow{\sim}H^0_{\mathrm B}(X_I;\mathbf Q)$ | `SplitBetti.cycleClass` | ROUTE |
| degree-zero singular cup, actual continuous-map pullback, and actual-fiber finite transfer | $\smile$ / $f^*$ / $f_*$, with the cohomological domain displayed | `SingularDegreeZero.cup` / `pullback` / `transfer` | ROUTE |
| characteristic cocycle normalization of the actual point class | $\operatorname{cl}_I([s_i])=\delta_i$ | `SplitBetti.cycleClass_pointCycle` | ROUTE |
| actual singular zero-simplex lifts and the proved source-matching transfer formula | $\{\tau:f\circ\tau=\sigma\}$; no second transfer operation | `SingularDegreeZero.ZeroSimplexLift` / `transfer_simplex_eq_sum_lifts` | ROUTE |
| actual cohomological pull--cup--transfer correspondence action | $c_{\mathrm B,*}u=(p_2)_*(\operatorname{cl}(c)\smile p_1^*u)$ | `SplitBetti.action` | ROUTE |
| rational algebra representation of the actual Chow convolution algebra / packaging in the existing action interface | $\rho_{\mathrm B,I}:\Gamma_I^{\mathrm{CH}}\to\operatorname{End}_{\mathbf Q}(H^0_{\mathrm B}(X_I;\mathbf Q))$; same action | `SplitBetti.realization` / `correspondenceAction` | ROUTE |
| actual tensor complexification of singular degree-zero cohomology / its computed complex point coordinates | $H_I=H^0_{\mathrm B}(X_I;\mathbf Q)$, $H_{I,\mathbf C}=\mathbf C\otimes_{\mathbf Q}H_I\cong\mathbf C^I$ | `SplitHodgeStructure.Complexification` / `complexCoordinates` | ROUTE |
| canonical rational embedding / conjugation induced from the rational structure | $\iota_I(u)=1\otimes u$ / $\overline{c\otimes u}=\bar c\otimes u$ | `SplitHodgeStructure.rationalEmbedding` / `conjugation` | ROUTE |
| explicitly specified effective degree-zero Hodge pieces, with directness, exhaustion, and conjugation proved | $H_I^{p,q}$; all of $H_{I,\mathbf C}$ at $(0,0)$, zero otherwise | `SplitHodgeStructure.bigrading` | ROUTE |
| rational preimage of the complex Hodge piece, independently of cycles | $H_{I,\mathrm{Hdg}}=\iota_I^{-1}(H_I^{0,0})$ | `SplitHodgeStructure.rationalHodgeClasses` | ROUTE |
| genuine scalar extension of a rational map / preservation of all complex bigrading pieces | $f_{\mathbf C}=1\otimes f$ / prose predicate | `SplitHodgeStructure.complexifyMap` / `IsHodgeMorphism` | ROUTE |
| actual coproduct with the distinguished point, respecting both inclusions | $I^+=\{*\}\amalg I$, $Z_{I^+}\cong\operatorname{Spec}\mathbf C\amalg Z_I$ | `SplitChowTateBlock.optionSchemeIso` | ROUTE |
| affine Chow graph construction from actual column pushforward and a fixed point-pair class | $\operatorname{enc}_I(z)=[(*,*)]+j_*z$, $j(i)=(*,i)$ | `SplitChowTateBlock.encode` | ROUTE |
| actual flat column pullback, linear and defined on every correspondence | $\operatorname{dec}_I(c)=j^*c$ | `SplitChowTateBlock.decode` | ROUTE |
| fixed actual cohomology decomposition into distinguished point and complement | $\tau_I:H^0_{\mathrm B}(X_{I^+};\mathbf Q)\xrightarrow{\sim}\mathbf Q(0)\oplus H_I$ | `SplitBettiTateBlock.blockCoordinates` | ROUTE |
| the existing actual Betti action in fixed coproduct coordinates / conjugation adapter | $\rho_I^+(c)=\tau_I\rho_{\mathrm B,I^+}(c)\tau_I^{-1}$ | `SplitBettiTateBlock.realization` / `coordinateChange` | ROUTE |
| actual finite codimension-zero Chow/Betti model with independent Hodge subspace | $\mathscr H_I^0=(\mathrm{CH}_0(Z_I;\mathbf Q),H_I,H_{I,\mathrm{Hdg}},\operatorname{cl}_I)$ | `SplitBettiTateBlock.hodgeModel` | ROUTE |
| instances of the existing graph interfaces using the actual geometric block and Hodge structure | use $\operatorname{enc}_I$, $\operatorname{dec}_I$, and the existing graph criterion; no duplicate objects | `SplitBettiTateBlock.construction` / `detection` / `hodgeCompatibility` | ROUTE |
| Hodge-morphism predicate transported through the fixed actual Betti block decomposition | prose predicate on $\mathbf Q(0)\oplus H_I$ | `SplitBettiTateBlock.IsBlockHodgeMorphism` | ROUTE |
| encoded Chow representative of the independently specified graph operator | $\Pi_\alpha=\operatorname{enc}_I(\operatorname{cl}_I^{-1}\alpha)$, $\rho_I^+(\Pi_\alpha)=P_\alpha$ | `SplitBettiTateBlock.graphProjectorLift` | ROUTE |
| actual regular split torsor action and graph-sheet collision identity | $G\curvearrowright Z_G$, $\coprod_{a\in G}Z_G\cong Z_G\times_{\operatorname{Spec}\mathbf C}Z_G$ | `SplitGaloisSheets.regularAction` / `regularCollisionDecomposition` | ROUTE |
| actual finite étale homogeneous intermediate cover, with no normality hypothesis | $Z_G\to Z_S$, $S=G/D$, $g\mapsto gD$ | `SplitGaloisSheets.quotientMap` | ROUTE |
| complementary marked sheets and their point-plus-complement labeling | $I=S\setminus\{s_0\}$, $I^+\cong S$ | `SplitGaloisResidual.Complement` / `sheetEquiv` | ROUTE |
| restriction with zero-extension inverse; auxiliary coordinates of the existing ideal | $E_D\xrightarrow{\sim}\mathbf Q^I$; no new residual object | `SplitGaloisResidual.residualCoordinates` | ROUTE |
| actual weighted point-cycle construction and its class, upgraded by its proved inverse | $\lambda_D(x)=\sum_{i\in I}x(i)[i]$ for the Chow map; distinguish its cycle representative in prose | `SplitGaloisResidual.residualCycles` / `residualChow` / `residualChowEquiv` | ROUTE |
| actual fundamental point-sum of the complement | $[Z_I]=\sum_{i\in I}[i]$ | `SplitGaloisResidual.fundamentalClass` | ROUTE |
| cycle class after the geometric residual Chow equivalence | $\theta_D=\operatorname{cl}_I\lambda_D$ | `SplitGaloisMarkedComparison.residualRealization` | ROUTE |
| independently generated Chow and Betti target classes | $z_D=\lambda_D(a_D)=-[Z_I]$, $\alpha_D=\theta_D(a_D)=-\operatorname{cl}_I[Z_I]$ | `SplitGaloisMarkedComparison.generatedChowClass` / `generatedClass` | ROUTE |
| actual diagonal pushforward embedding of point functions into correspondence convolution | $\delta_I:\mathbf Q^I\hookrightarrow\Gamma_I^{\mathrm{CH}}$ | `SplitChowDiagonal.diagonalAlgHom` | ROUTE |
| shared actual column pushforward used by both affine encoding and shear | $N_z=j_*z$; no second graph encoding | `SplitChowTateBlock.column` | ROUTE |
| raw marked-point Chow projector in the fixed block | $e_*=[(*,*)]$ | `SplitChowShear.pointProjector` | ROUTE |
| diagonal plus actual column, with its constructed two-sided inverse | $\mathcal U_z=1+N_z$, $\mathcal U_z^{-1}=\mathcal U_{-z}$ | `SplitChowShear.shear` / `shearUnit` | ROUTE |
| existing actual Chow action sends the geometric unit to the linear shear | $\rho_I^+(\mathcal U_z)=U_{\operatorname{cl}_I(z)}$; distinguish Chow $\mathcal U_z$ from linear $U_\alpha$ | `SplitBettiTateBlock.realization_shear` | ROUTE |
| actual scheme reindexing and its algebra map on rational sheet functions | $Z_{I^+}\cong Z_S$ and reindexing; no new geometric cover | `SplitGaloisMarkedComparison.sheetSchemeIso` / `sheetReindex` | ROUTE |
| actual cycle class of a weighted sheet cycle / its realized constant-unit coordinates | sheet-cycle class in prose; $\Theta_DT_D$ for the block map, not a new realization action | `SplitGaloisMarkedComparison.sheetCohomology` / `sourceToBlock` | ROUTE |
| the marked source coordinates are the action of the actual Chow shear on the full sheet class | $\Theta_DT_D(f)=\rho_I^+(\mathcal U_{z_D})\tau_I(\operatorname{cl}(\sum_s f(s)[s]))$ | `SplitGaloisMarkedComparison.sourceToBlock_eq_realization_shear` | ROUTE |
| injective actual sheet-to-Chow algebra map, diagonal pushforward followed by fixed geometric conjugation | $\delta_D^{\mathrm{mk}}=\operatorname{Ad}(\mathcal U_{z_D})\circ\delta_{I^+}\circ\operatorname{reindex}$ | `SplitGaloisMarkedComparison.markedEmbedding` | ROUTE |
| full sheet multiplication acts through the actual marked Chow embedding | $\rho_I^+(\delta_D^{\mathrm{mk}}(f))\Theta_DT_D(g)=\Theta_DT_D(fg)$; the selector square is its marked specialization | `SplitGaloisMarkedComparison.markedEmbedding_action` | ROUTE |
| actual image of the selector and Chow conjugate of the raw marked point | $\Pi_D=\delta_D^{\mathrm{mk}}(q_D)=\mathcal U_{z_D}e_*\mathcal U_{-z_D}=\operatorname{enc}_I(z_D)$ | `SplitGaloisMarkedComparison.markedProjector` | ROUTE |
| instantiated restriction-free comparison under the unchanged fixed Tate-block action | $\mathscr R_{\Pi_D}$, using $\Theta_D=\operatorname{id}_{\mathbf Q}\oplus\theta_D$ and existing $\rho_I^+$ | `SplitGaloisMarkedComparison.comparison` | ROUTE |
| the chosen idempotent and its independently specified graph target | $\rho_I^+\circ\varphi_{\Pi_D}=\varphi_{P_{\alpha_D}}$; no new target object | `SplitGaloisMarkedComparison.projectorLift` / `palomarTargetSquare` | ROUTE |
| exact rigidity of a surjective multiplicative residual realization | $\alpha=-1$ in the target algebra; a theorem, not a coverage hypothesis | `MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_surjective` | ROUTE |
| unique point label and scheme isomorphism respecting an integral closed immersion | $e:X\xrightarrow{\sim}\operatorname{Spec}k$, $s_i\circ e=f$ | `SplitPointGeometry.existsUnique_pointIso_of_isIntegral` | ROUTE |
| dimension bound for actual closed subschemes, equality if nonempty | $\dim X\leq 0$ / $\dim X=0$ | `SplitPointGeometry.topologicalKrullDim_le_zero_of_isClosedImmersion` / `topologicalKrullDim_eq_zero_of_isClosedImmersion` | ROUTE |
| quotient by a coordinate prime is the base field | $\mathfrak m_i=\ker(\operatorname{ev}_i)$, $k^I/\mathfrak m_i\cong_k k$ | `SplitFieldQuotient.evalQuotientEquiv` | ROUTE |
| actual point-supported diagonal span | $Z_I\xleftarrow{s_i}\operatorname{Spec}k\xrightarrow{s_i}Z_I$ | `SplitPointGeometry.pointSpan` | ROUTE |
| its free finite-étale span basis class | $\pi_i$ | `SplitPointGeometry.pointProjector` | ROUTE |
| earlier finite rational coefficient module, now the point-coordinate presentation of actual scheme Chow | $\mathbf Q^I$, $I=\{0,1\}$ | `SplitPointCorrespondence.ZeroCycles` | ROUTE |
| finite coefficient convolution algebra | $\Gamma_I=M_2(\mathbf Q)$ | `SplitPointCorrespondence.Correspondence` | ROUTE |
| point matrix unit | $\Pi=E_{00}$ | `SplitPointCorrespondence.firstPointProjector` | ROUTE |
| marked two-component source | $A=\mathbf Q\times\mathbf Q$, $\epsilon(a,b)=a$, $q=(1,0)$ | `SplitPointCorrespondence.markedSource` | ROUTE |
| second-coordinate map on the residual ideal | $\theta(0,b)=b$ | `SplitPointCorrespondence.residualEvaluation` | ROUTE |
| constant-unit coordinates | $T(a,b)=(a,b-a)$ | `SplitPointCorrespondence.constantCoordinates` | ROUTE |
| ordinary / conjugated matrix action | $C\mapsto C(-)$ / $\rho(C)=TCT^{-1}$ | `SplitPointCorrespondence.pointRealization` / `realization` | ROUTE |
| explicit instances of the canonical comparison / lift | specialization only; no independent symbol | `SplitPointCorrespondence.markedComparison` / `projectorLift` | ROUTE |
| scheme map and span induced by finite indexing functions | $Z_S\to Z_I$ / $Z_I\xleftarrow{\ell}Z_S\xrightarrow{r}Z_I$ | `SplitPointGeometry.mapOfFunction` / `span` | ROUTE |
| intrinsic-point and relabelling equivalences used for descent | prose only; presentation adapters | `labelEquivScheme` / `labelEquivOfIso` | ROUTE |
| finite matching pairs compute the actual scheme pullback | $\{(s,t):r(s)=\ell'(t)\}$ / $Z_S\times_{Z_J}Z_T$ | `Fiber` / `fiberIso` / `span_comp_iso` | ROUTE |
| sum-indexed span is the actual scheme coproduct | $P\sqcup Q$; no second coproduct object | `span_sum_iso` | ROUTE |
| split span is the actual indexed coproduct of its point-pair spans | $[S,\ell,r]\cong\coprod_{s\in S}[\{*\},\ell(s),r(s)]$ at the scheme-span level | `span_pointDecomposition_iso` | ROUTE |
| finite split presentation of an existing geometric class | witness only; no independent object symbol | `SplitSpanRealization.Presentation` | ROUTE |
| split-presentable submonoid of actual finite-étale span classes | $\mathcal S_{\mathrm{sp}}(Z_I/k)$ | `SplitSpanRealization.classSubmonoid` / `SplitClass` | ROUTE |
| free rational linearization of that submonoid, before coproduct relations | $\mathcal C_{\mathrm{sp}}(Z_I/k)$ | `SplitSpanRealization.FreeAlgebra` | ROUTE |
| injective source algebra inclusion | $j_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\hookrightarrow\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}$ | `SplitSpanRealization.toFiniteEtaleFreeAlgebra` | ROUTE |
| point-count assignment and its rational algebra extension; surjective, proved noninjective by the empty-span witness | $\chi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\twoheadrightarrow M_I(\mathbf Q)$ | `classMatrixHom` / `SplitSpanRealization.realization` | ROUTE |
| finite point-decomposition difference in the free algebra | $d_{S,\ell,r}=[S,\ell,r]-\sum_s[\{*\},\ell(s),r(s)]$ | `SplitSpanRealization.decompositionDefect` | ROUTE |
| two-sided ideal generated by those differences, proved equal to the realization kernel | $J_{\mathrm{sp}}=\langle d_{S,\ell,r}\rangle=\ker\chi_{\mathrm{sp}}$ | `SplitSpanRealization.additiveRelations` | ROUTE |
| quotient of the free source by finite point-decomposition relations, now algebra-isomorphic to the actual Chow endomorphisms | $\mathcal C_{\mathrm{sp}}^{\mathrm{add}}=\mathcal C_{\mathrm{sp}}/J_{\mathrm{sp}}$ | `SplitSpanRealization.AdditiveQuotient` | ROUTE |
| induced matrix map, proved to be an algebra isomorphism | $\overline\chi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}^{\mathrm{add}}\xrightarrow{\sim}M_I(\mathbf Q)$ | `SplitSpanRealization.quotientRealization` / `quotientRealizationEquiv` | ROUTE |
| linear normal-form map used in the kernel proof; not an algebra-homomorphism section of the free realization | proof adapter only; no independent notation | `SplitSpanRealization.pointNormalForm` | ROUTE |
| split-source point projector whose ambient image is the original point span | $\pi_0^{\mathrm{sp}}$, with $j_{\mathrm{sp}}(\pi_0^{\mathrm{sp}})=\pi_0$ | `GeometricSplitPoints.projector` | ROUTE |
| existing coefficient action composed with the new geometric-source map | $\rho\circ\chi_{\mathrm{sp}}$ | `GeometricSplitPoints.coefficientRealization` | ROUTE |
| canonical comparison/lift/square specialized to the actual source | no new notation; $(\rho\circ\chi_{\mathrm{sp}})\circ\varphi_{\pi_0^{\mathrm{sp}}}=\varphi_{P_{-1}}$ | `GeometricSplitPoints.markedComparison` / `projectorLift` / `palomarTargetSquare` | ROUTE |
| the existing coefficient action and target square descended through the proved additive quotient | induced action only; no duplicate marked-comparison object or independent notation | `GeometricSplitPoints.additiveCoefficientRealization` / `additivePalomarTargetSquare` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual generic germ on a nonempty open of the affine spectrum, expressed in the specified fraction field | $\eta_V:\Gamma(V,\mathcal O)\hookrightarrow F$ | `affineSectionsToFractionField` | ROUTE |
| actual section image and its canonical algebra equivalence | $R_V=\operatorname{im}\eta_V$, $\Gamma(V,\mathcal O)\simeq_T R_V$ | `affineSectionSubalgebra` / `affineSectionsEquivSubalgebra` | ROUTE |
| complement of the existing fixed--moving boundary ideal | $U_I=\operatorname{Spec}\widetilde B_N\setminus V(J_{\mathrm{fm}}(I))$ | `fixedMovingBoundaryOpen` | ROUTE |
| actual structure-sheaf sections on the boundary complement | $\Gamma(U_I,\mathcal O)$ | `BoundarySectionRing` | ROUTE |
| specialization of the generic-germ algebra embedding | $\eta_I:\Gamma(U_I,\mathcal O)\hookrightarrow N$ | `boundarySectionsToNormalClosure` | ROUTE |
| section overring in the same normal-closure field and canonical image equivalence | $R_I=\operatorname{im}\eta_I$, $\Gamma(U_I,\mathcal O)\simeq_{\widetilde B_N}R_I$ | `boundarySectionSubalgebra` / `boundarySectionsEquivSubalgebra` | ROUTE |
| existing trace-dual submodule and its normalization specialization | $T^\vee_B=\{z\in N:\operatorname{Tr}_{N/K}(zT)\subseteq B\}$ | `Submodule.traceDual B K (1 : Submodule T N)` / `normalizationTraceDual C` | ROUTE |
| scalar multipliers sending every actual boundary section into the trace dual | $(T^\vee_B:R_I)$ | `(normalizationTraceDual C).colon (boundarySectionSubalgebra C I hI).toSubmodule` | ROUTE |
| affine base | $B$ | `B : Type*`, `[CommRing B]` (parameter) | ROUTE |
| fraction field of the base | $K=\operatorname{Frac}(B)$ | `K : Type*`, `[Field K] [Algebra B K] [IsFractionRing B K]` (parameter) | ROUTE |
| selected finite extension | $L/K$ | `L : Type*`, `[Field L] [Algebra K L]` (parameter) | ROUTE |
| supplied normal closure | $N/K$ | `N : Type*`, `[Field N] [Algebra K N]` (parameter of `NormalClosureData`) | ROUTE |
| marked normal-closure datum | $\mathcal N=(K,L,N,\iota)$ | `NormalClosureData` | ROUTE |
| Galois structure derived from the same finite normal-closure datum over a perfect base | $\operatorname{Gal}_{\mathcal N}:\operatorname{IsGalois}(N/K)$ | `NormalClosureData.isGalois` | ROUTE |
| normal-closure Galois group | $G=\operatorname{Gal}(N/K)$ | `NormalClosureData.galoisGroup` | ROUTE |
| stabilizer of the marked copy of $L$ | $H=\operatorname{Gal}(N/\iota(L))$ | `intermediateFixingSubgroup` | ROUTE |
| normal-closure base-change splitting into marked sheets | $\sigma_{\mathcal N}:N\otimes_KL\to N^{G/H}$, an equivalence for separable $L/K$ (in particular over perfect $K$) | `NormalClosureData.normalClosureTensorToGenericSheets` / `normalClosureTensorGenericSheetsEquiv` | ROUTE |
| evaluation at the marked base sheet | $\epsilon_H^N:N^{G/H}\to N$ | `NormalClosureData.normalClosureBaseSheetAugmentation` | ROUTE |
| marked tensor-diagonal algebra map | $\delta_\iota:N\otimes_KL\to N$, $x\otimes y\mapsto x\iota(y)$ | `NormalClosureData.normalClosureTensorDiagonal` | ROUTE |
| multiplicative source square, followed by its perfect-field equivalence restatement | $\epsilon_H^N\circ\sigma_{\mathcal N}=\delta_\iota$ | `normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets` / `normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv` | ROUTE |
| integral closure of $B$ in $L$ | $\widetilde B_L=\operatorname{IntCl}_B(L)$ | `IntermediateNormalizationRing` | ROUTE |
| integral closure of $B$ in $N$ | $\widetilde B_N=\operatorname{IntCl}_B(N)$ | `NormalClosureNormalizationRing` | ROUTE |
| marked normalization scheme | $Y_L=\operatorname{Spec}(\widetilde B_L)$ | `intermediateNormalization` | ROUTE |
| common normal-closure normalization | $Y_N=\operatorname{Spec}(\widetilde B_N)$ | `normalClosureNormalization` | ROUTE |
| finite normalization with marked visible open | $\mathcal C=(U\mathbin{\lhook\joinrel\longrightarrow}Y_L,\mathcal N)$ | `NormalizedCover` | ROUTE |
| valuation/center normalization diagram | $\mathscr D$ | `Diagram` | ROUTE |
| conjugate marked embedding | $\iota_g:L\hookrightarrow N$ | `conjugateNormalClosureEmbeddingOverBase` | ROUTE |
| conjugate normalization leg | $c_g:Y_N\to Y_L$ | `conjugateNormalClosureToIntermediateNormalization` | ROUTE |
| deleted boundary in $Y_L$ | $\partial U=Y_L\setminus U$ | `Diagram.boundary` | ROUTE |
| boundary pulled to the common normalization | $\partial_g=c_g^{-1}(\partial U)$ | `pulledBackConjugateBoundary` | ROUTE |
| radical ideal of $\partial_g$ | $J_g=I(\partial_g)$ | `pulledBackConjugateBoundaryIdeal` | ROUTE |
| ideal generated by inertia differences | $J_{\mathrm{fix}}(I)=(\sigma(t)-t)_{\sigma\in I,t\in\widetilde B_N}$ | `fixedLocusIdeal` | ROUTE |
| sum of boundaries of sheets moved by $I$ | $J_{\mathrm{mov}}(I)=\sum_{I\nleq gHg^{-1}}J_g$ | `movingBoundaryIdeal` | ROUTE |
| combined fixed--moving ideal | $J_{\mathrm{fm}}(I)=J_{\mathrm{fix}}(I)+J_{\mathrm{mov}}(I)$ | `fixedMovingBoundaryIdeal` | ROUTE |
| height-one avoidance condition | $\operatorname{Sep}_{\partial}(\mathcal C)$ | `ConjugateBoundarySeparation` | ROUTE |
| ramified height-one locus as a type | $\operatorname{Ram}^{(1)}(Y_N/B)$ | `RamifiedCodimensionOnePoint` | ROUTE |
| empty height-one ramification locus | $\operatorname{Ram}^{(1)}(Y_N/B)=\varnothing$ | `NoCodimensionOneRamification` | ROUTE |
| identification of centers with $c_g$ | $\operatorname{Ctr}(\mathscr D)$ | `ConjugateCenterRealization` | ROUTE |
| equality of relative and geometric indices | $\operatorname{RamCmp}(\mathscr D)$ | `ConjugateRamificationRealization` | ROUTE |
| the preceding two independent comparisons | $\mathscr B_{\mathscr D}=(\operatorname{Ctr},\operatorname{RamCmp})$ | `ConjugateBoundaryData` | ROUTE |

### Inertia, sheets, and extension objects

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| centered valuation ring at a ramified point | $V_E$ | `valuationAt E` | ROUTE |
| valuation inertia subgroup | $I_E\leq G$ | `inertiaGroupAt` | ROUTE |
| stabilizer kernel on the residue ring | $I_Q^{\mathrm{pr}}\leq G$ | `primeInertiaSubgroup` | ROUTE |
| marked sheet set | $\Sigma_H=G/H$ | `GaloisSheets H` | ROUTE |
| pointwise sheet algebra | $F_k(H)=k^{G/H}$, with $A_H:=F_{\mathbf Q}(H)$ | `GenericSheetAlgebra k H` | ROUTE |
| characteristic function of selected sheets | $q_A=\mathbf 1_A$ | `genericSheetSelector k H A` | ROUTE |
| characteristic function of the base coset | $q_H=\mathbf 1_{\{H\}}$ | `MarkedSheetProjector.selector H` | ROUTE |
| $I$-stable selected sheet set | $\operatorname{Sat}_I(A)$, equivalently $I\cdot A=A$ | `InertiaSaturated I H A` | ROUTE |
| actual global selector extensions | $\operatorname{Ext}^{\mathrm{sel}}_{\partial}(q_A)$ | `GlobalSheetSelectorExtension` | ROUTE |
| selector gluing equivalence | $\operatorname{Pur}^{\mathrm{sel}}_{\partial}$ | `GaloisProjectorExtensionPurity` | ROUTE |
| rational group-algebra idempotent | $e_H=\lvert H\rvert^{-1}\sum_{h\in H}[h]$ | `SchemeCorrespondence.subgroupAverage H` | ROUTE |
| generic graph-correspondence image of the average | $\pi_H^\eta=\gamma_\eta(e_H)$ | `subgroupAveragingProjector` | ROUTE |
| free finite-etale span algebra | $\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}(X/T)$ | `FiniteEtaleFreeAlgebra pX` | ROUTE |
| generic convolution algebra | $\Gamma_\eta$ | `genericAlgebra` (parameter of `SchemeCorrespondence.RationalChowCorrespondenceModel`) | ROUTE |
| target convolution algebra | $\overline\Gamma$ | `compactifiedAlgebra` (parameter of `SchemeCorrespondence.RationalChowCorrespondenceModel`) | ROUTE |
| generic restriction | $r:\overline\Gamma\to\Gamma_\eta$ | `SchemeCorrespondence.RationalChowCorrespondenceModel.restriction` | ROUTE |
| raw closure witnesses for $e_\eta$ | $\operatorname{Cl}_r(e_\eta)$ | `AlgebraProjectorClosure` | ROUTE |
| multiplicative idempotence defect | $\operatorname{Def}(\Pi)=\Pi^2-\Pi$ | `projectorIdempotenceDefect` | ROUTE |
| raw closures with vanishing defect | $\operatorname{Cl}_r^0(e_\eta)$ | `ZeroDefectWitness` | ROUTE |
| compactified idempotent extensions | $\operatorname{Ext}_r(e_\eta)$ | `AlgebraProjectorExtension` | ROUTE |
| universal presentation of the generic idempotent | $\varphi_{e_\eta}:\mathcal U\to\Gamma_\eta$ | `AlgebraProjectorExtension.genericIdempotentMap` | ROUTE |
| universal presentation of a compactified idempotent | $\varphi_\Pi:\mathcal U\to\overline\Gamma$ | `AlgebraProjectorExtension.compactifiedIdempotentMap` | ROUTE |
| universal compactification square | $r\circ\varphi_\Pi=\varphi_{e_\eta}$ | `restriction_comp_compactifiedIdempotentMap` | ROUTE |
| all-boundary extensions of $e_H$ | $\operatorname{Ext}_{\partial,r}(e_H)$ | `CompactifiedSubgroupProjectorExtension` | ROUTE |
| generic/compactified graph square | $\mathscr G_r$ | `CompactifiedDeckGraphComparison` | ROUTE |

### Actual closed graphs and restriction (SP30)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual graph morphism, with the same ordered legs as the existing graph span | $g_\sigma=(\operatorname{id},\sigma):Y\to Y\times_UY$ | `SchemeCorrespondence.graphMorphism p σ` | ROUTE |
| kernel ideal of the graph morphism; defines the closed graph when $p$ is separated | $\mathcal I_\sigma$ | `SchemeCorrespondence.graphIdeal p σ` | ROUTE |
| actual closed graph and its source identification, not a cycle class | $\operatorname{Gr}(\sigma)$ / $Y\simeq\operatorname{Gr}(\sigma)$ | `(graphIdeal p σ).subscheme` / `graphSubschemeIso p σ` | ROUTE |
| proved properties of the graph morphism under separatedness | prose only; no extra source input | `graphMorphism_isClosedImmersion` / `graphMorphism_isProper` | ROUTE |
| actual inclusion of the cover and induced open inclusion of relative products | $\iota:Y\hookrightarrow\bar Y$ / $\iota^{(2)}:Y\times_UY\hookrightarrow\bar Y\times_S\bar Y$ | `FiniteEtaleExtension.inclusion` / `pairInclusion` | ROUTE |
| open immersion and actual Cartesian graph restriction square | prose only; no duplicate comparison package | `pairInclusion_isOpenImmersion` / `graph_restriction_commutes` / `graphRestriction_isPullback` | ROUTE |
| scheme-theoretic inverse-image equality for an already extended automorphism | $\mathcal I_{\operatorname{res}_E\sigma}=(\iota^{(2)})^*\mathcal I_\sigma$ | `graphIdeal_restriction` | ROUTE |
| specialization to a prescribed original action under the explicit deck-extension hypothesis | same ideal equality; theorem only | `graphIdeal_liftDeckAction` | ROUTE |

The graph span, its closed-subscheme realization, and any later Chow class
remain distinct types. The new construction has no new projector or
literature premise. Its base $S$ is auxiliary, not the ultimate Hodge target.
Here $(-)^*$ on ideals means scheme-theoretic inverse image, not yet a map
of Chow groups.

### Finite cycles and integral graph assembly (SP31)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual integral ideal-sheaf subschemes; the split type is its definitional specialization | $\operatorname{IntSub}(W)$ | `SchemeCycles.IntegralClosedSubscheme W` | CORE |
| finite, ungraded cycles; no rational-equivalence quotient | $Z_{\mathrm{fin}}(W;R)=\bigoplus_{Z\in\operatorname{IntSub}(W)}R[Z]$ | `SchemeCycles.Cycles W R` | CORE |
| coefficient-one integral generator | $[Z]$ | `SchemeCycles.fundamentalCycle R Z` | CORE |
| actual open map on inverse-image supports and nonempty integral support | $v^{-1}Z\to Z$ / $v^{-1}Z$ | `openRestrictionSubschemeMap` / `openRestrictionSubscheme` | ROUTE |
| empty-aware generator restriction and its linear extension | $v^*_{\mathrm{cyc}}[Z]$ / $v^*_{\mathrm{cyc}}:Z_{\mathrm{fin}}(W;R)\to_R Z_{\mathrm{fin}}(V;R)$ | `openRestrictionGenerator` / `openRestriction` | ROUTE |
| functoriality of the same open restriction | prose only; no extra comparison object | `openRestriction_id` / `openRestriction_comp` | ROUTE |
| the existing closed graph as an integral support, then its cycle generator | $\operatorname{Gr}(\sigma)$ / $[\operatorname{Gr}(\sigma)]$ | `graphIntegralSubscheme` / `graphCycle` | ROUTE |
| graph dimension transported through its actual source isomorphism | $\dim\operatorname{Gr}(\sigma)=\dim Y$; theorem only | `graphIdeal_topologicalKrullDim` | ROUTE |
| rational linear assembly of actual integral graph cycles | $\zeta_p:\mathbf Q[\operatorname{Aut}_U(Y)]\to_{\mathbf Q}Z_{\mathrm{fin}}(Y\times_UY;\mathbf Q)$ | `graphCycleLinearMap p` | ROUTE |
| integrality inherited by the nonempty open original cover | prose only; derived property, not a new source premise | `FiniteEtaleExtension.original_isIntegral` | ROUTE |
| generator compatibility and weighted cycle restriction square | $(\iota^{(2)})^*_{\mathrm{cyc}}\circ\zeta_{\bar p}=\zeta_p\circ\mathbf Q[\operatorname{res}_E]$ | `graphCycle_restriction` / `graphCycleLinearMap_restriction` | ROUTE |

The new $\zeta_p$ is not the existing free-span algebra map $\gamma$ or a
Chow realization. Its codomain has no newly imposed product. The split
zero-cycle notation remains $Z_0(Z_I;R)$ because every split integral
support already has proved dimension zero. General open restriction
introduces no assertion that absolute dimension is unchanged.

### Scheme-theoretic graph composition and integral multiplicity (SP32)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual relative triple product, with matching middle coordinates | $T=(Y\times_S Y)\times_Y(Y\times_S Y)$ | `tripleProduct p` | ROUTE |
| coordinate-pair projections | $p_{12},p_{23},p_{13}$ | `tripleProductP12`, `tripleProductP23`, `tripleProductP13` | ROUTE |
| source parameterization, with $\tau$ acting first | $h_{\sigma,\tau}(y)=(y,\tau y,\sigma(\tau y))$ | `graphCompositionMorphism p σ τ` | ROUTE |
| sum of inverse-image graph ideals, not their intersection as ideals | $\mathcal J_{\sigma,\tau}=p_{12}^*\mathcal I_\tau+p_{23}^*\mathcal I_\sigma$ | `graphIntersectionIdeal p σ τ` | ROUTE |
| actual scheme-theoretic intersection of the two pulled-back closed graphs | $Z_{\sigma,\tau}=V(\mathcal J_{\sigma,\tau})$ | `(graphIntersectionIdeal p σ τ).subscheme` | ROUTE |
| source identifies with that intersection | $Y\simeq Z_{\sigma,\tau}$; no extra object notation | `graphIntersectionIso` | ROUTE |
| first/last projection identifies intersection with composite graph | $Z_{\sigma,\tau}\simeq\operatorname{Gr}(\sigma\tau)$ | `graphCompositionIso` | ROUTE |
| exact scheme-theoretic image ideal | $\operatorname{Im}_{\mathrm{sch}}(Z_{\sigma,\tau}\to Y\times_S Y)=\operatorname{Gr}(\sigma\tau)$ | `graphIntersectionIdeal_map_p13` | ROUTE |
| fundamental multiplicity for an integral closed support, with actual ambient scalars | $\operatorname{length}_{\mathcal O_{W,i(\eta_Z)}}\mathcal O_{Z,\eta_Z}=1$ | `genericStalk_length_of_isClosedImmersion` / `integralSubscheme_genericStalk_length` | CORE |

No second projector, graph cycle type, or assumed convolution operation is
introduced. `graphMulIsom` remains the span comparison; the new theorem
identifies actual ideal-sheaf subschemes. Ideal `map` means the kernel ideal
of the composite inclusion, not a cycle pushforward. Ambient length one
does not yet identify a Chow intersection product.

### Closed-support images and graph-slice cycle maps (SP33)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual ideal image of a support whose composite into the target is a closed immersion | $f(Z)$ | `SchemeCycles.closedImageSubscheme f Z` | CORE |
| support-to-image isomorphism, preserving the generic point | $Z\simeq f(Z)$; no extra object notation | `closedImageSubschemeIso` / `closedImageSubschemeIso_genericPoint` | CORE |
| canonical generic degree-one proof; old split name is an adapter | $[\kappa(\eta_Z):\kappa(\eta_{f(Z)})]=1$ in the support-image application | `SchemeCycles.residueFieldMap_finrank_of_isIso` | CORE |
| degree-one pushforward of a single admissible support | $f_{*,Z}[Z]$ | `closedImageCycle` | CORE |
| linear pushforward along a globally closed immersion | $f_{*,\mathrm{cyc}}$ | `closedImmersionPushforward` | CORE |
| closed graph slice with free first and last coordinates | $s_\tau(y,z)=(y,\tau y,z)$ | `graphSliceMorphism p τ` | ROUTE |
| actual pair isomorphism, changing the input coordinate | $u_\tau=p_{23}s_\tau=(\tau,\mathrm{id})$ | `graphSlicePairMap p τ` | ROUTE |
| slice identifies with the first graph's actual inverse image | $s_\tau(W)=p_{12}^{-1}\operatorname{Gr}(\tau)$ | `graphSlice_isPullback` / `graphIdeal_comap_p12_eq_graphSlice_ker` | ROUTE |
| open restriction along the pair isomorphism | $\mathsf R_\tau=u_\tau^*{}_{\mathrm{cyc}}$ | `graphRightPullback` | ROUTE |
| pair pullback followed by closed slice pushforward | $\mathsf K_\tau=(s_\tau)_{*,\mathrm{cyc}}\mathsf R_\tau$ | `graphSlicePullPush` | ROUTE |
| existing actual intersection as an integral support and its canonical cycle | $Z_{\sigma,\tau}$ / $[Z_{\sigma,\tau}]$ | `graphIntersectionIntegralSubscheme` / `graphIntersectionCycle` | ROUTE |
| supportwise outer-image formula | $(p_{13})_{*,Z_{\sigma,\tau}}[Z_{\sigma,\tau}]=[\operatorname{Gr}(\sigma\tau)]$ | `graphIntersectionCycle_image_p13` | ROUTE |
| additional open-and-closed relative graph geometry under étaleness | prose only; no new cycle or projector | `EtaleGraphIntersection` openness instances / `graphSliceMorphism_isOpenImmersion` | ROUTE |

The pair and inverse-image graph schemes may be reducible. They are not
installed as integral generators. The cycle maps above have specified
domains; no ambient outer pushforward or Chow algebra product is declared.
The canonical residue-degree proof now lives in `Cycles/ResidueDegree.lean`,
with the old split-point theorem retained only as a compatibility adapter.

### Structural-base graph and cycle comparison (SP34)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| injective change-of-base group map retaining the actual automorphism | $\operatorname{forg}_b:\operatorname{Aut}_S(Y)\hookrightarrow\operatorname{Aut}_B(Y)$, $\sigma\mapsto\bar\sigma$ | `forgetDeckBase p b` | ROUTE |
| actual closed inclusions, for separated $b:S\to B$ and $r=b\circ p$ | $\kappa_2:W_p\hookrightarrow W_r$, $\kappa_3:T_p\hookrightarrow T_r$, with $W_p=Y\times_S Y$ | `pairBaseComparison p b`, `tripleBaseComparison p b` | ROUTE |
| graph, intersection, pair-isomorphism and slice compatibility | prose only; the graphs and slices are the existing objects with base subscripts | `GraphBaseComparison` morphism and ideal-image theorems | ROUTE |
| genuine ideal and cycle transport through inverse isomorphisms | $e^*_{\mathrm{cyc}}=(e^{-1})_{*,\mathrm{cyc}}$; theorem only | `ideal_comap_iso_eq_map_inv`, `openRestriction_iso_eq_pushforward_inv` | ROUTE |
| closed inclusion carries actual integral generators to their new-base versions | $\kappa_{2,*\mathrm{cyc}}[\operatorname{Gr}_p(\sigma)]=[\operatorname{Gr}_r(\bar\sigma)]$, $\kappa_{3,*\mathrm{cyc}}[Z^p_{\sigma,\tau}]=[Z^r_{\bar\sigma,\bar\tau}]$ | `graphCycle_pairBaseComparison`, `graphIntersectionCycle_tripleBaseComparison` | ROUTE |
| rational weighted assembly square | $\kappa_{2,*\mathrm{cyc}}\zeta_p=\zeta_r\mathbf Q[\operatorname{forg}_b]$ | `graphCycleLinearMap_baseComparison` | ROUTE |
| entire finite-cycle comparison squares, without ambient integrality | $\kappa_{2,*\mathrm{cyc}}\mathsf R^p_\tau=\mathsf R^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}}$, $\kappa_{3,*\mathrm{cyc}}\mathsf K^p_\tau=\mathsf K^r_{\bar\tau}\kappa_{2,*\mathrm{cyc}}$ | `graphRightPullback_baseComparison`, `graphSlicePullPush_baseComparison` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual principal-quotient length, extended to the fraction field and read as an integer on units | $\operatorname{ord}_A(f)$; one order, not a second valuation | Mathlib `Ring.ord`, `Ring.ordFrac` / `SchemeCycles.localOrder` | CORE |
| finite lengths and fraction formula | $\operatorname{ord}_A(a/b)=\ell_A(A/(a))-\ell_A(A/(b))$ | `principalQuotient_length_ne_top`, `localOrder_algebraMap`, `localOrder_fraction` | CORE |
| invariance of the actual length-defined order under compatible ring/field maps | prose only; compatibility theorem, not a new order input | `ord_ringEquiv`, `ordFrac_ringEquiv` | CORE |
| actual generic-point stalk, a field for integral schemes | $k(X)=\mathcal O_{X,\eta_X}$ | Mathlib `Scheme.functionField` | CORE |
| categorical and ring presentations of one actual contravariant field isomorphism | $e^*:k(Y)\xrightarrow{\sim}k(X)$ | `functionFieldIso` / `functionFieldEquiv` | CORE |
| actual field/local-stalk compatibility | prose only; proved commutative square | `functionFieldEquiv_algebraMap` | CORE |
| literal points with one-dimensional local ring | $\operatorname{DivPt}(X)=\{x:\dim\mathcal O_{X,x}=1\}$ | `DivisorPoint X` | CORE |
| constructor from an actual affine-chart height-one prime | prose only; no second point index | `divisorPointOfAffineHeightOne` | CORE |
| restriction of the actual scheme point equivalence | $e_1:\operatorname{DivPt}(X)\simeq\operatorname{DivPt}(Y)$ | `divisorPointEquiv e` | CORE |
| signed order through the canonical stalk-to-function-field algebra | $\operatorname{ord}_x:k(X)^\times\to\mathbf Z$ | `divisorOrder X x` | CORE |
| local coefficient invariance through the actual geometric maps | $\operatorname{ord}_x(e^*f)=\operatorname{ord}_{e_1(x)}(f)$ | `divisorOrder_iso` | CORE |
| computed nonzero signed coefficients, from $\mathbf Z/(2)$ having length one | $\operatorname{ord}_{\mathbf Z}(2)=1$, $\operatorname{ord}_{\mathbf Z}(1/2)=-1$; test only | `Examples.localOrder_int_two`, `Examples.localOrder_int_two_inv` | CORE |

The algebra API allows Noetherian domains of dimension at most one; the
scheme index requires local dimension exactly one. No normality or DVR
premise, valuation inequality, divisor cycle, or arbitrary relation package
is introduced. `DivisorPoint` is not the boundary's ramified-prime/valuation
index. SP36 identifies it with the existing integral closed prime supports;
SP37 supplies finite support under quasi-compactness; SP38 assembles the
finite divisor cycle in the existing module.

### Actual prime supports (SP36)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual reduced closed subscheme defined by the vanishing ideal of the point closure | $Z_x=(\overline{\{x\}})_{\mathrm{red}}$ | `pointSupport X x` | CORE |
| image of the integral subscheme's own generic point under its closed immersion | $\xi_Z=\iota_Z(\eta_Z)$; distinguish $\eta_Z\in Z$ from $\xi_Z\in X$ | `ambientGenericPoint Z` | CORE |
| reduced closure and ambient generic point are inverse | $X\simeq\operatorname{IntSub}(X)$ | `pointEquivIntegralClosedSubscheme X` | CORE |
| topological irreducible point closure and the actual underlying closed support | $\overline{\{x\}}$, $\|Z\|$; underlying spaces, not additional scheme generators | `pointClosureOrderIso`, `integralSupport` | CORE |
| chain codimension of the actual irreducible closed support | $\operatorname{codim}(\|Z\|,X)$; not $\dim X-\dim Z$ | `supportCodimension Z` | CORE |
| actual codimension/local-ring bridge | $\operatorname{codim}(\|Z\|,X)=\dim\mathcal O_{X,\xi_Z}$ | `supportCodimension_eq_stalkDim` | CORE |
| codimension-one subtype of the existing integral cycle generators | $\operatorname{PrimeDiv}(X)$ | `PrimeDivisor X` | CORE |
| existing divisor points identified with actual prime supports | $\operatorname{DivPt}(X)\simeq\operatorname{PrimeDiv}(X)$, $x\mapsto Z_x$ | `divisorPointEquivPrimeDivisor X` | CORE |
| existing point transport on supports, proved equal to the scheme-theoretic image | $e_{\mathrm{div}}: \operatorname{PrimeDiv}(X)\simeq\operatorname{PrimeDiv}(Y)$, $Z\mapsto e(Z)$ | `primeDivisorEquiv e`, `primeDivisorEquiv_val` | CORE |
| compatibility with the existing finite-cycle pushforward | $f_{*,\mathrm{cyc}}[Z_x]=[Z_{f(x)}]$ for closed immersions | `closedImmersionPushforward_pointSupport` | CORE |
| the existing signed local order, reindexed by actual prime supports | $\operatorname{ord}_Z(f)=\operatorname{ord}_{\xi_Z}(f)$; no second order | `primeDivisorOrder X Z` | CORE |
| actual support/field coefficient comparison | $\operatorname{ord}_Z(e^*f)=\operatorname{ord}_{e_{\mathrm{div}}(Z)}(f)$ | `primeDivisorOrder_iso` | CORE |

The support equivalence and codimension comparison hold for arbitrary
schemes. Integral locally Noetherian hypotheses are imposed only for the
existing signed coefficients. Codimension preservation is asserted for
isomorphisms, not for arbitrary closed immersions. The cycle module and
fundamental-cycle constructor are unchanged; no finite-support theorem,
graded principal divisor, quotient, projector, or relation package is
introduced by this checkpoint.

### Local and finite coefficient support (SP37)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| height-one prime containing a nonzero element is minimal over its principal ideal | $\mathfrak p\in\operatorname{Min}(a)$; theorem, not a new support object | `heightOne_mem_minimalPrimes_span` | CORE |
| finite numerator/denominator prime bound in an arbitrary-dimensional Noetherian domain | $\{\mathfrak p:\operatorname{ht}\mathfrak p=1,\ a\in\mathfrak p\text{ or }b\in\mathfrak p\}$ | `finite_heightOne_primes_containing`, `finite_heightOne_primes_containing_either` | CORE |
| representation through the actual affine section-to-function-field map | $f=a/b$, $a,b\in\Gamma(U,\mathcal O_X)\setminus\{0\}$; auxiliary sections, not chosen cycle coefficients | `exists_affine_fraction` | CORE |
| actual section/stalk/field compatibility and unit-germ criterion | prose only; existing canonical maps | `sectionToFunctionField_through_stalk`, `affineGerm_isUnit_iff` | CORE |
| existing coefficient vanishes outside the numerator/denominator prime loci | $a,b\notin\mathfrak p_x\Rightarrow\operatorname{ord}_x(f)=0$; no converse asserted | `divisorOrder_eq_zero_of_affine_fraction` | CORE |
| finite nonzero point-indexed coefficients in each affine chart | $\{x\in\operatorname{DivPt}(X):x\in U,\ \operatorname{ord}_x(f)\ne0\}$ | `finite_divisorPoints_in_affine` | CORE |
| locally finite family of the actual closed supports with nonzero coefficients | $(\|Z\|)_{Z\in\operatorname{PrimeDiv}(X),\ \operatorname{ord}_Z(f)\ne0}$; no new named projector or cycle type | `primeDivisorSupports_locallyFinite` | CORE |
| finite support of the same coefficient function under quasi-compactness, in its equivalent support/point indices | $\{Z:\operatorname{ord}_Z(f)\ne0\}$, equivalently $\{x:\operatorname{ord}_x(f)\ne0\}$ | `finite_primeDivisorOrder_support`, `finite_divisorOrder_support` | CORE |

Local finiteness refers to the actual closed-support family, not just
point-finiteness of a set. Quasi-compactness is explicit only at the global
finite-support endpoint. No normality or global ring-dimension bound is
used, and the full prime-divisor type need not be finite. SP38 assembles
the finite principal-divisor cycle in the existing ungraded module;
SP39 gives its homogeneous degree for an explicit dimension function.

### Finite principal-divisor cycles and isomorphism transport (SP38)

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| finite sum of the existing local orders on the existing prime-divisor subtype, embedded in the original cycle module | $\operatorname{div}_X(f)=\sum_Z\operatorname{ord}_Z(f)[Z]\in Z_{\mathrm{fin}}(X;\mathbf Z)$ | `principalDivisor X f` | CORE |
| full coefficient formula on the original integral generators | $\operatorname{ord}_Z(f)$ at prime divisors, zero elsewhere; no new coefficient function | `principalDivisor_apply_prime`, `principalDivisor_apply_of_not_prime`, `principalDivisor_apply` | CORE |
| exact finite support and coefficientwise zero criterion | $\operatorname{supp}(\operatorname{div}_X(f))=\{Z:\operatorname{ord}_Z(f)\ne0\}$ inside $\operatorname{IntSub}(X)$ | `principalDivisor_support`, `principalDivisor_eq_zero_iff` | CORE |
| identity, product, inverse and quotient laws in the same cycle module | $\operatorname{div}_X(fg)=\operatorname{div}_X(f)+\operatorname{div}_X(g)$, $\operatorname{div}_X(f^{-1})=-\operatorname{div}_X(f)$ | `principalDivisor_one`, `principalDivisor_mul`, `principalDivisor_inv`, `principalDivisor_div` | CORE |
| the same map bundled as a homomorphism, with an additive type tag on its multiplicative source | $\operatorname{div}_X:k(X)^\times\to Z_{\mathrm{fin}}(X;\mathbf Z)$; one map, not a second divisor | `principalDivisorAddHom`, `principalDivisorAddHom_ofMul` | CORE |
| actual ideal-image equivalence on all existing integral cycle generators | $Z\mapsto e(Z)$ on $\operatorname{IntSub}$; extends the previously proved $e_{\mathrm{div}}$ | `closedImageSubschemeEquiv e` and its application lemmas | CORE |
| the existing geometric pushforward preserves coefficients at actual image supports | $(e_{*,\mathrm{cyc}}c)(e(Z))=c(Z)$ | `closedImmersionPushforward_iso_eq_lmapDomain`, `_iso_apply_image`, `_iso_apply` | CORE |
| pushforward/function-field compatibility through an actual scheme isomorphism | $e_{*,\mathrm{cyc}}\operatorname{div}_X(e^*f)=\operatorname{div}_Y(f)$ | `principalDivisor_iso` | CORE |
| existing open restriction specialized to the same actual isomorphism | $e^*_{\mathrm{cyc}}\operatorname{div}_Y(f)=\operatorname{div}_X(e^*f)$ | `openRestriction_principalDivisor` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| explicit integer-valued point function, strictly increasing in closure-inclusion order and incrementing by one across covers | $\delta:X\to\mathbf Z$; both conditions of the standard definition | `DimensionFunction X` | CORE |
| degree of an existing integral support at its actual ambient generic point | $\deg_\delta(Z)=\delta(\xi_Z)$ | `supportDegree δ Z` | CORE |
| prime codimension gives immediate specialization and one-lower degree on an integral scheme | $\xi_Z\lessdot\eta_X$, $\deg_\delta(Z)=\delta(\eta_X)-1$ | `primeDivisor_covBy_genericPoint`, `supportDegree_primeDivisor` | CORE |
| degree of actual image support, even when only the support composite is closed | $\deg_\delta(f(Z))=\delta(f(\xi_Z))$ | `supportDegree_closedImageSubscheme` | CORE |
| actual closed point embedding preserves immediate specialization | prose only; follows from the order-convex image | `closedImmersion_covBy` | CORE |
| actual restriction of a dimension function, including both defining conditions | $\delta_W=\delta\circ\iota_W$, or $\delta\circ i$ | `DimensionFunction.comapClosedImmersion` and apply/id/comp laws | CORE |
| source degree equals actual ambient image degree | $\deg_{\delta\circ i}(Z)=\deg_\delta(i(Z))$; not codimension preservation | `supportDegree_comapClosedImmersion` | CORE |
| supported homogeneous submodule of the original cycle module | $Z^{\delta}_{\mathrm{fin},n}(X;R)\subset Z_{\mathrm{fin}}(X;R)$ | `cyclesOfDegree R δ n`, `mem_cyclesOfDegree_iff` | CORE |
| generator membership and degree detection; the converse requires nontrivial coefficients | $[Z]\in Z^{\delta}_{\mathrm{fin},n}\iff\deg_\delta(Z)=n$ for nontrivial $R$ | `single_mem_cyclesOfDegree`, `fundamentalCycle_mem_cyclesOfDegree`, `_iff` | CORE |
| cycles of distinct degrees intersect only at zero | $Z^{\delta}_{\mathrm{fin},n}\cap Z^{\delta}_{\mathrm{fin},m}=0$ for $n\ne m$ | `cyclesOfDegree_disjoint` | CORE |
| existing closed pushforward preserves compatible degrees; compatibility is proved for actual restriction | $i_{*,\mathrm{cyc}}Z^{\delta\circ i}_{\mathrm{fin},n}\subset Z^{\delta}_{\mathrm{fin},n}$ | `closedImmersionPushforward_mem_cyclesOfDegree`, `_comap` | CORE |
| existing finite principal divisor is one degree below the generic point | $\operatorname{div}_X(f)\in Z^{\delta}_{\mathrm{fin},\delta(\eta_X)-1}(X;\mathbf Z)$ | `principalDivisor_mem_cyclesOfDegree` | CORE |
| actual principal-divisor image has one-lower ambient carrier degree | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^{\delta}_{\mathrm{fin},\deg_\delta(W)-1}(X;\mathbf Z)$ | `closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree`, `principalDivisor_closedSupport_mem_cyclesOfDegree` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| derived finiteness of actual closed carriers | prose only; no new hypothesis package | `idealSubscheme_isLocallyNoetherian`, `idealSubscheme_compactSpace`, `idealSubscheme_isNoetherian` | CORE |
| finiteness transported by the actual support-to-image isomorphism | prose only; no new carrier | `closedImageSubscheme_isLocallyNoetherian`, `closedImageSubscheme_compactSpace` | CORE |
| the existing carrier principal cycle followed by the existing closed inclusion pushforward | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)$; a composite, not a second divisor | `ambientPrincipalDivisor W f` | CORE |
| actual principal-generator image identity, using the inverse contravariant function-field isomorphism | $i_{*,\mathrm{cyc}}(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)=(\iota_{i(W)})_{*,\mathrm{cyc}}\operatorname{div}_{i(W)}((e_W^*)^{-1}f)$ | `closedImmersionPushforward_ambientPrincipalDivisor` | CORE |
| actual integral degree-$n+1$ carriers with units in their function fields | $(W,f)$, $\deg_\delta(W)=n+1$, $f\in k(W)^\times$ | `PrincipalRelationData δ n` | CORE |
| local finiteness of actual nonempty carrier families is finiteness of the index under quasi-compactness | $(\|W_a\|)_{a\in A}$ locally finite $\Longleftrightarrow A$ finite | `principalRelationData_family_locallyFinite_iff` | CORE |
| the same ambient principal image in the supported degree submodule | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^\delta_{\mathrm{fin},n}(X;\mathbf Z)$ | `principalRelation δ n d` | CORE |
| absorb integer coefficients into actual rational-function powers | $\operatorname{div}_W(f^m)=m\operatorname{div}_W(f)$ | `PrincipalRelationData.zpow`, `principalRelation_zpow` | CORE |
| submodule generated by the actual degree-$n+1$ carrier principal images | $\mathcal R_n^\delta(X)$ | `principalRelations δ n` | CORE |
| exact unweighted finite-sum criterion and weighted finite-support criterion | $c\in\mathcal R_n^\delta\Longleftrightarrow c=\sum_{a=1}^r(\iota_{W_a})_{*,\mathrm{cyc}}\operatorname{div}_{W_a}(f_a)$ | `mem_principalRelations_iff_exists_list`, `_iff_exists_finsupp` | CORE |
| cycle difference is a genuine principal relation | $c\sim_{\mathrm{rat}}e$ | `RationallyEquivalent δ n c e` and its equivalence laws | CORE |
| quotient of the existing homogeneous integral cycles; canonical class map | $\mathrm{CH}_n^\delta(X)=Z^\delta_{\mathrm{fin},n}(X;\mathbf Z)/\mathcal R_n^\delta(X)$, $c\mapsto[c]$ | `ChowGroup δ n`, `classMap δ n` | CORE |
| exact quotient equality/kernel, surjectivity, and generator vanishing | $[c]=[e]\Longleftrightarrow c\sim_{\mathrm{rat}}e$, $\ker(c\mapsto[c])=\mathcal R_n^\delta$ | `classMap_eq_iff`, `classMap_eq_zero_iff`, `classMap_surjective`, `classMap_principalRelation` | CORE |
| restriction of the existing cycle map to compatible homogeneous submodules | $i_{*,\mathrm{cyc}}$ with domain $Z^{\delta_X}_{\mathrm{fin},n}$ | `gradedClosedImmersionPushforward` and val/id/comp laws | CORE |
| actual image carrier/function and its proved generator identity | $(W,f)\mapsto(i(W),(e_W^*)^{-1}f)$ | `PrincipalRelationData.closedImage`, `gradedClosedImmersionPushforward_principalRelation` | CORE |
| preservation of the generated submodule, deduced from geometry | $i_{*,\mathrm{cyc}}\mathcal R_n^{\delta_X}(X)\subseteq\mathcal R_n^{\delta_Y}(Y)$ | `principalRelations_le_comap_closedImmersionPushforward` | CORE |
| induced closed pushforward on the genuine quotient, with the existing cycle representative | $i_*:\mathrm{CH}_n^{\delta_X}(X)\to\mathrm{CH}_n^{\delta_Y}(Y)$, $[c]\mapsto[i_{*,\mathrm{cyc}}c]$ | `chowClosedImmersionPushforward` and classMap/id/comp laws | CORE |
| canonical specialization where degree compatibility is already proved | $\delta_X=\delta_Y\circ i$ | `chowClosedImmersionPushforward_restricted_classMap` | CORE |
| actual homogeneous-cycle equivalence with inverse the existing open restriction | $e_{*,\mathrm{cyc}}$, with inverse $e^*_{\mathrm{cyc}}$ | `gradedIsoEquiv`, `_val`, `_symm_val` | CORE |
| exact relation-submodule transport through the actual isomorphism | $e_{*,\mathrm{cyc}}\mathcal R_n^{\delta\circ e}(X)=\mathcal R_n^\delta(Y)$ | `principalRelations_map_gradedIsoEquiv` | CORE |
| induced quotient equivalence, identified with the existing closed quotient pushforward | $e_*:\mathrm{CH}_n^{\delta\circ e}(X)\xrightarrow{\sim}\mathrm{CH}_n^\delta(Y)$, with inverse induced by $e^*_{\mathrm{cyc}}$ | `chowIsoEquiv`, `_classMap`, `_symm_classMap`, `_toLinearMap` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual points of the closed carrier are the specialization interval below its ambient generic point | $\lvert W\rvert\simeq\{x:x\leq\xi_W\}$; the point map is the existing inclusion | `integralSubschemePointOrderIso W`, `_val` | CORE |
| sobriety identifies point chains with irreducible-closed chains | $\dim X$; no second dimension invariant | `topologicalKrullDim_eq_pointKrullDim` | CORE |
| actual carrier dimension is generic-point height; the whole integral scheme is the generic closure | $\dim W=\operatorname{height}(\xi_W)$, $h_X(x)=\dim\overline{\{x\}}$ | `ambientGenericPoint_height_eq_supportDim`, `point_height_eq_supportDim`, `genericPoint_height_eq_topologicalKrullDim` | CORE |
| finite dimension makes conversion to integer height lossless and gives strict specialization monotonicity | $h_X:X\to\mathbf Z_{\geq0}$ when $\dim X<\infty$; not yet called a dimension function in general | `point_height_ne_top`, `point_height_toNat_eq`, `point_height_toNat_strictMono` | CORE |
| explicit finite upper bound from actual polynomial presentations | proof-local bound only; not a sharp dimension formula or a new grading | `polynomialDimensionBound`, `mvPolynomial_ringKrullDim_le_bound`, `ringKrullDim_le_bound_of_surjective` | CORE |
| finite-type field algebras have finite dimension; nonempty order package additionally requires a nontrivial ring | $\dim A<\infty$ | `exists_ringKrullDim_le_of_finiteType`, `ringKrullDim_lt_top_of_finiteType`, `finiteRingKrullDim_of_finiteType` | CORE |
| bounds on actual affine spectra, quotient spectra and affine schemes with their section algebras | $\dim\operatorname{Spec}A<\infty$ | `spec_topologicalKrullDim_lt_top_of_finiteType`, `quotientSpec_topologicalKrullDim_lt_top_of_finiteType`, `affine_topologicalKrullDim_lt_top_of_finiteType` | CORE |
| actual stalk isomorphisms preserve point coheight | $\operatorname{coheight}_U(x)=\operatorname{coheight}_X(jx)$; not height or absolute-dimension preservation | `point_coheight_eq_of_isOpenImmersion` | CORE |
| finite chart bounds control global point-chain dimension | $\dim X\leq\max_i\dim U_i<\infty$ | `topologicalKrullDim_lt_top_of_finite_openCover` | CORE |
| the actual structural morphism supplies the affine finite-type algebras; quasi-compactness supplies the finite subcover | $X\to\operatorname{Spec}k$ finite type $\Longrightarrow\dim X<\infty$ | `affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType`, `topologicalKrullDim_lt_top_of_compact_locallyOfFiniteType`, `topologicalKrullDim_lt_top_of_finiteType` | CORE |
| under the actual dimension bound, every strict pair has heights zero and one | $x<y\Longrightarrow(h_X(x),h_X(y))=(0,1)$ if $\dim X\leq1$ | `point_height_le_one`, `point_height_eq_zero_and_eq_one_of_lt` | ROUTE |
| the existing dimension-function type instantiated by literal point height, with both laws proved | $\delta_X:=h_X$ under $\dim X\leq1$; no extra grading-law input | `DimensionFunction.ofKrullDimLEOne` and its apply/nonneg/value laws | ROUTE |
| the existing support degree and homogeneous-cycle test match actual carrier dimension | $\deg_{\delta_X}(W)=n\Longleftrightarrow\dim W=n$, $[W]\in Z^{\delta_X}_{\mathrm{fin},n}\Longleftrightarrow\dim W=n$ for nontrivial coefficients | `supportDegree_ofKrullDimLEOne_eq_iff`, `fundamentalCycle_mem_ofKrullDimLEOne_iff` | ROUTE |
| the actual polynomial spectrum and its constructed dimension function | $\mathbf A^1_k=\operatorname{Spec}k[T]$, $\delta_{\mathbf A^1_k}$ | `Examples.affineLine`, `affineLine_dimension`, `affineLineDimensionFunction` | ROUTE |
| the actual origin is the prime kernel of the constant-coefficient map | $o=V(T)$; no freely chosen closed point | `Examples.affineLineOriginIdeal_isMaximal`, `affineLineOrigin`, `affineLineOrigin_isClosed` | ROUTE |
| explicit positive-dimensional checks of the constructed grading | $\delta(\eta)=1$, $\delta(o)=0$ | `Examples.affineLineDimensionFunction_genericPoint`, `affineLineDimensionFunction_origin` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| canonical selected-prime unramifiedness premise, unchanged after its move | $h_I:\operatorname{Unram}_{q_I}(A\to S^I)$ | `NormalizationInertia.InertiaFixedRingUnramifiedAt` in `Inputs/FixedInertia.lean` | ROUTE |
| lossless unbundling into the existing Mathlib premise | prose only; no second input | `inertiaFixedRingUnramifiedAt_iff` | ROUTE |
| actual finite étale extension with its pullback identification | $\mathscr E_j(p)\ni E=(\bar p:\bar Y\to X,\;Y\simeq U\times_X\bar Y)$ | `LiteratureInputs.FiniteEtaleExtension j p` | ROUTE |
| selected existence proposition | $\mathscr E_j(p)\ne\varnothing$ | `FiniteEtaleExtensionHypothesis j p` | ROUTE |
| actual pullback and conjugation map on automorphisms | $\operatorname{res}_E:\operatorname{Aut}_X(\bar Y)\to\operatorname{Aut}_U(Y)$ | `FiniteEtaleExtension.restriction` | ROUTE |
| bijectivity of that selected restriction map | $\operatorname{Bijective}(\operatorname{res}_E)$ | `DeckExtensionHypothesis E` | ROUTE |
| restriction as a multiplicative equivalence, and action transport by its inverse | $\operatorname{res}_E:\operatorname{Aut}_X(\bar Y)\simeq\operatorname{Aut}_U(Y)$ / $\bar\rho_G=\operatorname{res}_E^{-1}\circ\rho_G$ | `FiniteEtaleExtension.deckEquiv` / `liftDeckAction` | ROUTE |
| selected additive exactness and surjectivity | $\operatorname{im}i=\ker r,\quad r\text{ surjective}$ | `ChowLocalizationHypotheses i r` | ROUTE |
| literal raw-lift fiber, reusing the canonical closure interface | $\operatorname{Cl}_r(e_\eta)=\{\Pi:r(\Pi)=e_\eta\}$ | `ChowLocalization.projectorClosure` | ROUTE |
| conditional boundary preimage of the existing defect, with a separate algebra restriction | $\operatorname{Def}(\Pi)\in\operatorname{im}i$, equivalently $i(b)=\Pi^2-\Pi$ | `ChowLocalization.convolutionDefect_mem_range` / `exists_boundary_of_convolutionDefect` | ROUTE |

The extension witness and its existence proposition are different objects;
neither implies the deck-restriction proposition. Additive exactness does not
assert that restriction is an algebra map. The boundary element `b` need not
be unique or zero. No new symbol is assigned to the input umbrella or to
routine adapters, and the old fixed-ring module imports the sole canonical
record rather than copying it.

### Marked block, realization, and Hodge target

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| augmentation ideal of the pointwise sheet algebra | $E_H=\ker(\operatorname{ev}_H)=(1-q_H)\triangleleft F_{\mathbf Q}(H)$ | `MarkedSheetProjector.Residual H` | ROUTE |
| unital residual corner, with the same underlying ideal and internal unit | $E_H^{\mathrm{corner}},\quad 1_{E_H^{\mathrm{corner}}}=1-q_H$ | `MarkedAugmentedAlgebra.ResidualCorner` | ROUTE |
| genuine selector/CRT product decomposition of algebras | $A_H\simeq_{\mathbf Q\text{-alg}}\mathbf Q\times E_H^{\mathrm{corner}}$ | `MarkedAugmentedAlgebra.selectorAlgebraDecomposition` | ROUTE |
| marked residual class | $a_H=q_H-1\in E_H$ | `MarkedSheetProjector.residualClass H` | ROUTE |
| multiplicative regular action of the commutative source | $\lambda_H:F_{\mathbf Q}(H)\to\operatorname{End}_{\mathbf Q}(F_{\mathbf Q}(H))$ | `MarkedAugmentedAlgebra.regularAction` | ROUTE |
| universal rational algebra with one distinguished idempotent | $\mathcal U=\mathbf Q\times\mathbf Q$ | `UniversalIdempotentAlgebra ℚ` | ROUTE |
| distinguished universal idempotent | $u=(1,0)\in\mathcal U$ | `UniversalIdempotentAlgebra.selector` | ROUTE |
| canonical algebra map determined by an idempotent $e$ in a rational algebra $B$ | $\varphi_e:\mathcal U\to B$, $(r,s)\mapsto re+s(1-e)$ | `UniversalIdempotentAlgebra.mapOfIdempotent` | ROUTE |
| linear intertwiner between two one-idempotent representations | $T:(V,\varphi_{e_V})\to(W,\varphi_{e_W})$ | `UniversalIdempotentAlgebra.RepresentationMorphism` | ROUTE |
| optional stronger full component-algebra presentation; not required by the active Galois route | $\iota_H:F_{\mathbf Q}(H)\to\Gamma_\eta$ | `MarkedSelectorAlgebraPresentation` | ROUTE |
| archived linear coset-average comparison, not an algebra map; retained name describes the archived source | $\ell_H(gH)=[g]e_H$ | `SchemeCorrespondence.sheetLinearization H` | ROUTE |
| graph projector attached to $\alpha$ | $P_\alpha(t,x)=(t,t\alpha)$ | `BlockGraphProjector.operator (R := ℚ) α` | ROUTE |
| projector onto the marked rational line | $P_0(t,x)=(t,0)$ | `BlockGraphProjector.diagonalOperator (R := ℚ) (M := H)` | ROUTE |
| change from diagonal to graph splitting | $U_\alpha(t,x)=(t,x+t\alpha)$ | `BlockGraphProjector.shear (R := ℚ) α` | ROUTE |
| canonical residual map and action square for a chosen projector, without ambient restriction | $\mathscr R_{\Pi}$ | `MarkedProjectorActionComparison` | ROUTE |
| detected Chow representative from the core comparison, without surjectivity or original idempotence | $\operatorname{cl}(D(\Pi))=\theta(a_H)$ | `MarkedProjectorActionComparison.cycleClass_decode_eq_generatedClass` | ROUTE |
| full lift using the chosen idempotent and surjective cancellation | $\Pi$; the same chosen element | `MarkedProjectorActionComparison.toAlgebraicProjectorLift` | ROUTE |
| extension-based specialization of the canonical comparison | $\mathscr R_{\Pi_x}$; no independent comparison fields | `MarkedSelectorActionComparison` | ROUTE |
| sheet specialization with prescribed generated class | $\mathscr R_{\alpha,x}$; retains the extension premise | `MarkedGaloisSelectorComparison` | ROUTE |
| rational linear map from the underlying module of the augmentation ideal | $\theta:E_H\to V$ | `MarkedProjectorActionComparison.residualRealization` | ROUTE |
| Tate-augmented residual map | $\Theta=\operatorname{id}_{\mathbf Q}\oplus\theta$ | `MarkedAugmentedAlgebra.productRealization` | ROUTE |
| realized projector equality as algebra-homomorphism composites | $\rho\circ\varphi_\Pi=\varphi_{P_\alpha}$ | `MarkedGaloisSelectorComparison.palomarTargetSquare` | ROUTE |
| compactified correspondence action | $\rho:\overline\Gamma\to\operatorname{End}_{\mathbf Q}(\mathbf Q\oplus V)$ | `RationalCorrespondenceAction` | CORE |
| generic/restriction/action package | $\mathscr C_{\mathrm{Chow}}$ | `RationalChowCorrespondenceModel` | ROUTE |
| independently specified target projector | $P$ | `RationalCohomologicalProjector` | ROUTE |
| lift with prescribed action | $\operatorname{Lift}_{\mathrm{CH}}(P)$ | `PrescribedChowProjectorLift` | ROUTE |
| one lift displayed as a commuting algebra-homomorphism square | $\rho\circ\varphi_\Pi=\varphi_P$ | `AlgebraicProjectorLift.realization_idempotentMap_square` | ROUTE |
| supplied cycle/Hodge model | $\mathscr H=(A,V,V_{\mathrm{Hdg}},\operatorname{cl})$ | `RationalHodgeCycleClassModel` | CORE |
| graph construction from a supplied Chow class, used in the Hodge-to-graph equivalence direction; not asserted linear | $C:A\to\Gamma$ | `ClassGraphProjectorConstruction.encode` | ROUTE |
| linear Chow detection compatible with lower-left cohomological evaluation | $D:\Gamma\to_{\mathbf Q} A$ | `ClassGraphProjectorDetection.decode` | ROUTE |
| rational Hodge membership | $\alpha\in V_{\mathrm{Hdg}}$ | `IsRationalHodgeClass M alpha` | CORE |
| cycle-class membership | $\alpha\in\operatorname{im}(\operatorname{cl})$ | `IsAlgebraicHodgeClass M alpha` | CORE |
| modeled rational Hodge target | $\mathrm{HC}_{\mathbf Q}(\mathscr H)$ | `RationalHodgeConjectureAt M` | CORE |
| equality-of-composites presentation of graph-projector coverage | $\forall\alpha\in V_{\mathrm{Hdg}},\ \exists\Pi:\rho\circ\varphi_\Pi=\varphi_{P_\alpha}$ | `EveryHodgeClassHasPalomarTargetSquare` | ROUTE |
| classwise marked-selector coverage | $\operatorname{Cov}_{\mathrm{Gal}}(\mathscr H,\rho)$ | `ClassDependentMarkedGaloisSelectorCoverage` | ROUTE |
| existential replacement for the same target class, used only for the reverse coverage implication; no equality with an original projector | named hypothesis; no new projector notation | `StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector` | ROUTE |

### Exact affine dimension and actual carrier comparison (SP42)

Here \(k\) is a field, \(A\) a commutative \(k\)-algebra and
\(\kappa(p)\) the actual residue field of \(A_p\). Transcendence
degrees in the dimension formulas are finite, so Lean's conversion from
cardinals to natural numbers is lossless. The existing \(h_X\) notation
denotes point-closure dimension; no general \(\delta_X\) is constructed
in this checkpoint.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| strict degree drop under an actual noninjective domain surjection with finite transcendence degree | $A\twoheadrightarrow B,\ \ker f\ne0\implies\operatorname{trdeg}_kB<\operatorname{trdeg}_kA$ | `trdeg_lt_of_surjective_of_not_injective` | CORE |
| strict decrease on actual prime quotients of a finite-type algebra | $p\subsetneq q\implies\operatorname{trdeg}_k(A/q)<\operatorname{trdeg}_k(A/p)$ | `primeQuotient_trdeg_strictAnti` / `primeQuotient_trdeg_toNat_strictAnti` | CORE |
| actual prime contraction and incomparability for an integral map | $P\subsetneq Q\implies f^{-1}P\subsetneq f^{-1}Q$ | `integral_specComap_strictMono` | CORE |
| actual finite-chain lift by lying over and going up, preserving length and the last contraction | $\ell(\widetilde c)=\ell(c),\ f^{-1}(\widetilde c_{\mathrm{last}})=c_{\mathrm{last}}$ | `exists_primeSeries_lift_of_injective_integral` | CORE |
| extended dimension comparison; injectivity is required for the reverse inequality and equality | $\dim S\le\dim R;\ R\hookrightarrow S\implies\dim R=\dim S$ | `ringKrullDim_le_of_integral` / `ringKrullDim_le_of_injective_integral` / `ringKrullDim_eq_of_injective_integral` | CORE |
| actual injective integral polynomial normalization; domain needed for the transcendence-degree identity, not the dimension lower bound | $k[T_1,\ldots,T_s]\hookrightarrow A,\ s=\operatorname{trdeg}_k A,\ s\le\dim A$ | `trdeg_eq_normalization_size` / `normalization_size_le_ringKrullDim` | CORE |
| independent normalization lower bound for domains and prime-chain upper bound for all finite-type algebras | $\operatorname{trdeg}_k A\le\dim A;\ \dim A\le\operatorname{trdeg}_k A$ | `trdeg_toNat_le_ringKrullDim_of_finiteType` / `ringKrullDim_le_trdeg_toNat_of_finiteType` | CORE |
| actual fraction-field algebra and scalar-tower comparison | $\operatorname{trdeg}_kA=\operatorname{trdeg}_k\operatorname{Frac}(A)$ | `trdeg_eq_of_isFractionRing` / `trdeg_eq_fractionRing` | CORE |
| finite-type domain dimension equality | $\dim A=\operatorname{trdeg}_k\operatorname{Frac}(A)$ | `ringKrullDim_eq_trdeg_toNat_of_finiteType` / `ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType` | CORE |
| proved sharp polynomial formula over a field | $\dim k[T_1,\ldots,T_n]=n$ | `mvPolynomial_ringKrullDim_eq_card` | CORE |
| topological dimension of the actual affine scheme of a finite-type domain | $\dim\operatorname{Spec}A=\operatorname{trdeg}_kA$ | `spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType` | CORE |
| opposite prime/scheme orders; actual quotient dimension | $\operatorname{coht}_{\operatorname{Spec}_{\mathrm{prime}}A}(p)=\operatorname{ht}_{X}(p)=\dim(A/p)$ | `prime_coheight_eq_quotientDim` / `spec_point_height_eq_prime_coheight` | CORE |
| existing reduced point carrier, not a new proxy type | $\dim\overline{\{p\}}_{\mathrm{red}}=\dim(A/p)$ | `spec_pointSupport_dimension_eq_quotientDim` | CORE |
| actual prime-localization residue field is a fraction field of the quotient | $\operatorname{trdeg}_k(A/p)=\operatorname{trdeg}_k\kappa(p)$ | `primeQuotient_trdeg_eq_residueField` | CORE |
| finite-type affine carrier dimension and the existing finite point-height value | $h_X(p)=\dim\overline{\{p\}}=\operatorname{trdeg}_k\kappa(p)$ | `spec_pointSupport_dimension_eq_residueField_trdeg` / `spec_point_height_toNat_eq_residueField_trdeg` | CORE |
| strict decrease on proper affine specialization | $p\subsetneq q\implies\operatorname{trdeg}_k\kappa(q)<\operatorname{trdeg}_k\kappa(p)$ | `prime_residueField_trdeg_toNat_strictAnti` | CORE |

No maximal-localization dimension identity, uniform maximal-chain theorem,
immediate-specialization unit step, general scheme chart/residue-field
transport or new dimension-function constructor is included in SP42.
The existing cycle module, Chow quotient and chosen projector are unchanged.

### Polynomial maximal height and closed-point local dimension (SP43)

Write \(R_n=k[T_1,\ldots,T_n]\), with \(k\) any field, and
\(X_n=\operatorname{Spec}R_n\). In the generic helper \(R\) is any
commutative ring and \(C:R\to R[T]\) is the actual constant-polynomial
homomorphism. No new cycle object or dimension-function package is used.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| contraction is a left inverse to ideal extension | $C^{-1}(pR[T])=p$ | `polynomial_comap_map_C` | CORE |
| actual order embedding of prime ideals | $\operatorname{Spec}_{\mathrm{prime}}R\hookrightarrow\operatorname{Spec}_{\mathrm{prime}}R[T],\ p\mapsto pR[T]$ | `polynomialPrimeExtension` | CORE |
| extending prime chains does not decrease height | $\operatorname{ht}(p)\leq\operatorname{ht}(pR[T])$ | `polynomialPrimeExtension_height_le` | CORE |
| polynomial quotient obstruction for any ideal | $pR[T]\notin\operatorname{MaxSpec}R[T]$ | `polynomial_map_C_not_isMaximal` | CORE |
| actual contracted-prime extension is strictly below a maximal ideal | $(m\cap R)R[T]\subsetneq m$ | `polynomial_map_comap_C_lt` | CORE |
| one extra height step, not an equality or catenarity assertion | $\operatorname{ht}(m\cap R)+1\leq\operatorname{ht}(m)$ | `polynomial_primeHeight_comap_add_one_le` | CORE |
| full height for every polynomial maximal ideal | $\operatorname{ht}_{R_n}(m)=n$ | `mvPolynomial_primeHeight_eq_card_of_isMaximal` / `mvPolynomial_height_eq_card_of_isMaximal` | CORE |
| dimension of the actual prime localization | $\dim(R_n)_m=n$ | `mvPolynomial_localization_dimension_of_isMaximal` | CORE |
| dimension of the actual structure-sheaf stalk | $\dim\mathcal O_{X_n,m}=n$ | `mvPolynomial_stalk_dimension_of_isMaximal` / `mvPolynomial_stalk_dimension_of_isClosed` | CORE |
| coheight in the scheme's closure-inclusion order | $\operatorname{coht}_{X_n}(m)=n$ | `mvPolynomial_closedPoint_coheight` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual finite integral subalgebra and determinant-trick annihilator; no global module finiteness | $y\in IS\implies\exists F\text{ monic},\ F(y)=0,\ F_i\in I^{d-i}\ (d=\deg F)$ | `exists_monic_annihilator_coeff_mem_pow_of_mem_map` / `exists_monic_annihilator_of_mem_map` | CORE |
| actual coefficient-map reduction of a monic polynomial | $\overline F=X^{\deg F}$ | `monic_map_eq_X_pow_of_lower_coeff_zero` | CORE |
| prime-ideal coefficient comparison for actual monic divisors, including scalar substitution | $G\mid F(aX),\ a\notin p,\ F_i\in p\ (i<\deg F)\implies G_j\in p\ (j<\deg G)$ | `coeff_mem_prime_of_monic_dvd_scaled` / `coeff_mem_prime_of_monic_dvd` | CORE |
| normal-base cancellation relative to the prescribed upstairs prime | $p\subseteq Q\cap R,\ a\notin p,\ ab\in pS\implies b\in Q$ | `mem_prime_of_mul_mem_map_of_isIntegrallyClosed` | CORE |
| proved going down for integral injections of domains with normal base; no new global instance | $p\subseteq Q\cap R\implies\exists P\subseteq Q,\ P\cap R=p$ | `hasGoingDown_of_isIntegrallyClosed` | CORE |
| integral incomparability plus reuse of the existing going-down height bound | $\operatorname{ht}_S(Q)=\operatorname{ht}_R(Q\cap R)$ | `primeHeight_eq_under_of_isIntegral_of_hasGoingDown` | CORE |
| full maximal height from the actual polynomial normalization, without a finite-type assumption on A | $g:k[T_1,\ldots,T_s]\hookrightarrow A\text{ integral}\implies\operatorname{ht}_A(m)=s$ | `normalization_primeHeight_eq_size` | CORE |
| finite-type-domain maximal heights | $\operatorname{ht}_A(m)=\operatorname{trdeg}_k A$ | `primeHeight_eq_trdeg_toNat_of_isMaximal` / `height_eq_trdeg_toNat_of_isMaximal` | CORE |
| dimension of the actual prime localization | $\dim A_m=\dim A$ | `localization_dimension_eq_of_isMaximal` | CORE |
| dimension of the actual structure-sheaf stalk on X=Spec(A) | $\dim\mathcal O_{X,m}=\dim A$ | `affine_stalk_dimension_of_isMaximal` / `affine_stalk_dimension_of_isClosed` | CORE |
| actual scheme-order coheight at a closed point | $\operatorname{coht}_X(m)=\operatorname{trdeg}_k A$ | `affine_closedPoint_coheight_eq_trdeg` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| chosen lifts of actual quotient variables and exact quotient square | $f:P\to B,\quad\pi_q f=g$ | `quotientPolynomialLift` / `quotient_comp_quotientPolynomialLift` | CORE |
| injection and nonzero polynomial images avoid the selected prime | $f\text{ injective},\ a\ne0\implies f(a)\notin q$ | `quotientPolynomialLift_injective` / `polynomial_notMem_of_quotient_injective` / `quotientPolynomialLift_notMem` | CORE |
| actual denominator image submonoid | $M\subseteq B\setminus q$ | `polynomial_map_nonZeroDivisors_le_primeCompl` / `polynomial_map_nonZeroDivisors_disjoint` | CORE |
| Noether normalization of the actual prime quotient and variable lift | $\exists n,f:\ \pi_q f\text{ injective and integral}$ | `exists_lifted_residue_normalization` | CORE |
| canonical localized algebra map, not a new carrier | $K\to B'$ | `genericFiberAlgebra` / `genericFiberAlgebra_algebraMap_eq` | CORE |
| exact compatibility of the actual scalar maps | $P\to K\to B',\quad k\to K\to B'$ | `genericFiberAlgebra_isScalarTower` / `genericFiber_isScalarTower_base` | CORE |
| actual localization pushout gives finite type | $B\text{ finite type over }P\implies B'\text{ finite type over }K$ | `genericFiber_finiteType` | CORE |
| domain and injection properties of the actual localization | $B\text{ domain},\ P\hookrightarrow B\implies B'\text{ domain},\ B\hookrightarrow B',\ K\hookrightarrow B'$ | `genericFiber_denominators_le_nonZeroDivisors` / `genericFiber_isDomain` / `genericFiber_localization_injective` / `genericFiber_baseField_injective` | CORE |
| actual contraction and primality, requiring only quotient injectivity | $\lambda^{-1}(q')=q,\quad q'\text{ prime}$ | `residueLocalization_comap_map` / `residueLocalization_map_isPrime` | CORE |
| field from the localized integral prime quotient, with exact kernel | $B'/q'\text{ field},\quad q'\text{ maximal}$ | `residueLocalization_map_isMaximal` | CORE |
| exact prime height under actual localization; no integral premise | $\operatorname{ht}_{B'}(q')=\operatorname{ht}_B(q)$ | `residueLocalization_primeHeight_map` | CORE |
| supplied-map and fully constructed finite-type localization endpoints | $B'/K\text{ finite type},\ q'\text{ maximal},\ \lambda^{-1}(q')=q,\ \operatorname{ht}(q')=\operatorname{ht}(q)$ | `residueNormalization_localization` / `exists_residueNormalization_localization` | CORE |
| SP44 applied to the actual domain generic fiber | $\operatorname{ht}_B(q)=\operatorname{trdeg}_K B'$ | `primeHeight_eq_residueNormalization_trdeg` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| full cardinal degree preserved by the actual localization; universe lifts in the general form | $\operatorname{trdeg}_k B=\operatorname{trdeg}_k M^{-1}B$ | `lift_trdeg_eq_of_isLocalization` / `trdeg_eq_of_isLocalization` | CORE |
| numeric consequence of cardinal invariance; not a finiteness assertion | Numeric projection of the preceding equality; no independent invariant | `trdeg_toNat_eq_of_isLocalization` | CORE |
| canonical fraction-field tower for an actual injective polynomial map, with no integral premise | $n+\operatorname{trdeg}_K B'=\operatorname{trdeg}_k B$ | `polynomial_genericFiber_trdeg_toNat_add` | CORE |
| original-field dimension formula for every prime of a finite-type domain | $\operatorname{ht}_B(q)+\operatorname{trdeg}_k(B/q)=\operatorname{trdeg}_k B$ | `primeHeight_add_quotient_trdeg_eq` / `height_add_quotient_trdeg_eq` | CORE |
| reuse of the existing actual prime-localization residue field | $\operatorname{ht}_B(q)+\operatorname{trdeg}_k\kappa(q)=\operatorname{trdeg}_k B$ | `primeHeight_add_residueField_trdeg_eq` | CORE |
| actual prime quotient dimension plus ordinary ideal height | $\operatorname{ht}_B(q)+\dim(B/q)=\dim B$ | `height_add_quotient_dimension_eq` | CORE |
| dimension of the actual prime localization | $\dim B_q+\dim(B/q)=\dim B$ | `localization_dimension_add_quotient_dimension_eq` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| primality under the actual quotient map, for a comparable prime pair | $p\subseteq q\implies\bar q=q(B/p)\text{ prime}$ | `primeQuotient_map_isPrime` | CORE |
| actual quotient-spectrum correspondence on a prime cover | $p\lessdot q\implies0\lessdot\bar q\text{ in }\operatorname{Spec}(B/p)$ | `primeQuotient_bot_covBy_map` | CORE |
| full prime height of the actual image ideal | $\operatorname{ht}_{B/p}(\bar q)=1$ | `primeQuotient_primeHeight_eq_one_of_covBy` | CORE |
| finite transcendence-degree unit drop between actual prime quotients | $\operatorname{trdeg}_k(B/q)+1=\operatorname{trdeg}_k(B/p)$ | `primeQuotient_trdeg_toNat_add_one_of_covBy` | CORE |
| same unit drop in the existing actual prime-localization residue fields | $\operatorname{trdeg}_k\kappa(q)+1=\operatorname{trdeg}_k\kappa(p)$ | `prime_residueField_trdeg_toNat_add_one_of_covBy` | CORE |
| actual quotient-ring dimension step | $\dim(B/q)+1=\dim(B/p)$ | `primeQuotient_dimension_add_one_of_covBy` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| expose the existing identity-on-points comparison, with dual prime order | $(\operatorname{Spec}A,\leq_{\mathrm{cl}})\simeq(\operatorname{Spec}A,\subseteq)^{\mathrm{op}}$ | `specPointOrderIso` | CORE |
| actual affine constructor and literal prime-residue-field evaluation | $\delta_{A/k}(x)=\operatorname{trdeg}_k\kappa(x)$ | `DimensionFunction.ofSpecFiniteType`, `ofSpecFiniteType_apply` | CORE |
| equality to actual finite closure height | $\delta_{A/k}(x)=h_{\operatorname{Spec}A}(x)=\dim\overline{\{x\}}$ | `DimensionFunction.ofSpecFiniteType_eq_pointHeight` | CORE |
| nonnegative point values | $0\leq\delta_{A/k}(x)$ | `DimensionFunction.ofSpecFiniteType_nonneg` | CORE |
| exact actual-carrier dimension test for natural n | $\deg_{\delta_{A/k}}W=n\iff\dim W=n$ | `supportDegree_ofSpecFiniteType_eq_iff` | CORE |
| existing homogeneous-cycle membership detects carrier dimension | $[W]\in Z^{\delta_{A/k}}_{\mathrm{fin},n}(\operatorname{Spec}A;R)\iff\dim W=n$ | `fundamentalCycle_mem_ofSpecFiniteType_iff` | CORE |
| actual affine structural-morphism constructor and literal point height | $\delta_{X/k}(x)=h_X(x)$ | `DimensionFunction.ofAffineLocallyOfFiniteType`, `ofAffineLocallyOfFiniteType_apply` | CORE |
| nonnegative structural-affine values | $0\leq\delta_{X/k}(x)$ | `DimensionFunction.ofAffineLocallyOfFiniteType_nonneg` | CORE |
| geometric degree of actual integral closed carriers | $\deg_{\delta_{X/k}}W=n\iff\dim W=n$ | `supportDegree_ofAffineLocallyOfFiniteType_eq_iff` | CORE |
| the same criterion in the existing cycle module on X | $[W]\in Z^{\delta_{X/k}}_{\mathrm{fin},n}(X;R)\iff\dim W=n$ | `fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual structural ring map and its locally installed algebra | $k\to\Gamma(\operatorname{Spec}k,\mathcal O)\xrightarrow{p^\sharp}\Gamma(X,\mathcal O_X)\xrightarrow{\operatorname{ev}_x}\kappa_X(x)$ | `residueFieldBaseMap`, `residueFieldBaseAlgebra`, `residueFieldBaseAlgebra_algebraMap` | CORE |
| actual evaluation naturality retains the structural action | $u_x^*\circ\operatorname{ev}_{u(x)}\circ p^\sharp=\operatorname{ev}_x\circ(p\circ u)^\sharp$ on global base constants | `residueFieldBaseMap_comp` | CORE |
| existing geometric residue map bundled as a base-algebra map | $u_x^*:\kappa_Y(u(x))\to_k\kappa_X(x)$ | `residueFieldBaseAlgHom`, `residueFieldBaseAlgHom_apply` | CORE |
| same map is a base-algebra equivalence for an actual open immersion | $u_x^*:\kappa_Y(u(x))\simeq_k\kappa_X(x)$ | `residueFieldBaseAlgEquivOfIsOpenImmersion`, `_apply` | CORE |
| actual stalk/localization-induced residue-field equivalence | $\psi_{A,x}:\kappa_{\operatorname{Spec}A}(x)\simeq\kappa(\mathfrak p_x)$ | `specResidueFieldEquiv` | CORE |
| compatibility with every actual A-constant | $\psi_{A,x}(\operatorname{ev}_x(a))=\overline a\in\kappa(\mathfrak p_x)$ | `specResidueFieldEquiv_evaluation` | CORE |
| same canonical map with structural base compatibility proved | $\psi_{A,x}:\kappa_{\operatorname{Spec}A}(x)\simeq_k\kappa(\mathfrak p_x)$ | `specResidueFieldAlgEquiv`, `specResidueFieldAlgEquiv_apply` | CORE |
| full-cardinal comparison over a field | $\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)=\operatorname{trdeg}_k\kappa(\mathfrak p_x)$ | `spec_schemeResidueField_trdeg_eq` | CORE |
| finite type of A proves finite residue transcendence degree | $\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)<\aleph_0$ | `spec_schemeResidueField_trdeg_lt_aleph0` | CORE |
| existing affine function evaluated in the actual scheme residue field | $\delta_{A/k}(x)=\operatorname{trdeg}_k\kappa_{\operatorname{Spec}A}(x)$ | `DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg` | CORE |
| full-cardinal invariance for actual open immersions | $\operatorname{trdeg}_k\kappa_Y(u(x))=\operatorname{trdeg}_k\kappa_X(x)$ | `residueFieldBase_trdeg_eq_of_isOpenImmersion` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| expose the existing actual-isomorphism height theorem, proof unchanged | $h_Y(e(x))=h_X(x)$ for $e:X\simeq Y$; theorem only | `point_height_iso` in `AffineSchemeDimensionFunction.lean` | CORE |
| actual structural residue degree is finite for affine locally finite-type X | $\operatorname{trdeg}_k\kappa_X(x)<\aleph_0$ | `affine_schemeResidueField_trdeg_lt_aleph0` | CORE |
| identify the existing height-defined affine function with actual structural residue degree | $\delta_{X/k}(x)=h_X(x)=\operatorname{trdeg}_k\kappa_X(x)$ | `DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg` | CORE |
| compare existing dimension values under an affine open immersion over k | $\delta_{X/k}(x)=\delta_{Y/k}(f(x))$ for open $f:X\to Y$, with source structural map $p\circ f$ | `DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| every actual structural residue degree is finite under locally finite type | $\operatorname{trdeg}_k\kappa_X(x)<\aleph_0$ | `schemeResidueField_trdeg_lt_aleph0` | CORE |
| existing affine-chart value equals the ambient structural residue degree | $\delta_{U/k}(u)=\operatorname{trdeg}_k\kappa_X(i(u))$ for open $i:U\to X$ | `affineChart_dimension_eq_schemeResidueField_trdeg` | CORE |
| values on two actual affine charts agree at the same ambient point | $i(u)=j(v)\Rightarrow\delta_{U/k}(u)=\delta_{V/k}(v)$ | `affineChart_dimension_eq_of_eq_image` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| a common actual affine open for a specialization pair, on any scheme | $x\leq y\Rightarrow\exists U\text{ affine open},\ x,y\in U$ | `exists_isAffineOpen_mem_of_le` | CORE |
| the global structural residue-degree dimension function, with both laws proved | $\delta_{X/k}:X\to\mathbb Z$, $x<y\Rightarrow\delta(x)<\delta(y)$, $x\lessdot y\Rightarrow\delta(y)=\delta(x)+1$ | `DimensionFunction.ofLocallyOfFiniteType` | CORE |
| evaluation using the actual structural residue field | $\delta_{X/k}(x)=\operatorname{trdeg}_k\kappa_X(x)$ | `DimensionFunction.ofLocallyOfFiniteType_apply` | CORE |
| the field normalization is nonnegative | $0\leq\delta_{X/k}(x)$ | `DimensionFunction.ofLocallyOfFiniteType_nonneg` | CORE |
| equality of the whole global and existing affine dimension-function objects | $\delta_{X/k}^{\mathrm{global}}=\delta_{X/k}^{\mathrm{affine}}$ for affine $X$; superscripts only for this comparison | `DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType` | CORE |
| arbitrary actual open immersions preserve the global values over the field | $\delta_{X/k}(x)=\delta_{Y/k}(f(x))$, with source structural map $p\circ f$ | `DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| literal extended point height equals the finite structural value | $h_X(x)=\delta_{X/k}(x)$ in $\mathbb N\cup\{\infty\}$ | `point_height_eq_ofLocallyOfFiniteType` | CORE |
| pointwise finite height without a global dimension bound | $h_X(x)<\infty$ | `point_height_ne_top_of_locallyOfFiniteType` | CORE |
| the existing global function equals integer point height | $\delta_{X/k}(x)=h_X(x)\in\mathbb Z$ | `DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight` | CORE |
| dimension of the actual reduced point-closure carrier | $\dim\overline{\{x\}}=\delta_{X/k}(x)$ | `pointSupport_dimension_eq_ofLocallyOfFiniteType` | CORE |
| the existing support degree detects actual carrier dimension | $\deg_{\delta_{X/k}}W=n\iff\dim W=n$, $n\in\mathbb N$ | `supportDegree_ofLocallyOfFiniteType_eq_iff` | CORE |
| existing homogeneous fundamental cycles detect actual dimension | $[W]\in Z^{\delta_{X/k}}_{\mathrm{fin},n}(X;R)\iff\dim W=n$, for nontrivial $R$ | `fundamentalCycle_mem_ofLocallyOfFiniteType_iff` | CORE |
| open immersions over the field preserve actual point height in the stated setting | $h_U(u)=h_X(i(u))$, for locally finite-type $X/k$ and open $i:U\to X$ | `point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| finite actual ambient dimension from the generic structural value | $\dim X=\delta(\eta_X)=d$ in the full extended dimension type | `integral_topologicalKrullDim_eq_ofLocallyOfFiniteType` | CORE |
| actual point coheight is finite | $\operatorname{coht}_X(x)<\infty$ | `point_coheight_ne_top_of_integral_locallyOfFiniteType` | CORE |
| actual coheight measures the drop from the generic value | $\operatorname{coht}_X(x)+\delta(x)=d$ | `point_coheight_add_dimension_of_integral_locallyOfFiniteType` | CORE |
| the existing integral support has finite chain codimension | $\operatorname{codim}_X W<\infty$ | `supportCodimension_ne_top_of_integral_locallyOfFiniteType` | CORE |
| existing chain codimension plus existing support degree | $\operatorname{codim}_X W+\deg_\delta W=d$ | `supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType` | CORE |
| actual carrier and ambient dimensions in the extended dimension type | $\operatorname{codim}_X W+\dim W=\dim X$ | `supportCodimension_add_dimension_of_integral_locallyOfFiniteType` | CORE |
| degree detects actual codimension for every natural n | $\deg_\delta W=d-n\iff\operatorname{codim}_X W=n$ | `supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType` | CORE |
| coefficient-one homogeneity detects actual codimension | $[W]\in Z^\delta_{\mathrm{fin},d-n}(X;R)\iff\operatorname{codim}_X W=n$, for nontrivial $R$ | `fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType` | CORE |
| the existing homogeneous submodule consists of finite codimension-n cycles | $c\in Z^\delta_{\mathrm{fin},d-n}(X;R)\iff\forall W,\ c(W)\ne0\Rightarrow\operatorname{codim}_X W=n$ | `mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| reindex the existing dependent pair by actual codimension | $(W,f)$ with $\deg_\delta W=d-n\;\longleftrightarrow\;(W,f)$ with $\operatorname{codim}_X W=n$, always $f\in k(W)^\times$ | `principalRelationDataEquivCodimension` | CORE |
| forward reindexing preserves the literal integral closed carrier | prose only; the same $W$ | `principalRelationDataEquivCodimension_apply_carrier` | CORE |
| forward reindexing preserves the literal rational function | prose only; the same $f\in k(W)^\times$ | `principalRelationDataEquivCodimension_apply_function` | CORE |
| inverse reindexing preserves the literal integral closed carrier | prose only; the same $W$ | `principalRelationDataEquivCodimension_symm_apply_carrier` | CORE |
| inverse reindexing preserves the literal rational function | prose only; the same $f\in k(W)^\times$ | `principalRelationDataEquivCodimension_symm_apply_function` | CORE |
| the reindexed generator is the existing ambient principal divisor | $(\iota_W)_{*,\mathrm{cyc}}\operatorname{div}_W(f)\in Z^\delta_{\mathrm{fin},d-(n+1)}(X;\mathbf Z)$ | `principalRelation_equivCodimension_symm_coe` | CORE |
| generic-degree relation data would require an impossible larger carrier degree | no $(W,f)$ with $\deg_\delta W=d_\delta+1$ | `isEmpty_principalRelationData_genericDegree` | CORE |
| the existing relation span vanishes in generic degree | $\mathcal R_{d_\delta}^{\delta}(X)=0$ | `principalRelations_genericDegree_eq_bot` | CORE |
| rational equivalence is equality in the existing generic-degree cycle module | $c\sim_{\mathrm{rat}}e\iff c=e$ in $Z^\delta_{\mathrm{fin},d_\delta}(X;\mathbf Z)$ | `rationallyEquivalent_genericDegree_iff_eq` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| coefficient extension on the existing homogeneous submodule | $z\mapsto z_{\mathbb Q}:Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)\to Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)$ | `cyclesOfDegreeRationalize` | CORE |
| literal coefficient cast at the same support | $z_{\mathbb Q}(W)=(z(W):\mathbb Q)$ | `cyclesOfDegreeRationalize_apply` | CORE |
| coefficient injectivity before any relation quotient | prose only; injectivity of $z\mapsto z_{\mathbb Q}$ | `cyclesOfDegreeRationalize_injective` | CORE |
| the same integral support, with its coefficient cast | $a[W]\mapsto(a:\mathbb Q)[W]$ | `cyclesOfDegreeRationalize_single` | CORE |
| rational homogeneous cycles are scalar extension of the integer module | $\mathbb Q\otimes_{\mathbb Z}Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)\simeq Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)$ | `cyclesOfDegreeRationalizationEquiv` | CORE |
| scalar extension preserves actual cycle representatives | $q\otimes z\mapsto qz_{\mathbb Q}$ | `cyclesOfDegreeRationalizationEquiv_tmul` | CORE |
| the tensor unit recovers the coefficient cast | $1\otimes z\mapsto z_{\mathbb Q}$ | `cyclesOfDegreeRationalizationEquiv_one_tmul` | CORE |
| universal-property quotient comparison for an existing scalar-extension model $E:S\otimes_R M\simeq N$ | $S\otimes_R(M/\langle r_i\rangle_R)\simeq N/\langle f(r_i)\rangle_S$ when $E(s\otimes m)=s f(m)$ | `scalarExtensionQuotientEquiv` | CORE |
| the generic comparison retains quotient representatives | $s\otimes[m]\mapsto[s f(m)]$ | `scalarExtensionQuotientEquiv_tmul_mk` | CORE |
| rational span of coefficient-extended actual principal divisors | $\mathcal R_m^\delta(X;\mathbb Q)=\operatorname{span}_{\mathbb Q}\{((\iota_W)_*\operatorname{div}_W(f))_{\mathbb Q}:\deg_\delta W=m+1\}$ | `rationalPrincipalRelations` | CORE |
| rational cycles modulo that same generator prescription | $\operatorname{CH}_m^\delta(X;\mathbb Q)=Z^\delta_{\mathrm{fin},m}(X;\mathbb Q)/\mathcal R_m^\delta(X;\mathbb Q)$ | `RationalChowGroup` | CORE |
| quotient class map on rational homogeneous cycles | $z\mapsto[z]_{\mathbb Q}$ | `rationalClassMap` | CORE |
| the actual rational relation space is the class-map kernel | $[z]_{\mathbb Q}=0\iff z\in\mathcal R_m^\delta(X;\mathbb Q)$ | `rationalClassMap_eq_zero_iff` | CORE |
| every rational class has an actual finite homogeneous representative | prose only; surjectivity of $z\mapsto[z]_{\mathbb Q}$ | `rationalClassMap_surjective` | CORE |
| each existing principal generator vanishes after coefficient extension | $[((\iota_W)_*\operatorname{div}_W(f))_{\mathbb Q}]_{\mathbb Q}=0$ | `rationalClassMap_principalRelation` | CORE |
| tensor extension of the integer Chow quotient equals the rational quotient | $\mathbb Q\otimes_{\mathbb Z}\operatorname{CH}_m^\delta(X)\simeq\operatorname{CH}_m^\delta(X;\mathbb Q)$ | `chowRationalizationEquiv` | CORE |
| the Chow comparison preserves scalar-weighted representatives | $q\otimes[z]\mapsto[qz_{\mathbb Q}]_{\mathbb Q}$ | `chowRationalizationEquiv_tmul_classMap` | CORE |
| canonical coefficient extension on integral Chow classes | $\operatorname{CH}_m^\delta(X)\to\operatorname{CH}_m^\delta(X;\mathbb Q)$; ordinary arrow | `chowRationalize` | CORE |
| the canonical rationalization commutes with the existing class map | $[z]\mapsto[z_{\mathbb Q}]_{\mathbb Q}$ | `chowRationalize_classMap` | CORE |
| the rational relation span also vanishes in generic degree | $\mathcal R_{\delta(\eta_X)}^\delta(X;\mathbb Q)=0$ on integral Noetherian $X$ | `rationalPrincipalRelations_genericDegree_eq_bot` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| the existing geometric pushforward restricted to homogeneous cycles over any semiring | $i_{*,\mathrm{cyc}}:Z^{\delta_X}_{\mathrm{fin},m}(X;R)\to Z^{\delta_Y}_{\mathrm{fin},m}(Y;R)$ | `gradedClosedImmersionPushforwardWithCoefficients` | CORE |
| its underlying finite cycle is the existing actual closed pushforward | prose only; the same $i_{*,\mathrm{cyc}}z$ | `gradedClosedImmersionPushforwardWithCoefficients_val` | CORE |
| graded identity over any coefficient semiring | $(\mathrm{id}_X)_{*,\mathrm{cyc}}=\mathrm{id}$ | `gradedClosedImmersionPushforwardWithCoefficients_id` | CORE |
| graded composition is the existing geometric composition | $j_{*,\mathrm{cyc}}i_{*,\mathrm{cyc}}=(j\circ i)_{*,\mathrm{cyc}}$ | `gradedClosedImmersionPushforwardWithCoefficients_comp` | CORE |
| actual ungraded closed pushforward commutes with coefficient cast | $i_{*,\mathrm{cyc}}(z_{\mathbb Q})=(i_{*,\mathrm{cyc}}z)_{\mathbb Q}$ | `closedImmersionPushforward_rationalize` | CORE |
| the same coefficient square on the existing homogeneous submodules | prose only; the preceding equality in degree $m$ | `gradedClosedImmersionPushforward_rationalize` | CORE |
| actual open restriction along an isomorphism has the canonical restricted degree | $e^*z\in Z^{e^*\delta}_{\mathrm{fin},m}(X;R)$ for $z\in Z^\delta_{\mathrm{fin},m}(Y;R)$ | `openRestriction_iso_mem_cyclesOfDegree` | CORE |
| preservation of the rational span of the same actual principal generators | $i_{*,\mathrm{cyc}}\mathcal R_m^{\delta_X}(X;\mathbb Q)\subseteq\mathcal R_m^{\delta_Y}(Y;\mathbb Q)$ | `rationalPrincipalRelations_le_comap_closedImmersionPushforward` | CORE |
| descent of actual closed pushforward to the rational quotient | $i_*:\operatorname{CH}_m^{\delta_X}(X;\mathbb Q)\to\operatorname{CH}_m^{\delta_Y}(Y;\mathbb Q)$ | `rationalChowClosedImmersionPushforward` | CORE |
| the quotient map preserves the actual cycle formula | $i_*[z]_{\mathbb Q}=[i_{*,\mathrm{cyc}}z]_{\mathbb Q}$ | `rationalChowClosedImmersionPushforward_classMap` | CORE |
| canonical dimension restriction supplies the support-degree premise | prose only; the same formula for $\delta_X=i^*\delta_Y$ | `rationalChowClosedImmersionPushforward_restricted_classMap` | CORE |
| rational quotient identity | $(\mathrm{id}_X)_*=\mathrm{id}$ | `rationalChowClosedImmersionPushforward_id` | CORE |
| rational quotient composition | $j_*i_*=(j\circ i)_*$ | `rationalChowClosedImmersionPushforward_comp` | CORE |
| the integral-to-rational class map commutes with actual pushforward | prose only; the coefficient-extension square for $i_*$ | `rationalChowClosedImmersionPushforward_chowRationalize` | CORE |
| the descended rational map is the scalar extension of integral Chow pushforward | prose only; the tensor-comparison square with $1\otimes i_*$ | `rationalChowClosedImmersionPushforward_chowRationalizationEquiv` | CORE |
| scalar extension of the existing integral Chow isomorphism in the actual rational quotient models | $e_*:\operatorname{CH}_m^{e^*\delta}(X;\mathbb Q)\xrightarrow{\sim}\operatorname{CH}_m^\delta(Y;\mathbb Q)$ | `rationalChowIsoEquiv` | CORE |
| the rational isomorphism agrees with tensoring the existing integral isomorphism | prose only; the same tensor-comparison square | `rationalChowIsoEquiv_chowRationalizationEquiv` | CORE |
| its forward map is the already descended rational closed pushforward | prose only; the same $e_*$ | `rationalChowIsoEquiv_toLinearMap` | CORE |
| forward isomorphism preserves actual closed-image representatives | $e_*[z]_{\mathbb Q}=[e_{*,\mathrm{cyc}}z]_{\mathbb Q}$ | `rationalChowIsoEquiv_classMap` | CORE |
| inverse isomorphism is actual open restriction on representatives | $e_*^{-1}[z]_{\mathbb Q}=[e^*z]_{\mathbb Q}$ | `rationalChowIsoEquiv_symm_classMap` | CORE |
| rationalization commutes with the existing integral Chow isomorphism | prose only; the corresponding class-map square | `rationalChowIsoEquiv_chowRationalize` | CORE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| the actual generic-stalk isomorphism induced by the open immersion | $j^*:k(Y)\xrightarrow{\sim}k(X)$ | `functionFieldIsoOfOpenImmersion` | ROUTE |
| the same map as a ring equivalence, not another field construction | prose only; the same $j^*$ | `functionFieldEquivOfOpenImmersion` | ROUTE |
| the actual generic-stalk map commutes with specialization from each local stalk | prose only; the local-to-generic stalk square | `functionFieldIsoOfOpenImmersion_stalkSpecializes` | ROUTE |
| the same square for the canonical local-ring algebra maps | $j^*(a)=j_x^{\#}(a)$ after the canonical maps into $k(X)$, for $a\in\mathcal O_{Y,j(x)}$ | `functionFieldEquivOfOpenImmersion_algebraMap` | ROUTE |
| actual local-ring isomorphism preserves Krull dimension | $\dim\mathcal O_{Y,j(x)}=\dim\mathcal O_{X,x}$ | `stalkDimension_openImmersion` | ROUTE |
| the actual point map embeds the one-dimensional local-ring locus | $j_1:\operatorname{DivPt}(X)\hookrightarrow\operatorname{DivPt}(Y)$ | `divisorPointEmbedding` | ROUTE |
| the embedded divisor point has the unchanged actual point image | $j_1(x)=j(x)$ on underlying points | `divisorPointEmbedding_val` | ROUTE |
| exact range of the divisor-point embedding | $y\in\operatorname{im}(j_1)\iff y\in j(X)$ for $y\in\operatorname{DivPt}(Y)$ | `mem_range_divisorPointEmbedding_iff` | ROUTE |
| the old isomorphism point equivalence has this same forward map | prose only; $j_1=e_1$ when $j=e.\mathrm{hom}$, by definitional equality | `divisorPointEmbedding_iso` | ROUTE |
| the same signed local order is preserved through the actual field/stalk maps | $\operatorname{ord}_x(j^*f)=\operatorname{ord}_{j_1(x)}(f)$ | `divisorOrder_openImmersion` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| reduced ambient closure through the existing point/support construction | $\overline{j(W)}_{\mathrm{red}}=\operatorname{pointSupport}_X(j(\xi_W))$ | `openClosureSubscheme` | ROUTE |
| its literal ambient generic point | $\xi_{\overline{j(W)}_{\mathrm{red}}}=j(\xi_W)$ | `openClosureSubscheme_ambientGenericPoint` | ROUTE |
| the nonempty restricted carrier has the same ambient generic point | $j(\xi_{Z\cap U})=\xi_Z$ | `ambientGenericPoint_openRestrictionSubscheme` | ROUTE |
| exact criterion for a carrier to meet the open | $Z\cap U\ne\varnothing\iff\xi_Z\in j(U)$ | `nonempty_openRestrictionSubscheme_iff` | ROUTE |
| restriction recovers the actual original ideal sheaf | $j^*\mathcal I_{\overline{j(W)}_{\mathrm{red}}}=\mathcal I_W$ | `openClosureSubscheme_comap` | ROUTE |
| ambient reduced closure recovers each carrier meeting the open | $\overline{j(Z\cap U)}_{\mathrm{red}}=Z$ when $Z\cap U\ne\varnothing$ | `openClosureSubscheme_openRestrictionSubscheme` | ROUTE |
| preservation of actual chain codimension under reduced ambient closure | $\operatorname{codim}_X\overline{j(W)}_{\mathrm{red}}=\operatorname{codim}_U W$ | `supportCodimension_openClosureSubscheme` | ROUTE |
| preservation of chain codimension under nonempty open restriction | $\operatorname{codim}_U(Z\cap U)=\operatorname{codim}_X Z$ | `supportCodimension_openRestrictionSubscheme` | ROUTE |
| on prime supports, reduced closure agrees with the existing divisor-point embedding | prose only; the same $j_1$ through the point/prime-support equivalences | `openClosureSubscheme_divisorPoint` | ROUTE |
| exact coefficient formula for the existing finite-cycle restriction | $(j^*c)(W)=c(\overline{j(W)}_{\mathrm{red}})$ | `openRestriction_apply` | ROUTE |
| signed local orders agree on the corresponding actual prime supports | $\operatorname{ord}_W(j^*f)=\operatorname{ord}_{\overline{j(W)}_{\mathrm{red}}}(f)$ | `primeDivisorOrder_openImmersion` | ROUTE |
| the existing finite principal divisor commutes with actual open restriction | $j^*\operatorname{div}_X(f)=\operatorname{div}_U(j^*f)$ | `openRestriction_principalDivisor_of_isOpenImmersion` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| actual open point maps preserve immediate specialization | $x\mathbin{\lessdot}y\Rightarrow j(x)\mathbin{\lessdot}j(y)$ in the scheme specialization orders | `openImmersion_covBy` | ROUTE |
| literal composition with the actual open point map, with both dimension-function laws proved | $\delta_U=\delta\circ j$ | `DimensionFunction.comapOpenImmersion` | ROUTE |
| unchanged pointwise values under the restriction constructor | $\delta_U(x)=\delta(j(x))$ | `DimensionFunction.comapOpenImmersion_apply` | ROUTE |
| identity restriction of the supplied dimension function | $\delta\circ\mathrm{id}=\delta$ as dimension-function objects | `DimensionFunction.comapOpenImmersion_id` | ROUTE |
| composition of actual restrictions | $(\delta\circ j)\circ k=\delta\circ(j\circ k)$ | `DimensionFunction.comapOpenImmersion_comp` | ROUTE |
| open and closed restriction constructors agree when both apply | prose only; the same restricted $\delta$ for an open-and-closed immersion | `DimensionFunction.comapOpenImmersion_eq_comapClosedImmersion` | ROUTE |
| actual reduced closure preserves the corresponding support degree | $\deg_\delta\overline{j(W)}_{\mathrm{red}}=\deg_{\delta_U}W$ | `supportDegree_openClosureSubscheme` | ROUTE |
| a nonempty restricted integral carrier retains its degree | $\deg_{\delta_U}(Z_U)=\deg_\delta Z$ when $Z_U\ne\varnothing$ | `supportDegree_openRestrictionSubscheme` | ROUTE |
| the already defined finite-cycle restriction preserves homogeneity | $j^*Z^\delta_{\mathrm{fin},m}(X;R)\subseteq Z^{\delta_U}_{\mathrm{fin},m}(U;R)$ | `openRestriction_mem_cyclesOfDegree` | ROUTE |
| restriction of that same geometric cycle map to the existing degree submodules | $j^*:Z^\delta_{\mathrm{fin},m}(X;R)\to Z^{\delta_U}_{\mathrm{fin},m}(U;R)$ | `gradedOpenRestriction` | ROUTE |
| the underlying finite cycle is unchanged by homogeneous packaging | prose only; the existing $j^*c$ | `gradedOpenRestriction_val` | ROUTE |
| identity on the same homogeneous representatives | $(\mathrm{id}_X)^*=\mathrm{id}$ | `gradedOpenRestriction_id` | ROUTE |
| contravariant composition of the same graded restriction | $(j\circ k)^*=k^*j^*$ | `gradedOpenRestriction_comp` | ROUTE |
| the existing actual carrier maps commute with their closed inclusions | $\iota_Z\circ j_Z=j\circ\iota_{Z_U}$ | `openRestrictionSubschemeMap_subschemeι` | ROUTE |
| the actual Cartesian square commutes on all finite cycles | $j^*(\iota_Z)_*=(\iota_{Z_U})_*j_Z^*:Z_{\mathrm{fin}}(Z;R)\to Z_{\mathrm{fin}}(U;R)$ | `openRestriction_closedImmersionPushforward_subscheme` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| the actual ambient principal divisor restricts to the actual nonempty carrier's principal divisor | $j^*((\iota_W)_*\operatorname{div}_W(f))=(\iota_{W_U})_*\operatorname{div}_{W_U}(j_W^*f)$ | `openRestriction_ambientPrincipalDivisor_of_nonempty` | ROUTE |
| an empty inverse-image carrier contributes zero | $j^*((\iota_W)_*\operatorname{div}_W(f))=0$ when $W_U=\varnothing$ | `openRestriction_ambientPrincipalDivisor_of_isEmpty` | ROUTE |
| derive source Noetherianity from the actual open immersion and target Noetherianity | prose only; $X$ Noetherian implies $U$ Noetherian | `openImmersion_isNoetherian` | ROUTE |
| restrict the existing degree-one-higher datum on a nonempty carrier, with no Noetherian premise | $(W,f)\mapsto(W_U,j_W^*f)$ with $\deg_{\delta_U}W_U=m+1$ | `PrincipalRelationData.openRestriction` | ROUTE |
| retain the literal ideal-comap integral carrier | prose only; the same $W_U$ | `PrincipalRelationData.openRestriction_carrier` | ROUTE |
| retain the actual forward contravariant function-field map | prose only; the literal $j_W^*f\in k(W_U)^\times$ | `PrincipalRelationData.openRestriction_function` | ROUTE |
| the existing graded map sends the nonempty generator to its actual restricted generator | prose only; the preceding nonempty ambient principal-divisor identity inside the degree-$m$ homogeneous module | `gradedOpenRestriction_principalRelation_of_nonempty` | ROUTE |
| the empty carrier gives the zero homogeneous cycle | prose only; the preceding empty ambient principal-divisor identity inside the degree-$m$ homogeneous module | `gradedOpenRestriction_principalRelation_of_isEmpty` | ROUTE |
| preservation of the span is a consequence of the proved generator identities | $j^*\mathcal R_m^\delta(X)\subseteq\mathcal R_m^{\delta_U}(U)$ | `principalRelations_le_comap_openRestriction` | ROUTE |
| the existing rational-equivalence predicate on integral cycles is preserved | $c\sim_{\mathrm{rat}}e\Rightarrow j^*c\sim_{\mathrm{rat}}j^*e$ for $c,e\in Z^\delta_{\mathrm{fin},m}(X;\mathbb Z)$ | `rationallyEquivalent_openRestriction` | ROUTE |

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

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| descend the actual graded integral cycle map using the proved relation-span inclusion | $j^*:\operatorname{CH}_m^\delta(X)\to\operatorname{CH}_m^{\delta_U}(U)$ | `chowOpenRestriction` | ROUTE |
| preserve the actual integral cycle representative | $j^*[z]=[j^*z]$ | `chowOpenRestriction_classMap` | ROUTE |
| the identity immersion induces the identity on the existing quotient | $\operatorname{id}^*=\operatorname{id}$ | `chowOpenRestriction_id` | ROUTE |
| preserve contravariant composition with the literal composed dimension function | $(j\circ i)^*=i^*\circ j^*$ | `chowOpenRestriction_comp` | ROUTE |
| coefficient extension commutes with the existing finite-cycle operation | $j^*(z_{\mathbf Q})=(j^*z)_{\mathbf Q}$ | `openRestriction_rationalize` | ROUTE |
| the same coefficient equality in the existing homogeneous submodules | prose only; the preceding identity in degree $m$ | `gradedOpenRestriction_rationalize` | ROUTE |
| preserve the rational span of the same actual principal generators | $j^*\mathcal R_m^\delta(X;\mathbf Q)\subseteq\mathcal R_m^{\delta_U}(U;\mathbf Q)$ | `rationalPrincipalRelations_le_comap_openRestriction` | ROUTE |
| descend the actual rational cycle restriction to the existing quotient | $j^*:\operatorname{CH}_m^\delta(X;\mathbf Q)\to\operatorname{CH}_m^{\delta_U}(U;\mathbf Q)$ | `rationalChowOpenRestriction` | ROUTE |
| preserve the actual rational cycle representative | $j^*[z]=[j^*z]$ for rational $z$ | `rationalChowOpenRestriction_classMap` | ROUTE |
| retain the identity on the rational quotient | $\operatorname{id}^*=\operatorname{id}$ | `rationalChowOpenRestriction_id` | ROUTE |
| retain contravariant composition on the rational quotient | $(j\circ i)^*=i^*\circ j^*$ | `rationalChowOpenRestriction_comp` | ROUTE |
| commute with the existing integral-to-rational Chow class map | $j^*(c_{\mathbf Q})=(j^*c)_{\mathbf Q}$ for integral Chow classes $c$ | `rationalChowOpenRestriction_chowRationalize` | ROUTE |
| identify the rational quotient map with scalar extension of the integral map on all tensors | prose only; the full square under the existing comparisons $q\otimes[z]\mapsto[qz_{\mathbf Q}]$ | `rationalChowOpenRestriction_chowRationalizationEquiv` | ROUTE |

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
localization exactness were later proved at SP110 by support comparison
and principal-relation lifting; they do not follow just
from these SP63 surjectivity assertions. Proper
pushforward's norm comparison, flat/Gysin operations, general Chow
convolution and prescribed target identification/realization/coverage
remain separate, as recorded in `GAP_MAP.md` and `TARGET_BRIDGE.md`.

### Surjectivity of the existing open restrictions (SP63 / A11av)

Let \(j:U\hookrightarrow X\) be an open immersion, let
\(\delta\) be a supplied dimension function on \(X\), and retain
\(\delta_U=\delta\circ j\). The degree \(m\) is any integer.
The maps below are the existing finite-cycle and Chow restriction maps.

| Object / mathematical role | LaTeX notation | Lean representation | Proof role |
| --- | --- | --- | --- |
| lift every actual finite cycle, over an arbitrary semiring | $j^*:Z_{\mathrm{fin}}(X;R)\twoheadrightarrow Z_{\mathrm{fin}}(U;R)$ | `openRestriction_surjective` | ROUTE |
| lift in the same supplied degree, without ambient finiteness premises | $j^*:Z_{\mathrm{fin},m}^{\delta}(X;R)\twoheadrightarrow Z_{\mathrm{fin},m}^{\delta_U}(U;R)$ | `gradedOpenRestriction_surjective` | ROUTE |
| lift every integral Chow class through an actual homogeneous cycle representative | $j^*:\operatorname{CH}_m^\delta(X)\twoheadrightarrow\operatorname{CH}_m^{\delta_U}(U)$ | `chowOpenRestriction_surjective` | ROUTE |
| lift every rational Chow class through the existing rational cycle quotient | $j^*:\operatorname{CH}_m^\delta(X;\mathbf Q)\twoheadrightarrow\operatorname{CH}_m^{\delta_U}(U;\mathbf Q)$ | `rationalChowOpenRestriction_surjective` | ROUTE |

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

### Supplementary object and adapter coverage (2026-10-13)

These source-linked rows close gaps in the earlier notation inventory.
A row groups related presentations of the displayed objects; conversion
maps, comparison witnesses and aliases retain those symbols rather than
creating new mathematical carriers. All entries here belong to auxiliary
routes or examples. Their existence as Lean definitions does not discharge
the hypotheses of their geometric applications.

#### Boundary: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Compatibility of sheet action and inertia average | $\rho(g),\ e_I=\lvert I\rvert^{-1}\sum_{g\in I}[g]$ | `SheetActionCompatibility`; `inertiaAveragingProjector` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/AveragingAction.lean) | ROUTE |
| Generic/compactified images of group-algebra projectors and their extensions | $\gamma_\eta(q),\ \bar\gamma(q),\ \operatorname{Ext}(\gamma_\eta(q))$ | `genericGroupAlgebraProjector`; `compactifiedGroupAlgebraProjector`; `groupAlgebraProjectorExtension`; `subgroupAveragingProjectorExtension` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/CompactifiedGraphProjector.lean) | ROUTE |
| Noether different, contact quotient and ramification locus | $\mathfrak D_\mu=\mu(\operatorname{Ann}\ker\mu),\ C/(J+\operatorname{Ann}J)\simeq A/\mathfrak D_\mu,\ \operatorname{Ram}=\{P:\neg\operatorname{Unram}_P\}$ | `noetherDifferentIdeal`; `contactQuotientMap`; `contactRingEquivNoetherDifferentQuotient`; `collisionNoetherDifferentIdeal`; `collisionContactRingEquivDifferentQuotient`; `collisionRamificationLocus` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Different.lean) | ROUTE |
| Height-one comparison of inertia and sheet indices | $I_E,\ e_E$; named comparison hypothesis | `HeightOneInertiaRealization` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/ExtensionCriterion.lean) | ROUTE |
| Single-boundary extension and existing-family adapters; prescribed action remains a premise | $\operatorname{Ext}_{I,r}(e_H),\ \rho(\Pi)=P$; singleton-family adapters have no new symbol | `projectorLiftOfRealizes`; `BoundarySubgroupProjectorExtension`; `toCompactifiedPUnit`; `toBoundary`; `GaloisCollisionDecomposition.subgroupProjector`; `complement` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/GaloisProjectorExtension.lean) | ROUTE |
| Different detects ramification at the actual height-one prime | $\mathfrak D_{\mathrm{coll}}\subseteq P\ \Longleftrightarrow\ \neg\operatorname{Unram}_P(R\to S),\ \mathfrak D_{\mathrm{coll}}=\mathfrak D_{\mathrm{Ded}}$; distinct comparison predicates | `CollisionDifferentDetectsRamificationAt`; `CollisionDifferentComparison` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/HeightOneDifferent.lean) | ROUTE |
| Original Galois group, conjugate normalization leg and visible open | $G,\ c_g:Y_N\to Y_L,\ U_g=c_g^{-1}(U)$ | `NormalizedCover.GaloisGroup`; `conjugateToIntermediate`; `pulledBackConjugateVisibleOpen` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/ConjugateBoundary.lean) | ROUTE |
| Conjugate ring map underlying the existing scheme leg | $c_g^\#: \widetilde B_L\to\widetilde B_N$ | `conjugateNormalizationRingMap` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/ConjugateNormalization.lean) | ROUTE |
| Base-compatible normal-closure action on the normalization | $G\to\operatorname{Aut}_B(\widetilde B_N),\ G\to\operatorname{Aut}_{\operatorname{Spec}B}(Y_N)$ | `normalClosureEquivOverBase`; `normalClosureNormalizationRingEquiv`; `normalClosureDeckTransformation`; `normalClosureFiniteDeckAction`; `normalClosureNormalizationSchemeIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/DeckAction.lean) | ROUTE |
| Actual local map between nested invariant rings | $(S^H)_{Q\cap S^H}\to(S^I)_{Q\cap S^I}$ | `fixedPointsLocalRingHom` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/FixedRingUnramified.lean) | ROUTE |
| Normalization legs, centered valuations, sheet orbits, visible centers and hidden-inertia predicates | $Y_N\to Y_L\to\operatorname{Spec}B,\ \iota:L\to N,\ V_E,\ D_E\backslash G/H,\ [H],\ e_E(s),\ Q_{E,s},\ \operatorname{NoHiddenInertia}$ | `intermediateNormalizationToBase`; `normalClosureEmbeddingOverBase`; `normalClosureNormalizationToBase`; `normalClosureToIntermediateNormalization`; `ValuationCenteredAt`; `sheetClasses`; `inertiaIndex`; `baseClass`; `ConjugateCenterVisible`; `RamifiedConjugateCentersInBoundaryAt`; `RamifiedConjugateCentersInBoundary`; `HasHiddenInertiaOrbit`; `NoHiddenInertia`; `centerPrime`; `geometricRamificationIndex` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/InertiaDiagram.lean) | ROUTE |
| Action on normalization and fixed-field/fixed-ring comparison | $G\curvearrowright\widetilde B_N,\ \operatorname{IntCl}_B(N^H)\simeq(\widetilde B_N)^H$ | `normalClosureNormalizationRingActionHom`; `FixedSubgroupNormalizationRing`; `fixedFieldNormalizationToFixedRing`; `fixedFieldNormalizationEquivFixedRing` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/InvariantIntermediate.lean) | ROUTE |
| Valuation identification with the selected prime localization and stabilizer transport | $V_E\simeq(\widetilde B_N)_Q$; comparison witness, not a second valuation ring | `ValuationLocalizationAt`; `HasValuationLocalizationAt`; `localRingEquivOfPrimeStabilizer` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/LocalizationBridge.lean) | ROUTE |
| Normalization map induced contravariantly by a field embedding | $E\hookrightarrow E^\prime,\ \operatorname{Spec}\operatorname{IntCl}_B(E^\prime)\to\operatorname{Spec}\operatorname{IntCl}_B(E)$ | `normalizationDomination`; `normalizedCoordinateRing`; `normalizedAffineModel` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/Model.lean) | ROUTE |
| Marked intermediate field and trivial-extension comparisons | $\iota(L)\subset N,\ L=K,\ N=K$; extension-triviality predicates and the corresponding field equivalence | `intermediateField`; `IntermediateExtensionTrivial`; `ExtensionTrivial`; `extensionEquivBase` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/NormalClosure.lean) | ROUTE |
| Quotient of the conjugate tensor algebra by the evaluation kernel | $(\bigotimes_{\sigma:L\hookrightarrow N}L)/\ker\varepsilon\simeq N$ | `tensorEvaluationQuotientEquiv`; `tensorEvaluation` | Constructed evaluation and quotient comparison for the existing normal closure; used in the normalization refinement, not a prescribed Chow cycle; [source](../../HodgeConjecture/Boundary/Normalization/NormalClosureTensor.lean) | ROUTE |
| Generic base change of normalization and its conjugate tensor | $K\otimes_B\operatorname{IntCl}_B(L)\simeq L,\ K\otimes_B(\bigotimes_B\operatorname{IntCl}_B(L))\simeq\bigotimes_K L$ | `normalizedCoordinateRingBaseChangeEquiv`; `normalizationTensorBaseChangeEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/NormalizationBaseChange.lean) | ROUTE |
| Actual normalization prime inertia and comparison with valuation inertia | $I_Q^{\mathrm{pr}},\ \operatorname{Unram}_{Q\cap S^{I_Q}}(B\to S^{I_Q}),\ I_Q^{\mathrm{pr}}\leftrightarrow I_E,\ (\widetilde B_N)^G$ | `normalizationPrimeInertiaGroup`; `NormalizationPrimeInertiaFixedRingUnramifiedAt`; `PrimeInertiaComparisonAt`; `FullInvariantNormalizationRing` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/PrimeInertia.lean) | ROUTE |
| Marked sheet algebra, embeddings, delta tensors and actual separable splitting | $A_H,\ G/H\simeq\operatorname{Hom}_K(L,N),\ L\otimes_KL\to N^{G/H},\ e_s\in N\otimes_KL,\ N\otimes_KL\simeq N^{G/H}$ | `NormalClosureData.rationalMarkedSheetAlgebra`; `NormalClosureData.sheetEmbedding`; `NormalClosureData.sheetEmbeddingEquiv`; `NormalClosureData.collisionToGenericSheets`; `NormalClosureData.sheetDeltaTensor`; `NormalClosureData.normalClosureTensorGenericSheetsEquiv`; `formallyUnramifiedMarkedAugmentedAlgebra` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/SelectorComparison.lean) | ROUTE |
| Discrete valuation tower, decomposition group and inertia subgroup | $V_K\subset V_N,\ D_V\leq G,\ I_V\leq D_V$ | `decompositionGroupAt`; `inertiaWithinDecomposition`; `DiscreteValuationTower` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Normalization/ValuationInertia.lean) | ROUTE |
| Existing zero-defect closures regarded as extensions | $\operatorname{Cl}_r^0(e)\to\operatorname{Ext}_r(e)$; adapter | `toAlgebraProjectorExtension`; `convolutionDefect` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/ProjectorClosureDefect.lean) | ROUTE |
| Selected-set height-one comparison and invariance at every boundary | $A\subset G/H,\ I_E A=A$; selected-sheet and singleton adapters | `SelectedSheetHeightOneInertiaRealization`; `ofBaseSheet`; `InvariantAtEveryBoundary` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/SheetProjectorExtension.lean) | ROUTE |
| Double-coset sheets and their representative-independent inertia indices | $D\backslash G/H,\ e_I(gH)=[I:I\cap gHg^{-1}]$ | `DecompositionSheetClasses`; `inertiaIndexAtSheet`; `inertiaIndexAtRepresentative`; `inertiaIndexAtDoubleCoset` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/DecompositionSheets.lean) | ROUTE |
| Inertia invisibility and detection on visible sheets | $I\text{ fixes }s,\ I\text{ fixes }V\subseteq G/H$; detection predicate | `InertiaInvisibleAt`; `InertiaInvisibleOn`; `VisibleSheetsDetectInertia` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/GaloisSheets.lean) | ROUTE |
| Inertia-invariant pointwise selector | $gq=q\ (g\in I)$ | `InertiaInvariantSelector` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/GenericProjector.lean) | ROUTE |
| Inertia orbit index at the marked sheet | $[I:I\cap H]$ | `inertiaQuotientIndex` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/InertiaQuotient.lean) | ROUTE |
| An inertia orbit crosses the selected-set boundary | $\exists g\in I,\ s\in A:\ gs\notin A$ | `InertiaCrosses`; `baseSheet` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/InertiaSaturation.lean) | ROUTE |
| Marked evaluation/augmentation and selector-coordinate adapters | $\operatorname{ev}_H:A_H\to\mathbf Q,\ A_H\simeq\mathbf Q\oplus E_H,\ P_{q_H-1}$ | `baseEvaluation`; `baseAugmentation`; `markedAugmentedAlgebra`; `selectorDecomposition`; `graphOperator`; `decomposition`; `multiplication` | Existing definitions/adapters; [source](../../HodgeConjecture/Boundary/Sheets/MarkedBlockProjector.lean) | ROUTE |
| Integral conjugate-tensor evaluation into the same normalization | $\varepsilon_B:\bigotimes_{\sigma:L\hookrightarrow N}\operatorname{IntCl}_B(L)\to\operatorname{IntCl}_B(N)$ | `normalizationTensorEvaluation` | Used by the selected-component construction in `FiniteEtaleNormalClosure.lean`; its output is the normal-closure refinement, not SP109's cycle family; [source](../../HodgeConjecture/Boundary/Normalization/NormalizationTensor.lean) | ROUTE |

#### Collision: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Actual affine collision map, self-fiber product, diagonal and decomposition | $\operatorname{Spec}A\to\operatorname{Spec}B,\ \operatorname{Spec}(A\otimes_BA),\ \Delta,\ \operatorname{Spec}A\sqcup\operatorname{Spec}(C/\operatorname{Ann}J)$ | `affineCollisionMap`; `affineSelfCollisionScheme`; `affineSelfCollisionSpecIso`; `affineCollisionDiagonal`; `collisionDiagonalQuotientEquiv`; `affineSelfCollisionDecomposition`; `affineSelfCollisionDecompositionOfFormallyUnramified` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/AffineGeometry.lean) | ROUTE |
| Tensor collision algebra, multiplication kernel and annihilator | $C=A\otimes_BA,\ \mu,\ J=\ker\mu,\ \operatorname{Ann}(J)$ | `collisionMultiplication`; `collisionOffDiagonalIdeal` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/Algebra.lean) | ROUTE |
| Polynomial collision equations, quotient and diagonal obstruction | $F_j(x)-F_j(y),\ I_F,\ C_F=R[x,y]/I_F,\ J_F=\ker\bar\mu$ | `collisionGenerator`; `collisionIdeal`; `CollisionRing`; `obstructionIdeal` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/Basic.lean) | ROUTE |
| Scheme decomposition and its diagonal/off-diagonal structure maps | $X\times_YX\simeq X\sqcup C_{\mathrm{off}},\ X\to X\times_YX,\ C_{\mathrm{off}}\to X\times_YX\to X\times_SX$ | `diagonalInclusion`; `offDiagonalInclusion`; `offDiagonalToProduct`; `offDiagonalToAmbientProduct`; `affineCollisionSchemeDecomposition`; `CollisionSelectorPair.affineSchemeDecomposition`; `affineCollisionSchemeDecompositionOfFormallyUnramified` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/ClopenDecomposition.lean) | ROUTE |
| Polynomial collision diagonal evaluation, with ring-map adapter | $\bar\mu:C_F\to R[x]$ | `collisionDiagonal`; `barMu` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/CollisionDiagonal.lean) | ROUTE |
| Diagonal and off-diagonal selectors and their paired datum | $e_\Delta\leftrightarrow(1,0),\ e_{\mathrm{off}}\leftrightarrow(0,1)$ in $C/J\times C/\operatorname{Ann}J$ | `IsDiagonalSelector`; `IsOffDiagonalSelector` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/ComponentSelectors.lean) | ROUTE |
| Overlap ideal, contact ideal and contact ring | $J\cap\operatorname{Ann}J,\ J+\operatorname{Ann}J,\ C/(J+\operatorname{Ann}J)$; not $\Pi^2-\Pi$ | `overlapDefectIdeal`; `contactIdeal`; `ContactRing`; `collisionOverlapDefectIdeal`; `CollisionContactRing` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/DecompositionDefect.lean) | ROUTE |
| Paired polynomial variables/rings, renamings, diagonal ideal and evaluation | $\iota\sqcup\iota,\ R[x],\ R[x,y],\ x_i\mapsto x_i,y_i,\ x_i-y_i,\ I_\Delta,\ R[x,y]/I_\Delta\simeq R[x]$ | `PairVars`; `SourceRing`; `PairRing`; `leftRename`; `rightRename`; `diagonalGenerator`; `diagonalIdeal`; `diagonalEval`; `diagonalQuotientEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/Diagonal.lean) | ROUTE |
| Complement of the open-and-closed diagonal and its coproduct realization | $(X\times_YX)\setminus\Delta_X,\ X\times_YX\simeq X\sqcup C_{\mathrm{off}}$ for separated étale $f$ | `collisionOffDiagonalOpen`; `collisionDecompositionCofanIsColimit`; `separatedEtaleCollisionSchemeDecomposition`; `finiteEtaleCollisionSchemeDecomposition` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/EtaleDecomposition.lean) | ROUTE |
| Self-fiber-product algebra and diagonal multiplication | $A\otimes_BA,\ \mu(a\otimes a^\prime)=aa^\prime$ | `SelfFiberProductAlgebra`; `diagonalMultiplication` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/FiberProduct.lean) | ROUTE |
| Intrinsic and ambient collision/diagonal/off-diagonal schemes, ideals and projection maps | $X\times_YX,\ p_1,p_2,\ \Delta_X,\ X\times_SX,\ \mathcal I_{\mathrm{coll}},\mathcal I_\Delta,\mathcal I_{\mathrm{off}},\ V(\mathcal I_{\mathrm{off}})$; each ideal retains its ambient scheme | `collisionSpace`; `collisionFst`; `collisionSnd`; `collisionDiagonal`; `collisionToProduct`; `absoluteDiagonal`; `collisionToAmbientProduct`; `collisionObstructionIdealSheaf`; `ambientCollisionIdealSheaf`; `ambientDiagonalIdealSheaf`; `intrinsicOffDiagonalIdealSheaf`; `intrinsicOffDiagonalScheme`; `ambientOffDiagonalIdealSheaf`; `ambientOffDiagonalScheme`; `ambientCollisionIdealSheafOver`; `ambientDiagonalIdealSheafOver`; `ambientOffDiagonalIdealSheafOver`; `ambientOffDiagonalSchemeOver` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/GlobalGeometry.lean) | ROUTE |
| Relative diagonal and off-diagonal ideal sheaves, including affine presentations | $\mathcal I_\Delta,\ \operatorname{Ann}(\mathcal I_\Delta)$ on $X\times_YX$ | `relativeDiagonalIdealSheaf`; `relativeOffDiagonalIdealSheaf`; `affineRelativeDiagonalIdealSheaf`; `affineRelativeOffDiagonalIdealSheaf` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/IdealSheaf.lean) | ROUTE |
| Colon ideal, saturation, clopen selector and polynomial residual factor | $(I:J),\ (I:J^\infty),\ \bar q,\ A/I\simeq A/J\times A/(I:J),\ \operatorname{OffDiag}(F)$; hypotheses remain explicit | `offDiagonalColonIdeal`; `idealSaturation`; `IsClopenModulo`; `quotientEquivDiagonalProdOffDiagonal`; `collisionOffDiagonalIdeal`; `OffDiagonalRing`; `collisionIdealSaturation`; `IsCollisionOffDiagonalSelector`; `collisionRingEquivDiagonalProdOffDiagonal` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/OffDiagonal.lean) | ROUTE |
| Coordinate map and polynomial/tensor collision identification | $R[t_j]\to R[x_i],\ t_j\mapsto F_j,\ C_F\simeq R[x]\otimes_{R[t]}R[x]$ | `coordinateAlgHom`; `collisionTensorEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/PolynomialFiberProduct.lean) | ROUTE |
| Algebra, spectrum and scheme forms of the same complementary-ideal decomposition | $C\simeq C/J\times C/\operatorname{Ann}J,\ \operatorname{Spec}C\simeq\operatorname{Spec}(C/J)\sqcup\operatorname{Spec}(C/\operatorname{Ann}J)$ | `idealProductDecomposition`; `idealSpectrumDecomposition`; `idealAffineSchemeDecomposition`; `collisionProductDecomposition`; `collisionSpectrumDecomposition`; `collisionAffineSchemeDecomposition` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/SchemeDecomposition.lean) | ROUTE |
| Two collision legs, compatible cocones and induced universal map | $R[x]\rightrightarrows C_F,\ (u,v),\ C_F\to T,\ \operatorname{Hom}(C_F,T)\simeq\{(u,v):uF=vF\}$ | `collisionLeft`; `collisionRight`; `CollisionCocone`; `collisionPairMap`; `collisionLift`; `collisionRestrict`; `collisionUniversalEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/UniversalProperty.lean) | ROUTE |
| Ideal-sheaf annihilator, in the existing sheaf-colon construction | $\operatorname{Ann}(\mathcal J)=(0:\mathcal J)$ | `annihilator` | Existing definitions/adapters; [source](../../HodgeConjecture/Collision/SheafColon.lean) | ROUTE |

#### CommutativeAlgebra: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Evaluation of the existing indexed tensor product | $\bigotimes_R A_i\to B$; comparison map, no new algebra | `piTensorProductEvaluation` | Existing definitions/adapters; [source](../../HodgeConjecture/CommutativeAlgebra/FiniteTensorProduct.lean) | ROUTE |
| Indexed tensor congruence and scalar extension | $S\otimes_R(\bigotimes_R A_i)\simeq\bigotimes_S(S\otimes_R A_i)$; congruence adapter | `piTensorProductCongr`; `piTensorProductBaseChangeEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/CommutativeAlgebra/PiTensorBaseChange.lean) | ROUTE |

#### Correspondence: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Additive span-class map, multiplicative realization and free-algebra lift | $\chi:[P]\mapsto\chi(P),\ \mathbf Q[\operatorname{Span}(X)]\to\Gamma$ | `AdditiveClassMap`; `AlgebraModel`; `classValue`; `classMonoidHom`; `freeAlgebraMap` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Algebra.lean) | ROUTE |
| Isomorphism relation, span class, composition and identity | $P\cong Q,\ [P],\ [Q]\circ[P],\ [\Delta_X]$ | `Isomorphic`; `classOf`; `classComp`; `classOne`; `Class` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Classes.lean) | ROUTE |
| Collision and off-diagonal spans and their coproduct decomposition | $[X\times_YX]=[\Delta_X]+[C_{\mathrm{off}}]$ at the span level | `collisionSchemeCorrespondence`; `offDiagonalSchemeCorrespondence`; `correspondenceDecompositionIsom` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Collision.lean) | ROUTE |
| Étale and finite étale conditions on both correspondence legs | $X\xleftarrow{\ell}Z\xrightarrow{r}Y,\ \ell,r\text{ (finite) étale}$ | `HasEtaleLegs`; `HasFiniteEtaleLegs` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Etale.lean) | ROUTE |
| Finite étale span classes, their submonoid and free-algebra inclusions | $\operatorname{Span}_{\mathrm{f\acute et}}(X),\ [P],\ \mathbf Q[\operatorname{Span}_{\mathrm{f\acute et}}(X)]\to\mathbf Q[\operatorname{Span}(X)]$ | `classHasFiniteEtaleLegs`; `finiteEtaleClassSubmonoid`; `FiniteEtaleClass`; `finiteEtaleClassOf`; `finiteEtaleOfScheme`; `finiteEtaleFreeAlgebraMap` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/EtaleClasses.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $W\simeq f(W)$ | `imageIntegralSubschemeIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitCycleGeometry.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $G\curvearrowright Z_{G/H},\ G\times Z_G\simeq Z_G\times Z_G$ in the regular-torsor example | `deckAction`; `sheetAction`; `indexedSchemeIso`; `regularPairEquiv`; `regularTorsorIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitGaloisSheets.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $I\simeq\operatorname{Spec}(k^I)$ | `labelEquivSpectrum` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitPointMaps.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $\mathcal O_{Z_I,s_i}\simeq k$ | `baseStalkIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitPointMultiplicity.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $[s_i]\circ[s_i]\simeq[s_i]$ at the point-span level; point coordinates in the Chow specialization | `pointSpan_comp_self_iso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitPoints.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $Z_{I\times J}\simeq Z_I\times_kZ_J,\ (s_i,s_j),\ Z_{f^{-1}(i)}\simeq f^{-1}(s_i)$ | `productComparison`; `pointPairInclusion`; `pointFiberComparison` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitProductGeometry.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $Z_{S\sqcup T}\simeq Z_S\sqcup Z_T$ and the coproduct universal map | `sumDesc`; `sumSchemeIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitSpanCoproduct.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $P\simeq\coprod_{s\in S}P_s$ | `pointDecompositionIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitSpanDecomposition.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $Z_S\to Z_I, Z_J$; relabeling, identity, singleton and fiber-comparison adapters | `precompose`; `isoOfEquiv`; `spanIsoOfEquiv`; `span_identity_iso`; `singletonIso`; `span_point_iso`; `fiberComparison` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Examples/SplitSpanGeometry.lean) | ROUTE |
| Indexed disjoint union of spans, inclusions and additivity predicate | $\coprod_i P_i,\ P_i\hookrightarrow\coprod_iP_i,\ \chi(\coprod_iP_i)=\sum_i\chi(P_i)$ | `indexedCoprod`; `indexedCoprodIn`; `PreservesFiniteIndexedCoproducts` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/FiniteCoproduct.lean) | ROUTE |
| Finite étale span realization model and class evaluation | $\chi_{\mathrm{f\acute et}}(P)\in\Gamma$; supplied realization laws | `FiniteEtaleAlgebraModel`; `classOf` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/FiniteEtaleModel.lean) | ROUTE |
| Finite deck action, induced graph-algebra maps, averages and complementary lifts | $G\to\operatorname{Aut}_S(X),\ \mathbf Q[G]\to\Gamma,\ \sum_g[g],\ e_G,\ 1-e_G$ | `toClassMonoidHom`; `toDeckGroupAlgebra`; `toFiniteEtaleAlgebra`; `finiteGroupSum`; `finiteGroupAverage`; `averagingProjector`; `complementaryAveragingProjector`; `averagingProjectorLift`; `complementaryAveragingProjectorLift`; `restrict` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/FiniteGroupProjector.lean) | ROUTE |
| Galois collision decomposition, graph family and normalized collision class | $X\times_YX\simeq\coprod_{g\in G}\Gamma_g,\ \lvert G\rvert^{-1}\chi(X\times_YX)$ | `GaloisCollisionDecomposition`; `actionOverBase`; `graphCorrespondence`; `graphFamilyCorrespondence`; `collisionCorrespondenceIso`; `finiteEtaleAlgebraRealization`; `normalizedCollisionClass`; `normalizedCollisionProjectorLift` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/GaloisCollision.lean) | ROUTE |
| Underlying deck map, graph classes and graph-algebra map | $\sigma:X\to X,\ [\Gamma_\sigma],\ \mathbf Q[\operatorname{Aut}_S(X)]\to\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}$ | `DeckTransformation.toSchemeHom`; `graphOneIsom`; `graphFiniteEtaleClass`; `graphClassMonoidHom`; `DeckGroupAlgebra`; `graphAlgebraMap`; `graph` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Graph.lean) | ROUTE |
| Images of idempotents and complete orthogonal decompositions | $\gamma(q),\ q_iq_j=0\ (i\ne j),\ \sum_iq_i=1,\ \rho(\gamma(q_i))=P_i$; prescribed-action equations are additional inputs | `groupAlgebraCorrespondence`; `groupAlgebraProjectorLift`; `prescribedGroupAlgebraProjectorLift`; `GroupAlgebraDiagonalDecomposition`; `toDiagonalDecompositionLift`; `toPrescribedDiagonalDecompositionLift`; `correspondence` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/GroupAlgebraProjector.lean) | ROUTE |
| Idempotent corner, Hecke algebra/elements, double cosets and correspondence corner | $eAe,\ \mathbf Q[H]\to\mathbf Q[G],\ e_H\mathbf Q[G]e_H,\ e_H[g]e_H,\ H\backslash G/H,\ \gamma(e_H)\Gamma\gamma(e_H)$ | `cornerSubmodule`; `cornerRingHom`; `subgroupAlgebraMap`; `heckeElement`; `doubleCosetOperator`; `CorrespondenceHeckeAlgebra`; `heckeToCorrespondenceCorner`; `heckeCorrespondence`; `heckeProjectorLift`; `prescribedHeckeProjectorLift` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/HeckeProjector.lean) | ROUTE |
| Span generators and disjoint-union additivity defect in the free algebra | $[P],\ [P\sqcup Q]-[P]-[Q]$ | `ofClass`; `ofScheme`; `coprodAdditivityDefect` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Linearized.lean) | ROUTE |
| Universal idempotent maps, prescribed squares and complementary diagonal decompositions | $\varphi_\Pi,\ \varphi_P,\ \rho\varphi_\Pi=\varphi_P,\ (\Pi,1-\Pi),\ (P,1-P)$ | `algebraIdempotentMap`; `cohomologicalIdempotentMap`; `ofIdempotentMapSquare`; `DiagonalDecompositionLift`; `complementaryCohomologicalProjectors`; `complementaryAlgebraicProjectors`; `toBoolDiagonalDecomposition`; `complement` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/ProjectorLift.lean) | ROUTE |
| Span-to-product map, transpose, composition adapters and proper-support predicate | $Z\to X\times_SY,\ {}^tZ,\ (R\circ Q)\circ P\simeq R\circ(Q\circ P),\ Z\hookrightarrow Z\sqcup Z^\prime$; properness is a property of the pair map | `toAmbientProduct`; `transpose`; `identityCompIsom`; `compIdentityIsom`; `assocIsom`; `inl`; `IsProperSupport`; `identity`; `refl`; `symm`; `trans`; `coprod`; `inr` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/Scheme.lean) | ROUTE |
| Transpose on spans/classes and its opposite-algebra involutions | $P\mapsto{}^tP,\ {}^t(Q\circ P)={}^tP\circ{}^tQ,\ \Gamma\to\Gamma^{\mathrm{op}},\ {}^t\Gamma_\sigma=\Gamma_{\sigma^{-1}}$ | `Isom.transpose`; `transposeCompIsom`; `transposeIdentityIsom`; `classTranspose`; `classTransposeEquiv`; `classTransposeMulEquiv`; `finiteEtaleClassTranspose`; `finiteEtaleClassTransposeEquiv`; `finiteEtaleClassTransposeMulEquiv`; `freeTransposeLinearEquiv`; `freeTransposeRingInvo`; `finiteEtaleFreeTransposeLinearEquiv`; `finiteEtaleFreeTransposeRingInvo`; `graphTransposeIsom` | Existing definitions/adapters; [source](../../HodgeConjecture/Correspondence/TransposeAlgebra.lean) | ROUTE |

#### Inputs: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Chosen finite étale extension and original-open comparison | $\bar Y\to X,\ Y\simeq U\times_X\bar Y$; choice from the existing existence premise | `chosenExtension`; `comparisonIso` | Existing definitions/adapters; [source](../../HodgeConjecture/Inputs/FiniteEtaleExtension.lean) | ROUTE |

#### LinearAlgebra: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Linear map defining the graph block | $t\mapsto t\alpha$ | `lineMap` | Existing definitions/adapters; [source](../../HodgeConjecture/LinearAlgebra/BlockGraphProjector.lean) | ROUTE |
| Augmentation ideal, underlying linear kernel, selector coordinates and graph block | $E=\ker\epsilon,\ A\simeq R\oplus E,\ P_{q-1}$; ideal/linear-kernel adapters retain $E$ | `augmentationIdeal`; `LinearResidual`; `residualLinearEquiv`; `selectorDecomposition`; `graphOperator`; `decomposition`; `multiplication` | Existing definitions/adapters; [source](../../HodgeConjecture/LinearAlgebra/MarkedAugmentedAlgebra.lean) | ROUTE |
| Residual-corner identifications with the original ideal and idempotent corner | $E^{\mathrm{corner}}\simeq E\simeq(1-q)A(1-q)$; underlying-type/ring adapters | `residualCornerEquivIdealType`; `residualCornerEquivIdeal`; `residualCornerEquivIdempotentCorner`; `complement` | Existing definitions/adapters; [source](../../HodgeConjecture/LinearAlgebra/MarkedAugmentedAlgebraDecomposition.lean) | ROUTE |
| Complement of the universal marked idempotent | $1-u=(0,1)\in R\times R$ | `complement` | Existing definitions/adapters; [source](../../HodgeConjecture/LinearAlgebra/UniversalIdempotentAlgebra.lean) | ROUTE |

#### Realization: retained auxiliary objects

| Object / mathematical role | LaTeX notation | Lean representation | Status / source | Proof role |
| --- | --- | --- | --- | --- |
| Existing split-example objects and geometric comparison adapters | $Z_{I\times J}(\mathbf C)\simeq Z_I(\mathbf C)\times Z_J(\mathbf C)$ | `productEquiv`; `labelEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/Examples/SplitComplexPoints.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $\rho_I:CH_0(Z_I\times Z_I)_{\mathbf Q}\to\operatorname{End}H^0(Z_I)$ | `actionLinear`; `linearRepresentation` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/Examples/SplitCorrespondenceAction.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $\theta:E_H\simeq H^0(Z_I,\mathbf Q)$ in the split example | `residualRealizationEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/Examples/SplitGaloisMarkedComparison.lean) | ROUTE |
| Finite fiber-sum transfer | $f_*a(y)=\sum_{f(x)=y}a(x)$ | `fiberSum` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/FiniteTransfer.lean) | ROUTE |
| Singular-simplex presentation, point zero-simplex and discrete degree-zero cohomology | $S_n(X),\ [x]\in S_0(X),\ \mathbf Q^X\to H^0(X,\mathbf Q)$; last map uses the stated discreteness hypotheses | `simplexEquivSingularSet`; `pointSimplex`; `ofFunctions`; `face`; `cocycles` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/SingularDegreeZero.lean) | ROUTE |
| Actual zero-simplex lifts identified with the point fiber | $\operatorname{Lift}_f(\sigma)\simeq f^{-1}(\sigma(*))$ | `zeroSimplexLiftEquiv` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Betti/ZeroSimplexTransfer.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $\Gamma_I^{CH}\simeq M_I(\mathbf Q)$ | `endMatrixCoordinates` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitChowAlgebra.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $[(s_i,s_j)]$ | `pointCorrespondence`; `diagonal` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitChowComposition.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $a\mapsto\sum_i a_i[s_i],\ \Delta_*:CH_0(Z_I)\to CH_0(Z_I\times Z_I)$ | `cyclesOfFunction`; `diagonalLinear` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitChowDiagonal.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $[s_i]\circ[s_i]\simeq[s_i]$ at the point-span level; point coordinates in the Chow specialization | `pointCoordinates` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitPoints.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $[P_{ij}],\ [P]-\sum_s[P_s],\ \mathcal C_{\mathrm{sp}}^{\mathrm{free}}/J_{\mathrm{sp}}$ | `pointSpanClass`; `decompositionGenerators`; `additivePresentation` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitSpanQuotient.lean) | ROUTE |
| Existing split-example objects and geometric comparison adapters | $[P],\ \chi(P),\ P\mapsto M_P$; split-presentation, identity and composition adapters | `spanClass`; `spanPresentation`; `Presentation.matrix`; `identityPresentation`; `Presentation.comp`; `ofSpan`; `ofSchemeSpan`; `classMatrix` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/SplitSpanRealization.lean) | ROUTE |
| Fixed-deck class-indexed graph coverage and stronger factorization premise | $\operatorname{Cov}_{\mathrm{deck}}(X,p,\alpha),\ \operatorname{Factor}_{\mathrm{deck}}$; no automatic coverage instance | `ClassIndexedFiniteCoverGraphCoverage`; `GraphProjectorLiftFactorizationThroughFixedDeckData` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/GaloisHodgeTarget.lean) | ROUTE |
| Class-dependent marked witness and comparison/representation adapters | $W_\alpha,\ \theta,\ \Theta P_{a_H}=\rho(\Pi)\Theta$; existing witness fields, not a constructed cover | `toMarkedSelectorActionComparison`; `toIdempotentRepresentationMorphism`; `ClassDependentMarkedGaloisSelectorWitness` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/GaloisMarkedRealization.lean) | ROUTE |
| Complement of the same prescribed projector and its two-summand decomposition | $1-\Pi,\ (\Pi,1-\Pi)$; adapters | `complementAlgebraicProjectorLift`; `toBoolDiagonalDecomposition` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/GaloisProjector.lean) | ROUTE |
| One-idempotent representation and its intertwiner | $\varphi_e:\mathbf Q^2\to\operatorname{End}(V),\ \Theta e_V=e_W\Theta$ | `endomorphismRepresentation`; `ofSelectorIntertwines` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/IdempotentRepresentation.lean) | ROUTE |
| Selector representation, stronger presented comparison and identity-presentation adapters | $\varphi_q,\ \mathscr R_\Pi,\ A\to B\to\Gamma$; full source-algebra presentation is additional data | `selectorRepresentation`; `toIdempotentRepresentationMorphism`; `genericProjector`; `PresentedMarkedSelectorActionComparison`; `toPresentedIdentity`; `identity` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean) | ROUTE |
| Two-sided relation presentation and its generic/compactified quotient models | $\Gamma=Z/I,\ \Gamma_\eta=Z_\eta/I_\eta,\ \bar\Gamma=\bar Z/\bar I,\ \gamma_\eta,\ \rho$; not automatically the geometric Chow quotient | `CorrespondenceAlgebraPresentation`; `QuotientAlgebra`; `PresentedRationalChowCorrespondenceModel`; `GenericAlgebra`; `CompactifiedAlgebra`; `genericCycleClass`; `cohomologicalAction`; `toRationalChowCorrespondenceModel`; `lift` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Presentation.lean) | ROUTE |
| Graph line map, lower-left detection, Hodge compatibility and coverage schemas | $t\mapsto t\alpha,\ d_{\mathrm{ll}}(P),\ 2P_\alpha-1,\ P_\alpha\text{ Hodge},\ \forall\alpha\ \exists\Pi:\rho(\Pi)=P_\alpha$ | `lineMap`; `lowerLeftClass`; `lowerLeftClassLinear`; `ClassGraphProjectorHodgeCompatibility`; `EveryHodgeClassHasGraphProjectorLift`; `EveryClassGraphHodgeMorphismHasAlgebraicLift`; `reflection` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/TateGraphProjector.lean) | ROUTE |
| Normalized pull-push projector and existing cohomological-projector adapter | $P_f=d^{-1}f^*f_*$ | `normalizedProjector`; `toRationalCohomologicalProjector` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/TransferProjector.lean) | ROUTE |
| Existing two-point free split-span source | $\mathcal C_{\mathrm{sp}}^{\mathrm{free}}(Z_{\{0,1\}})$ | `Source` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Examples/GeometricSplitPoints.lean) | ROUTE |
| Complement of a cohomological projector | $1-P$ | `complement` | Existing definitions/adapters; [source](../../HodgeConjecture/Realization/Chow/Model.lean) | ROUTE |

Coverage audit (2026-10-13): all 909 entries found by the comment-stripped,
public line-start declaration scan have an exact identifier occurrence in
inline Lean code in this registry. The scan covers
`def`/`abbrev`/`structure`/`class`, including source-linked presentation rows.
This is a declaration-name coverage check, not an assertion that every
theorem needs its own symbol or that a supplied model is geometrically
instantiated. Private helpers and Mathlib internals are not new registry
objects. The detailed canonical tables remain the notation authority.

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
