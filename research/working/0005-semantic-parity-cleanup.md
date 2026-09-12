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

### Split-point checkpoint (SP17--SP18)

| ID | Object or overlap | Disposition | Required action | Status |
| --- | --- | --- | --- | --- |
| SP17 | Action comparison unnecessarily requires ambient restriction to commutative sheets | CANONICALIZE | Extract `MarkedProjectorActionComparison`; retain extension-based comparisons as lossless specializations; prove the full-matrix obstruction and instantiate the new core. | DONE; FULL BUILD AND VERIFICATION PASS |
| SP18 | Geometric point span, free span class, matrix coefficient, and Chow class | CONNECT / KEEP DISTINCT | Construct the split-span coefficient realization on actual geometric classes; retain the free source, its matrix image, and genuine Chow as distinct objects. | COEFFICIENT BRIDGE PROVED; CHOW/BETTI OPEN |

SP18 validation: full Lean build, declaration/axiom verification, single-PDF
build, and independent mathematical/parity review passed. Detailed scope and
verification are recorded in `0008-split-span-cycle-realization.md`.

| Lean object | Mathematical role | Canonical TeX notation |
| --- | --- | --- |
| `SplitPointGeometry.scheme` | finite split scheme | $Z_I=\operatorname{Spec}(k^I)$ |
| `SplitPointGeometry.pointInclusion` | selected component inclusion | $s_i:\operatorname{Spec}k\to Z_I$ |
| `SplitPointGeometry.pointSpan` | actual point-supported diagonal span | $Z_I\xleftarrow{s_i}\operatorname{Spec}k\xrightarrow{s_i}Z_I$ |
| `SplitPointGeometry.pointProjector` | its free finite-étale span basis class | $\pi_i$ |
| `SplitPointCorrespondence.ZeroCycles` | finite rational coefficient module, not yet identified with scheme Chow | $\mathbf Q^I$, $I=\{0,1\}$ |
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
| `SplitSpanRealization.Presentation` | finite split presentation of an existing geometric class | witness only; no independent object symbol |
| `SplitSpanRealization.classSubmonoid` / `SplitClass` | split-presentable submonoid of actual finite-étale span classes | $\mathcal S_{\mathrm{sp}}(Z_I/k)$ |
| `SplitSpanRealization.FreeAlgebra` | free rational linearization of that submonoid, before coproduct relations | $\mathcal C_{\mathrm{sp}}(Z_I/k)$ |
| `SplitSpanRealization.toFiniteEtaleFreeAlgebra` | injective source algebra inclusion | $j_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\hookrightarrow\mathcal C^{\mathrm{free}}_{\mathrm{f\acute et}}$ |
| `classMatrixHom` / `SplitSpanRealization.realization` | point-count assignment and its rational algebra extension | $\chi_{\mathrm{sp}}:\mathcal C_{\mathrm{sp}}\twoheadrightarrow M_I(\mathbf Q)$ |
| `GeometricSplitPoints.projector` | split-source point projector whose ambient image is the original point span | $\pi_0^{\mathrm{sp}}$, with $j_{\mathrm{sp}}(\pi_0^{\mathrm{sp}})=\pi_0$ |
| `GeometricSplitPoints.coefficientRealization` | existing coefficient action composed with the new geometric-source map | $\rho\circ\chi_{\mathrm{sp}}$ |
| `GeometricSplitPoints.markedComparison` / `projectorLift` / `palomarTargetSquare` | canonical comparison/lift/square specialized to the actual source | no new notation; $(\rho\circ\chi_{\mathrm{sp}})\circ\varphi_{\pi_0^{\mathrm{sp}}}=\varphi_{P_{-1}}$ |

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
