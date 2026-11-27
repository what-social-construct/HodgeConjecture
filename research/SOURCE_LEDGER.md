# Source ledger

Every row must map a source theorem to the exact hypotheses and conclusion of
the Lean interface it is intended to discharge. A topic-level citation is not
enough.

In the manuscript, an exact standard source input is stated in the specialized
form used here and cited; its published proof is not repeated. When a source
theorem is used as an imported premise, Lean represents it as a named
proposition parameter and the surrounding result remains visibly conditional
on that parameter. Directly proved finite-split specializations instead
record the exact comparison of definitions, without adding a source axiom.

The `HodgeConjecture/Inputs/` modules package selected conclusions separately.
They are not formalizations of complete source theorems, and no global proof
instance supplies them. Their conditional consumers are distinct from the
still-open source-to-geometric instantiations and the application-specific
graph/action and coverage problems; see `working/0016-source-input-packages.md`.

Last source/interface review: 2026-11-27 (actual reciprocal scheme charts,
original cover-swap/circle-inverse signs and infinity Gysin).
Latest formal checkpoint: 2026-11-27 (every complex-valued P¹ point, selected
normal-chart unit-scale independence and original point-class certificates;
earlier checkpoints retain their scope).
Earlier source records retain their original
validation scope.

### Original holomorphic Betti comparison on canonical P¹ (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Original P¹ H² coordinate, canonical point homeomorphism and rational generator | `ProjectiveLineHolomorphicComparisonIso.sourceCoordinates`, `generator_ne_zero` | Source is the exact tensor complexification of canonical scheme-point rational singular H², with complex dimension one |
| Existing rational-diagonal zero detection for the original 0053 comparison | `comparison_embedded_generator_ne_zero` | The original `Scheme.ComplexPoints.holomorphicBettiComparison` has nonzero image on the transported rational cover generator; no substitute map is used |
| Separately constructed cochain-induced holomorphic isomorphism from 0055 | `targetCoordinates`, `target_finrank` | Used only to prove the same intrinsic holomorphic target has complex dimension one; equality of comparison maps is not assumed |
| Complex-linear one-dimensional coordinate calculation | `scalarComparison_apply`, `scalarComparison_one_ne_zero`, `comparison_bijective`, `holomorphicBettiComparison_isIso`, `comparisonEquiv` | The exact original canonical P¹ degree-two map is bijective and has a native inverse; generic holomorphic comparison remains open |

See [0056](working/0056-projective-line-holomorphic-comparison-iso.md).

### Complex singular cochains and derived constant sheaf (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Native postcomposition by ℚ → ℂ, `ScalarRestriction.sheafifyMap_fac` and the original pullbacks | `SingularCoefficientChange.coefficientMap`, `comparison_coefficient`, `globalUnit_coefficient_complex`, `coefficientCohomologyMap` | Literal coefficient inclusion on the same singular simplices; strict compatibility with the original rational and complex local resolutions and global units, including induced cohomology |
| Native tensor unit and the original `cochainComparison` simplex formula | `tensorUnit`, `tensorUnitComplexMap`, `coefficientMap_factor` | Strict equality of original cochain maps; the induced homology pure-tensor identity still requires canonical homology transport |
| Exact scalar restriction of original termwise sections and the flasque whole-complex comparison | `restrictedSectionsHomologyIso`, `coefficientCohomologyMap_sections`, `restrictedHypercohomologyIso` | Strict square through original rational and complex global sections, plus a cross-coefficient iso for every flasque complex; identification with the older injective-resolution `cohomologyIso` remains open |
| Original indexed small-chain inclusion from 0046 and exact `HomCoefficients.functor ℚ ℂ` | `ComplexCoverSmallCochains.restriction_quasiIso`, `restriction_surjective`, `vanishingComplex_acyclic` | Arbitrary indexed open cover; unrestricted complex functionals and no finite-dimensionality assumption on chains or simplices |
| Original locally finite closed refinement and sheaf local-lift constructions, applied to complex simplex functions | `SingularCoefficientChange.sheafificationKernel_acyclic`, `globalCochainsToSheaf_surjective`, `globalCochainsToSheaf_quasiIso` | Native kernel acyclic on any space; global unit surjective and a quasi-isomorphism on paracompact Hausdorff spaces |
| Native open embedding, zero extension and sheafification-on-opens comparison | `openExtension`, `pullback_openExtension`, `cochainSheaf_isFlasque_of_locallyCompact_secondCountable` | Actual open restrictions on the same complex cochain sheaves; local compactness, second countability and Hausdorffness imply flasqueness |
| Existing native complex local resolution, flasque whole-complex comparison and `singleIsoRightDerived` | `cohomologyToConstantSheafDerived`, `_isIso`, `_resolution` | Isomorphism from unrestricted complex singular cohomology to actual right-derived sections of the native complex constant sheaf under the stated topology hypotheses; the map and resolution square are fixed |
| Native holomorphic Poincaré resolution from 0044 and the finite-cohomology coefficient map from 0054 | `complexSingularToHolomorphic`, `cochainHolomorphicComparison`, their `_isIso` theorems | Same intrinsic holomorphic hypercohomology target; a separately named cochain-induced composite is invertible under topology and finite rational-cohomology hypotheses, with equality to the 0053 map still open |
| Native `InjectiveResolution.desc`, derived unit naturality and homology-factor naturality | `rightDerivedPostcomposeIso_hom_naturality`, `comparisonFromComplexHomology_naturality`, `complexHomologyIsoHypercohomology_inv_naturality` | Generic morphisms of the original objects and nonnegative complexes; these are partial naturality stages, not the final scalar-restriction square |

See [0055](working/0055-complex-singular-derived-comparison.md). The exact
identification with the previously constructed holomorphic map remains open.

### Coefficient change with finite-dimensional cohomology (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib kernel quotients, `quotKerEquivRange`, `LinearMap.exists_extend` | `HomCoefficients.functor`, `exists_factor`, `map_exact`; original `RationalDual.functor` and `map_exact` adapters | Arbitrary vector spaces over a field, unrestricted functionals into a commutative coefficient algebra. Native kernel factorization and extension from subspaces prove exactness; the original rational dual specializes this shared construction |
| Native `IsBaseChange.linearMapRightBaseChangeEquiv` and `IsBaseChange.linearMap` | `HomCoefficients.comparison_bijective`, `comparisonEquiv` | Finite-dimensional source vector space. The hom is exactly scalar evaluation A ⊗ Hom_k(V,k) → Hom_k(V,A), using the existing coefficient algebra action |
| Native `LinearMap.baseChange` and `Module.Flat.lTensor_exact` | `tensorFunctor`, `tensorFunctor_map_exact`, `tensorHomologyIso` | Source is a field, hence the coefficient algebra is flat. Actual tensor maps and native homology comparison are used; chain terms need not be finite |
| Native `ShortComplex.homologyMap_mapNatTrans`, exact coefficient functors, `HomologicalComplex.homologyOp` | `complexComparison_quasiIsoAt`, `cohomologyComparison_isIso`, `cohomologyIso` | Only original homology in the compared degree is finite dimensional. The actual cochain coefficient map induces the isomorphism, with its tensor-homology square proved |
| Existing `CochainDualComparison.comparisonIso`, `SingularChainCoordinates.coordinates`, native `Finsupp.llift` | `SingularCoefficientChange.rationalComplexIso`, `complexCoordinates`, `cochainComparison_apply`, induced square | Original rational singular chains and cochains, unrestricted complex simplex functions, native transpose differential; the coefficient map is literally scalar multiplication of original cochain values |
| Native `Module.finite_dual_iff` and exact dual homology; original rational P¹ calculation and canonical Betti equivalence | `finiteHomology_of_finiteCohomology`, `cohomologyComparison_isIso`; original/canonical P¹ controls | Finiteness of original rational cohomology in one degree suffices. P¹ degree two discharges this from existing proofs; the original generator has nonzero image in actual complex-functional cohomology |

See [0054](working/0054-finite-cohomology-coefficient-change.md). No external
proof port, dependency or axiom is added. Identifying this cochain coefficient
map with the exact holomorphic map from 0053 remains open. The native
complex-coefficient sheaf resolution is now constructed in 0055; the
remaining derived naturality square is still required for holomorphic
invertibility.
No scalar-extension/infinite-product interchange is asserted.

### Complex coefficients and actual holomorphic hypercohomology (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib `ModuleCat.restrictScalars`, `extendRestrictScalarsAdj`, `sheafCompose`, `constantCommuteCompose`; native local-surjectivity criterion | `ScalarRestriction.sheaves`, `constantIso`, `constantMap` | Any commutative ring map and original topological space; exact scalar restriction retains sections and restrictions, and native constant-sheaf functoriality constructs the coefficient map |
| Existing `LinearRestriction.injective_linear_restriction_surjective`, flasque whole-complex comparison and `rightDerivedPostcomposeIso` | `ScalarRestriction.cohomologyIso`, `constantCohomologyMap` | Same actual injective resolution in the larger coefficient category; its restricted terms are flasque. Actual ordinary derived sections commute with restriction without asserting preservation of injective sheaves |
| Existing intrinsic `HolomorphicAtlas.comparison_quasiIso`, `singleIsoRightDerived`, `hypercohomologyIsoOfQuasiIso` | `HolomorphicAtlas.constantSheafDerivedIso`, resolution square | Complex-smooth manifold with the existing real/complex scalar tower; original native complex constant sheaf and actual intrinsic holomorphic complex. No individual form-sheaf acyclicity or global-section resolution is assumed |
| Previous original rational comparison; native `LinearMap.liftBaseChange` and `IsScalarTower.of_compHom` | `ScalarRestriction.extendLinear`, `AnalyticBettiComparison.rationalComparison`, `complexComparison` | Original constant-sheaf coefficient map, actual holomorphic target and existing tensor complexification; constructed objectwise on the same manifold. The map is not assumed invertible |
| Pinned Mathlib `LinearMap.exists_leftInverse_of_injective`; native functoriality of split monomorphisms | `constantMap_isSplitMono`, `rationalComparison_mono`, rational-diagonal zero detection | Injective field coefficient inclusion splits linearly. Only the injectivity proof uses a splitting; the comparison map remains fixed by coefficient inclusion. Rational comparison additionally uses the existing Hausdorff, locally compact, second-countable and strong local contractibility hypotheses |
| Existing smooth atlas, canonical affine/P¹ topology, canonical P¹ Betti equivalence and original `coverGenerator_ne_zero` | Scheme `holomorphicBettiComparison`; affine and nonzero actual holomorphic P¹ controls | All fixed relative dimensions and nonnegative degrees; other general scheme topology remains explicit. P¹ image is nonzero in actual intrinsic holomorphic hypercohomology |

See [0053](working/0053-complex-coefficients-holomorphic-comparison.md).
No external proof port, dependency or axiom is added. Next prove invertibility
of this exact complex-linear map on the intended spaces. Scalar extension
through infinite products of simplex functions is not asserted. Proper
algebraic/analytic comparison, periods, purity and prescribed-class coverage
retain their earlier open scope.

### Rational singular groups and actual derived constant-sheaf cohomology (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `BoundedBelowDerived.mapExtendIso`; pinned Mathlib `extendHomologyIso` | `SheafHypercohomology.nonnegativeSectionsHomologyIso` | Same fixed-ring global-sections functor and original nonnegative complex; native extension by zero identifies the original degree with the corresponding integer degree |
| Native extension of quasi-isomorphisms and `Localization.inverts` | `derivedGlobalSectionsMap_isIso`, `hypercohomologyIsoOfQuasiIso` | Original sheaf-complex map is a quasi-isomorphism; the existing derived-sections functor and its original homology map supply the isomorphism, for any fixed commutative ring |
| Existing `globalCochainsToSheaf_quasiIso` and original whole-complex comparison | `SingularCochains.cohomologyToHypercohomology_isIso` | Original rational singular group maps through the original global unit and native degree comparison. Global paracompact Hausdorff and flasque-term hypotheses remain explicit in the general variant; the proved locally compact second-countable Hausdorff criterion discharges them |
| Existing local `comparison_quasiIso` and `singleIsoRightDerived` | `cohomologyToConstantSheafDerived`, `cohomologyIsoConstantSheafDerived` | Contractible-neighborhood bases supply the inverse local-resolution map; the native rational constant sheaf and actual ordinary right-derived global sections are the target. The original resolution square and zero-class detection are proved |
| Existing scheme analytic atlas, canonical affine/P¹ topology and canonical P¹ homeomorphism | Scheme wrappers and nonzero derived P¹ fixture | Strong local contractibility is proved for smooth fixed-relative-dimension schemes; other point-topology hypotheses remain explicit and are discharged on canonical examples. The original degree-two class has nonzero image in the actual derived constant-sheaf target |

See [0052](working/0052-rational-singular-constant-sheaf-comparison.md).
This assembles existing proofs and native maps. No external proof port,
dependency, axiom or replacement cohomology object is added. The subsequent
0053 checkpoint above constructs the complex-linear comparison to the
original holomorphic target; its invertibility remains open.

The generic local-exactness module now imports native local contractibility
directly. Its unused geometry-helper import moves to the scheme wrapper
that actually uses the normed-space and chart specializations. The import
guards for generic local exactness and the singular resolution now forbid
local geometry as well.

### Original whole-complex derived comparison (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Native cycle objects and differential factorization; pinned Mathlib `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` and `epi_of_shortExact` | `FlasqueComplex.cycles_isFlasque`, `sections_acyclic` | Original acyclic bounded-below complex with native flasque abelian sheaf terms; induction on its lower bound and actual section lifting prove sections acyclic on every open |
| Native cokernel short complex and its homology long exact sequence | `FlasqueComplex.sections_quasiIso_of_mono` | A monomorphic quasi-isomorphism between native flasque complexes, with bounded-below target; the original quotient is acyclic and flasque, so the actual sections map is a quasi-isomorphism |
| Pinned Mathlib `CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`; original derived-functor unit and its naturality | `SheafHypercohomology.isIso_comparison_of_flasqueTerms` | Any fixed commutative ring and original bounded-below flasque module-sheaf complex. Native replacement, original exact coefficient forgetting and its native cokernel prove invertibility of the existing unit; no resolution or comparison premise is added |
| Existing `SingularCochains.cochainSheaf_isFlasque` and locally compact second-countable specialization | `derivedComparison_isIso`, `derivedComparisonFromComplexHomology_isIso`; canonical scheme wrappers | The original singular sheaf complex and actual comparison, all integer homology degrees. Canonical affine and P¹ topology hypotheses are already proved |

See [0051](working/0051-singular-derived-comparison.md). The original generic
hypercohomology construction moves unchanged to the shared sheaf layer,
with old public names and de Rham re-exports retained. No external proof
port, dependency or axiom is added. The subsequent 0052 checkpoint above
assembles the composite to actual derived rational constant-sheaf cohomology.

### Actual derived vanishing of flasque sheaf terms (2026-11-10)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `BasisCycles.isZero_Hobj_of_le` (complete Stacks 01EW adaptation) and `FlasqueCech.isZero_cechComplex_homology_of_isFlasque` (09SZ adaptation) | `BasisCycles.isZero_Hobj_of_isFlasque` in `FlasqueDerived` | All opens and all covers; self-refinement discharges cofinality and the existing flasque theorem supplies actual Čech vanishing. The conclusion is the original right-derived section object, with no new resolution or comparison premise |
| Existing `LinearCoefficients.underlying`, exactness and `cechAcyclicInjectives`; native surjective restrictions | `underlying_isFlasque_of_isFlasque`, `isZero_cohomology_of_isFlasque` | Same fixed-ring module coefficient category, arbitrary commutative ring and topological space; underlying sheaves retain the original restrictions |
| Original `BoundedBelowDerived.rightDerivedPostcomposeIso`; native homology under exact postcomposition | Shared `DerivedPostcompose` owner and `LinearCoefficients.cohomologyForgetIso` | Original proof and public name retained; both sides use the same actual injective resolution in the original module category. The old de Rham helper delegates to this construction |
| Existing native flasqueness of `SingularCochains.cochainSheaf X q` from 0049 | `isZero_cochainSheaf_cohomology`, `isZero_cochainSheaf_derivedGlobalSections`, canonical scheme wrappers | Actual module-valued positive derived sections vanish for each original term, on every original open; canonical affine and P¹ topology hypotheses are already proved |

See [0050](working/0050-flasque-derived-sections.md). The existing source
attributions are retained. No external proof port, dependency or axiom
is added. The subsequent 0051 checkpoint above proves the whole-complex
bounded-below comparison, separately from this individual-term vanishing theorem.

### Open restriction and native flasque singular cochain sheaves (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `restrictPresheaf` / `local_restrictSheaf` in `SheafCohomology/OpenImmersionRestriction.lean`; native open-image functor and pointwise covering sieves | `SheafCohomology.openEmbedding_isCocontinuous` | DIRECT cover-lifting proof on the original opens; the existing restriction objects are reused, with their prior Stacks 00A1 attribution retained |
| Pinned Mathlib `Functor.pushforwardContinuousSheafificationCompatibility`, `toSheafify_pullbackSheafificationCompatibility`, `Opens.isOpenEmbedding_obj_top` | `sheafifyOpenIso`, `toSheafify_sheafifyOpenIso`, `toSheafify_app_surjective_of_restrict` | Native isomorphism and original unit; arbitrary fixed commutative coefficient ring and original ambient open |
| Native `IsEmbedding.homeomorphImage`, `TopCat.isoOfHomeo`; existing singular cochain functor and degree evaluation | `SingularCochains.openPresheafIso` | Same original simplex functions on actual subopens and their ambient images; no differential or cochain reconstruction |
| Existing `globalCochainsToSheaf_surjective`, `openExtension`, `pullback_openExtension`, and unit naturality | `toSheafify_open_surjective`, `exists_global_cochain_open_lift`, `cochainSheaf_restriction_surjective` | Actual ambient cochain lifts; only the smaller open must be paracompact Hausdorff; no new global comparison input |
| Native `TopCat.Presheaf.IsFlasque`, open local compactness, subtype second countability, locally compact second-countable sigma-compactness and paracompactness | `cochainSheaf_isFlasque`, `cochainSheaf_isFlasque_of_locallyCompact_secondCountable` | Original module-valued cochain sheaf, all degrees; all-open paracompactness is explicit and is proved from the stated stronger topology hypotheses |
| Existing affine coordinate and P¹/one-point homeomorphisms; actual two canonical affine charts and native open-quotient countable-basis theorem | Affine `locallyCompactSpace`, `secondCountableTopology`; P¹ `canonicalLocallyCompactSpace`, `canonicalSecondCountableTopology` | PROVED original point-topology properties. P¹ local compactness uses the existing homeomorphism and its countable basis descends through the actual open chart quotient. No replacement topology or global transported instance |

See [0049](working/0049-open-singular-sheaf-restrictions.md). No external
proof port, dependency or axiom is added. The subsequent 0050 checkpoint
above proves positive derived-cohomology vanishing for these terms.
The bounded-below whole-complex comparison, general scheme topology and
complex coefficients remain explicit obligations.

### The actual global sheafification unit (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `LocalExactness.sheafifyStalkIso`; pinned Mathlib `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`, `isLocallySurjective_iff` and original `germ_eq` | `toSheafify_exists_local_lift`, `toSheafify_germ_eq_iff` in `SheafifyLocalLifts` | SHARED native local representative and local equality proofs; any commutative coefficient ring, no point-set conditions |
| Existing `RelativeCochains.extension`, `restriction_extension`, `subsetToSubtype` and `subtypeToSubset` | `SingularCochains.openExtension`, `pullback_openExtension` | Same original rational cochains, with extension a right inverse of the original open pullback |
| Pinned Mathlib `precise_refinement`, `exists_iUnion_eq_closed_subset`, `NormalSpace.of_paracompactSpace_r1Space`, `LocallyFinite.point_finite`, `iInter_compl_mem_nhds` | `exists_locallyFinite_closed_refinement`, `exists_cochain_locally_eq_of_closed_cover`, `globalCochainsToSheaf_surjective` | DIRECT PATCHING PROOF on original cochain functions; paracompact Hausdorff spaces, actual finite local germ agreements, without a finite global cover or a supplied comparison |
| Pinned Mathlib exact native `ShortComplex.kernelSequence` and its `homology_exact₂`, `homology_exact₃`; existing `sheafificationKernel_acyclic` | `ComplexKernel.quasiIso_of_surjective_of_acyclic`, `globalCochainsToSheaf_quasiIso`, `globalCochainsToSheaf_homologyIso` | Original unit and its actual native kernel; the target is termwise global sections, with no derived comparison asserted |
| Existing `PolynomialComplexPoints.homeomorph`, `ProjectiveLineComplexPoints.canonicalHomeomorph`, `onePointHomeomorph`; native Hausdorff and paracompact invariance | Canonical affine `t2Space`, `paracompactSpace`; P¹ `canonicalT2Space`, `canonicalParacompactSpace` | PROVED original point-topology hypotheses, in all affine dimensions and on the original glued P¹; no replacement topology or global transported instance |

See [0048](working/0048-global-singular-sheaf-sections.md). No external
proof port, dependency or axiom is added. Sheaf-term acyclicity, derived
sections, general scheme point-topology properties and complex
coefficients remain separate obligations.

### Actual global sheafification kernel (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `LocalExactness.sheafifyStalkIso`; pinned Mathlib `TopCat.Presheaf.germ_eq`, `section_ext`, `germ_res_apply` and `stalkFunctor_map_germ_apply` | `SheafCohomology.toSheafify_app_eq_zero_iff` | DIRECT PROOF for the native unit of a module-valued presheaf over any commutative ring, on every original open; no point-set assumptions |
| Existing `globalCochainsToSheaf`, top-open inclusion and original `subsetToSubtype` / `subtypeToSubset` | `globalCochainsToSheaf_eq_zero_iff`, `globalCochainsToSheaf_eq_zero_iff_cover`, `globalCochainsToSheaf_ker_eq_iSup` | Same actual global map and original cochains; local witnesses form a point-indexed open cover; degreewise kernel equality, not an assumed comparison |
| Pinned Mathlib `ShortComplex.kernelSequence_exact`, exactness under `HomologicalComplex.eval`, `moduleCat_range_eq_ker`, `moduleCat_exact_iff` | `SheafCohomology.ComplexKernel` | SHARED native-kernel degree evaluation and lifting, for module-valued cochain maps; no reconstructed kernel complex |
| Existing `CoverSmallCochains.exists_vanishing_primitive` on the original relative cover kernel | `exists_locallyZero_primitive`, `exists_kernel_primitive`, `sheafificationKernel_acyclic` | Actual locally zero primitives lift through the native inclusion; degree zero vanishes; all degrees on every topological space and canonical scheme point space |

See [0047](working/0047-global-sheafification-kernel.md). No external
proof port, dependency or axiom is added. Global-unit surjectivity and
its comparison with termwise sections are now proved in 0048 above.
Sheaf-term acyclicity, derived sections and complex coefficients remain
separate obligations. Existing local-stalk proof attribution is retained.

### Arbitrary open-cover small chains (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `NativeSimplexGeometry.lebesgue_number`; pinned Mathlib compact metric Lebesgue-number lemma and native weights embedding | `lebesgue_number_diam` | ORIGINAL LOCAL GENERALIZATION to an arbitrary indexed open cover of the native compact standard simplex; actual whole-cell weights diameter, without a supplied bound |
| Existing `exists_nativeIteration_mesh_lt`, affine realization/naturality and actual singular iteration | `CoverSubdivision.exists_iteration_small` | REUSED PROOFS on original native chains; any indexed open cover of any original topological space; a maximum over each finite chain's actual support suffices |
| Existing native subcomplex inclusion range and `chainSubmoduleEquiv`; original explicit singular homotopy | `SubcomplexOperators.restrictMap`, `restrictHomotopy`; indexed restricted subdivision | SHARED CONSTRUCTIONS; support preservation is proved from actual simplex images, with no openness needed for preservation itself |
| Existing `ChainHomologyClasses.quasiIso_of_eventual_image` | `CoverSmallChains.inclusion_quasiIso` | Actual restricted operators and original inclusion; all premises discharged by the proved subdivision, homotopy and shrinking, without a comparison input |
| Existing exact `RationalDual` and `CochainDualComparison.pullback_quasiIso` | `CoverSmallCochains.restriction_quasiIso` | Original rational simplex-function restriction; no finite-dimensionality assumption |
| Existing `RelativeCochains.extension`, `shortComplex_shortExact`; pinned Mathlib `ShortComplex.ShortExact.acyclic_X₁` | `restriction_surjective`, `vanishingComplex_acyclic`, `exists_vanishing_primitive` | Original relative kernel, all degrees including zero; actual primitives retain vanishing on the same indexed cover |

See [0046](working/0046-arbitrary-open-cover-small-chains.md). No external
proof port or new dependency is used. Cover-independent iteration proofs
retain their names in `SingularSubdivisionIteration`; two-open consumers
specialize the indexed proof. The actual global-unit kernel identification
and acyclicity are now proved in 0047 above; 0048 proves global
surjectivity and the termwise-section comparison under its topology
hypotheses. Derived sections and complex coefficients remain open.

### Rational singular sheaf resolution (2026-11-09)

The [checkpoint](working/0045-singular-cochain-sheaf-resolution.md) uses
existing local singular cochains, contractible vanishing and path-connected
degree-zero calculations. Native pinned Mathlib supplies `Opens.toTopCat`,
`Opens.inclusionTopIso`, contractible balls, neighborhood bases,
`OpenPartialHomeomorph.homeomorphOfImageSubsetSource`, native sheafification,
and `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`.
The new local proofs assemble these on the original carriers; no external
proof is ported. The previous local-stalk proof attribution is retained.
Shared sheafification and the existing global-sections definition move
to `SheafCohomology.LinearSheaves`; de Rham reuses them.

The primary comparison papers [Sella](https://arxiv.org/abs/1602.06674)
and [Petersen](https://arxiv.org/abs/2102.06927) were audited for the
remaining global step. They distinguish local resolution from global
comparison and explain the point-set hypotheses in the classical
sheafification route. They are mathematical references, not imported
Lean proofs or a substitute for the remaining sheaf-acyclicity and
derived-section arguments. No full singular/sheaf comparison theorem was located in the
pinned Mathlib audit; no replacement comparison assumption is introduced.
Complex coefficient compatibility remains an explicit separate obligation.

### Intrinsic holomorphic Poincaré comparison (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Existing `HolomorphicForms.pullback_comp`, `pullback_differential` and native derivative locality | `chartPullback_compatible`, `fromChart`, `chartEquiv`, `chartComplexIso` | Native complex C∞ manifold; an actual intrinsic open contained in a chart source. The derivative cocycle, inverse laws and differential compatibility are proved. No chart-extension premise. |
| Existing coordinate `locally_exact_positive` from the constructed radial homotopy | `HolomorphicAtlas.locally_exact_positive` | Closed positive-degree intrinsic form, original point and compatible real scalar structure on the model. Restrict, construct the existing coordinate primitive, and transport back to a neighborhood in the same topology. |
| Existing coordinate `locally_constant_zero` and original coordinate constants | `HolomorphicAtlas.constant`, `locally_constant_zero`, `augmentation_exact` | Degree-zero kernel is locally the same complex constants; no connected-open or global-constancy premise. |
| Original coordinate augmentation's native local-injectivity proof; `LocalExactness.exact_of_exists_local_preimage`; native exact augmented-complex criterion | `ConstantLift.mono`, `AugmentedComplex.quasiIso`, intrinsic `comparison_quasiIso` | Actual sheafification lift, proved local constancy, monomorphism and positive exactness. Coordinate and intrinsic comparisons share these proofs. The resulting native map is a full sheaf quasi-isomorphism. |
| Constructed canonical analytic manifold for `SmoothOfRelativeDimension d x` | `Scheme.ComplexPoints.holomorphicComparison_quasiIso` | Same original canonical scheme points and topology, in every degree; actual affine spaces and original glued P¹ instantiate it. No comparison-data input or new source axiom. |

This is transport of the existing coordinate construction through the
proved atlas, using the already pinned native Mathlib. No new download,
external proof port or dependency was needed. The
[checkpoint](working/0044-intrinsic-holomorphic-poincare.md) leaves the
analytic/singular and proper algebraic/analytic comparisons, the general
period isomorphism and purity open.

### Intrinsic forms and the all-degree algebraic map (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib `Analysis/Calculus/DifferentialForm/Basic.lean`, `extDeriv_pullback` | `HolomorphicForms.pullback_differential` | Actual complex C∞ coordinate map, source/target coordinate opens and original native alternating sections; local extension independence and naturality are proved, with no comparison input. |
| Native `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear` and `alternatizationL`; determinant expansion | `covectorWedge`, `wedgeOneForms` | Actual continuous covectors and original sections; coefficient is the determinant, with degree-one identity and no factorial scaling. |
| Existing `kaehlerRealization`, `AlgebraDeRham.formsMap`, `exteriorPower.alternatingMapLinearEquiv` | `formsRealization`, `algebraicFormsMap`, `algebraicFormsMap_one` | Genuine algebra map into holomorphic functions; all original Kähler exterior powers, extending the same degree-one map. No alternative form carrier. |
| Native `Matrix.det_succ_column_zero`; shared `span_range_smul_ιMulti_D_eq_top`; proved coordinate pullback | `extDeriv_coordinateGenerator`, `algebraicFormsMap_differential` | Universal coordinate generator gives the determinant volume form; the shared spanning theorem proves the full chain law, without a supplied compatibility premise. |
| Existing native coordinate forms sheaf and analytic atlas | `HolomorphicAtlas.formsPresheaf_isSheaf`, `complex` | Any native complex C∞ manifold; actual derivative descent equations glue uniquely and d preserves them. |
| Original `chartEvaluation`, shared scheme section algebras and proved all-degree naturality | `Scheme.ComplexPoints.algebraicFormsMap`, `algebraicFormsComparison` | Scheme smooth of fixed relative dimension over ℂ; original regular evaluation, Kähler forms, scheme restrictions and intrinsic analytic opens. This supplies a map, not an algebraic/analytic comparison isomorphism. |

All sources above are already local at the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, or existing project constructions.
No new source download, external proof port or dependency is introduced.
The [checkpoint](working/0043-holomorphic-forms-descent.md) records the
all-degree map. Intrinsic local Poincaré comparison is now completed in
[0044](working/0044-intrinsic-holomorphic-poincare.md); analytic/singular,
proper comparison and purity remain open.

### Canonical analytic atlas and actual evaluations (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` and `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` | `Scheme.ComplexPoints.exists_etaleCoordinates` | IMPORTED PROOFS with actual original section rings and constants; a scheme smooth of relative dimension d over ℂ gives an actual étale morphism from an affine neighborhood to Spec ℂ[Fin d]. No atlas input |
| Axiom Weil [EtaleLocalHomeomorph](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/EtaleLocalHomeomorph.lean), local implicit-function and standard-étale construction only; native [ImplicitContDiff](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ImplicitContDiff.lean) | `exists_analyticImplicitFunction`, `exists_analyticOpenPartialHomeomorph_of_etale` | PORTED AND STRENGTHENED PROOFS: complex analytic polynomial equation, an original point/root and invertible derivative construct the inverse and retain `ContDiff ℂ ω` regularity in every finite parameter dimension. The partial homeomorphism restricts the actual scheme map in the existing evaluation topology; every regular function on its affine source is an analytic coordinate expression. Unrelated Nullstellensatz/étale-site portions omitted |
| Existing `AffineComplexPoints.structureMorphism` and `homeomorphZeroLocusOfIsAffine`; affine-line presentation argument in Weil [RiemannSurface](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean) | `PolynomialComplexPoints.homeomorph`, `homeomorph_ofAlgHom`, `homeomorph_symm_apply` | GENERALIZED PROOF for Spec ℂ[Fin d], reusing the original affine structure map and regular coordinates. The inverse is the original polynomial evaluation scheme point; no transported topology or replacement point carrier |
| Weil [RiemannSurface](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/RiemannSurface.lean), algebraic atlas and regular-function/morphism arguments | `exists_isAlgebraicChart`, `analyticChartedSpace`, `analyticIsManifold`, `contMDiffOn_evalOrZero`, `contMDiff_map` | PORTED AND GENERALIZED from relative dimension one to d. Constructed analytic étale inverses replace the curve-only differentiability-to-analyticity shortcut. Native analytic manifold structure uses the same canonical point topology; all regular sections on arbitrary opens and scheme morphisms between different fixed dimensions are analytic. No supplied chart-compatibility record |
| Existing `evalHom`, `constHom`, original section restrictions and `eval_map_point`; native bundled complex smooth-function algebra | `regularFunctionsAlgebra`, `regularEvaluation`, `chartEvaluation`, restriction/pullback compatibility | ORIGINAL LOCAL CONSTRUCTION of actual evaluation algebra maps into native complex C∞ functions. Scalar structure is explicitly the original constants and is not registered ambiguously on section rings. Chartwise and intrinsic evaluations agree pointwise. Provides the actual degree-zero input to the existing Kähler realization |
| Existing two-chart `projectiveLineOpenCover`, native polynomial standard smoothness and source locality | `projectiveLineAffineStructureMorphism_smoothOfRelativeDimension`, `projectiveLine_smoothOfRelativeDimension` | ORIGINAL LOCAL PROOFS over any commutative base. The same glued P¹ model is smooth of relative dimension one, hence the general canonical analytic atlas applies. No separate Proj model or assumed smoothness |

The [checkpoint](working/0042-canonical-analytic-atlas.md) records exact
scope and validation. `SmoothRegularZeroSet`, `EtaleSections` and
`ProjectiveLineCharts` were audited but not ported: the first two are not
needed for this direct analytic étale construction, and the last uses a
different Proj model. The original curve file itself does not prove the
higher-dimensional analytic result; that generalization uses the
strengthened local proof here. [Attribution/license](../third_party/axiom-weil/README.md)
are retained. Intrinsic forms descent, the full algebraic forms map,
analytic/singular comparison, proper comparison and purity remain OPEN.

### Higher-degree radial Poincaré comparison (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib [Alternating/Curry](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean) and [Alternating/Uncurry/Fin](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean): `curryLeftLI`, `alternatizeUncurryFin_curryLeft`, native alternating-sum formula | `contraction`, `contraction_alternatize`, `extDeriv_eulerContraction` | ORIGINAL LOCAL PROOFS on the same native coefficients; insertion, finite-sum signs, derivative product rule and Euler degree factor proved for vector-valued forms over a nontrivially normed field. No source homotopy premise |
| Pinned Mathlib [ParametricIntervalIntegral](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean): `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, compact-neighborhood and complex smoothness APIs | `hasFDerivAt_parameterIntegral`, `contDiffOn_parameterIntegral` | IMPORTED differentiation theorem with all bounds, measurability, integrability and differentiability conditions discharged from actual local complex C∞ regularity along the fixed unit interval. Compactness gives a common parameter neighborhood; induction proves complex C∞ regularity |
| Pinned Mathlib [IntervalIntegral/ContDiff](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/IntervalIntegral/ContDiff.lean): `integral_deriv_of_contDiffOn_Icc`, native linear-map integral commutation | `radialHomotopy`, `differential_radialHomotopy`, `differential_radialHomotopy_of_closed` | ORIGINAL weighted radial construction, complex-smooth coefficients, actual dK + Kd = id in every positive degree on a convex coordinate open. The endpoint computation retains the factor 1/(n+1) for constant forms |
| Native [CurveIntegral/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean): `curveIntegral_segment`; original coefficient equivalences | `radialIntegral_zero_eq_segmentPrimitive`, `radialHomotopy_zero_eq_primitive` | PROVED equality with the existing degree-one integral and normalized zero-form section; no independent replacement primitive |
| Existing shared local sheaf exactness criterion and native quasi-isomorphism APIs | `locally_exact_positive`, `exact_positive`, `complex_exactAt_positive`, `comparison_quasiIso` | ORIGINAL LOCAL PROOFS using actual radial primitives after shrinking to balls. Full local sheaf comparison in every coordinate dimension; finite dimensionality not needed. The smooth analytic atlas is constructed above; intrinsic forms descent, algebraic/analytic forms comparison, singular comparison and purity remain OPEN |

See [0041](working/0041-higher-degree-holomorphic-poincare.md). This closes
the higher-degree coordinate gap recorded in the following checkpoint;
it does not import a general scheme comparison from Axiom Stacks or Weil.

### Holomorphic complex and local Poincaré comparison (2026-11-09)

| Exact proof source | Local interface | Hypotheses, endpoints and decision |
| --- | --- | --- |
| Pinned Mathlib [DifferentialForm/Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean): `extDeriv`, `extDeriv_add`, `extDeriv_smul`, local congruence and `extDeriv_extDeriv_apply` | `HolomorphicForms.differential`, `differential_eq_of_extension`, `restrict_differential`, `differential_comp` | IMPORTED PROOFS; actual complex alternating coefficients and complex C∞ sections on coordinate opens; locality proves agreement of local extensions; no supplied differential or square-zero premise |
| Pinned Mathlib [Manifold/Sheaf/Smooth](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Sheaf/Smooth.lean): `smoothSheaf` and native bundled-map algebra | `HolomorphicForms.Sections`, `HolomorphicDeRham.formsSheaf`, `complex` | REUSED actual complex C∞ coefficient sections and sheaf property; fixed-ℂ module upgrade; no general scheme analytic atlas inferred |
| Pinned Mathlib [CurveIntegral/Poincare](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean): `Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric` | `hasFDerivAt_segmentPrimitive`, `differential_primitive`, `locally_exact_one` | IMPORTED PROOF with discharged symmetry and real-differentiability conditions from the actual closed complex one-form. Convex coordinate open, base point in it and complete codomain ℂ. Primitive is the actual segment integral and is proved complex C∞. Covers degree one in every coordinate dimension, not higher-degree Poincaré |
| Pinned Mathlib [Calculus/MeanValue](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/MeanValue.lean): `Convex.is_const_of_fderivWithin_eq_zero` | `locally_constant_zero`, `augmentation_exact`, `comparison_quasiIsoAt_zero` | IMPORTED PROOF; shrink inside the original open to a ball, obtain actual local constants, then use original sheafification. No connectedness of the full open or global constant-kernel assertion |
| Axiom Weil [HolomorphicCohomology](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Geometry/Manifold/Sheaf/HolomorphicCohomology.lean), extension-by-zero helper only | Auxiliary `extend`, `contDiffAt_extend` in `Geometry/Holomorphic/Forms.lean` | NARROW ADAPTATION generalized to native alternating coefficient spaces; local derivative helper only, no Dolbeault/de Rham comparison imported |
| Axiom Weil [Holomorphic](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Geometry/Manifold/Sheaf/Holomorphic.lean): `TopCat.Sheaf.exact_of_exists_local_preimage` | Shared `SheafCohomology.LocalExactness.exact_of_exists_local_preimage` | PORTED PROOF generalized to existing fixed-ring module sheaves; actual germ representatives and shrinking prove exactness on the original stalks. [Attribution/license](../third_party/axiom-weil/README.md) retained |
| Native finite-dimensional linear dependence and alternating maps | `coefficient_eq_zero_of_finrank_lt`, `complexLine_section_eq_zero` | DIRECT LOCAL PROOFS; all coefficients above actual dimension vanish. The original complex-line comparison is preserved and now specializes the all-degree theorem above |
| Native `Derivation.liftKaehlerDifferential`, existing `AlgebraDeRham.kaehlerMap`, native `Polynomial.aeval` | `holomorphicDerivation`, `kaehlerRealization_D`, `algebraicOneFormsMap_D`, `polynomialEvaluation_apply` | DIRECT LOCAL PROOFS; analytic Leibniz rule proves the derivation, genuine algebra maps give da ↦ d(φ(a)), polynomial evaluation is constructed. No new Kähler carrier or supplied type/map compatibility. Smooth-scheme holomorphic evaluation is constructed above; full forms comparison remains OPEN |

The [checkpoint](working/0040-holomorphic-derham-local-poincare.md) records
the original degree-zero/one comparison. The audited Weil holomorphic and
curve Dolbeault files do not supply a general scheme atlas or the desired
singular period map. The higher-degree contraction is proved locally in
[0041](working/0041-higher-degree-holomorphic-poincare.md).

### Canonical complex points and comparison endpoints (2026-11-08)

| Source result | Local interface | Exact scope and decision |
| --- | --- | --- |
| Complex-point definitions and regular-function topology in [Weil Definitions](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Definitions.lean) and [AnalyticTopology](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/Defs/AlgebraicGeometry/ComplexPoints/AnalyticTopology.lean) | `AlgebraicGeometry.Scheme.ComplexPoints`, `Mem`, `eval`, `basicSets`, `instTopologicalSpace`, open-point subsets and continuous affine evaluations in `Geometry/ComplexPoints.lean` | PORTED PROOFS; actual sections over the same complex base; native Mathlib only; monolithic definitions and metadata omitted |
| [ComplexPoints/Functoriality](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/Functoriality.lean) | `Geometry/ComplexPointsFunctoriality.lean`: evaluation ring maps, affine evaluation embedding, arbitrary-open evaluation continuity, continuous maps, open/closed immersion embeddings and polynomial-coordinate zero-locus homeomorphisms | PORTED PROOFS; same actual sections, rings and scheme maps; no de Rham or purity conclusion; [license and attribution](../third_party/axiom-weil/README.md) |
| Native `Spec`/global-section naturality, original P¹ charts and singular homeomorphism pullbacks | `AffineComplexPoints.homeomorph`, `ProjectiveLineComplexPoints.canonicalHomeomorph`, `SchemeBetti` functors, `ProjectiveLineCanonicalComparison` | DIRECT LOCAL PROOFS; independently specified affine/P¹ topologies agree with the canonical one; old cochains, period normalization, filtration and Chow source retained |
| [Stacks DeRham/RealizationComparison](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksFrontier/AlgebraicGeometry/DeRham/RealizationComparison.lean) | No new imported comparison | ENDPOINT MISMATCH for the required period map: module-sheaf versus underlying abelian-sheaf hypercohomology on the same algebraic space |
| [Stacks HodgeWeilCohomologyTheory](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksFrontier/AlgebraicGeometry/DeRham/HodgeWeil/HodgeWeilCohomologyTheory.lean) and [HodgeSpreadingOut/CharZero](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/CharZero.lean) | No new degeneration or purity instance | SUBSTANTIVE HYPOTHESES remain: `hbetti` and `hDI`; neither discharges canonical-conjugation opposedness for our target |
| [Weil AnalyticSpace](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/AnalyticSpace.lean) and [Betti/ArtinComparison](https://github.com/AxiomMath/Weil/blob/27cdb2049be62ee2911429b47f54774078450e32/Weil/AlgebraicGeometry/ComplexPoints/Betti/ArtinComparison.lean) | Not ported here | TOPOLOGICAL SHEAVES / ÉTALE-TORSION comparison; not an algebraic de Rham-to-singular period isomorphism or a holomorphic de Rham construction |

The [checkpoint](working/0039-canonical-scheme-betti-target.md) records the
remaining local Poincaré, analytic/singular and algebraic/analytic map
comparisons. No new Lake dependency, global project axiom or substantive
comparison-hypothesis wrapper is introduced by this proof port.

### Tate/Hodge graph compatibility (2026-11-08)

The [bridge checkpoint](working/0038-tate-hodge-graph-bridge.md) directly
proves the Tate filtration, pure products, Hodge-piece preservation and
graph compatibility using Mathlib's tensor/product equivalence and
submodule lattice operations. The original `BlockGraphProjector`,
filtration-derived cycle model and `TateGraphProjector` equivalence are
reused. The Tate convention is ℚ(-p) of type (p,p), weight 2p. No external
comparison or purity theorem is installed. The former Hodge-compatibility
premise is discharged; geometric Chow construction/detection, the action,
general comparison/purity and coverage remain explicit or open.

### Cyclic filtered defect construction (2026-11-08)

The [construction](working/0037-filtered-projector-defect.md) uses Mathlib's
`Module.AEval`, `Submodule.span`, `Polynomial.degreeLE`,
`IsModuleFiltration`, `Module.annihilator` and finite-presentation theorem
over a Noetherian ring. The generator is the repo's existing
`projectorIdempotenceDefect`, specialized to `C.closureClass x`; existing
restriction and Chow exactness provide the boundary-image consequences.
No paper theorem, connection, Hodge-family comparison or vanishing premise
is added. The annihilator and all relations are computed from the original
algebra, and a nonzero polynomial closure controls the boundary inference.

### Comparison, weights and vanishing (2026-11-08)

These references distinguish the geometric period comparison, arithmetic
de Rham–Betti classes, and the elimination of a boundary obstruction. None
supplies an installed Lean theorem or a new premise. The
[target and vanishing audit](working/0036-filtered-hodge-target-and-vanishing.md)
records the implementation and comparison with the Jacobian collision repo.

| Source | Exact scope inspected | Application and remaining construction |
| --- | --- | --- |
| [Kreutz–Shen–Vial, *De Rham–Betti classes with coefficients*, 2206.08618v3](https://arxiv.org/html/2206.08618v3) | Definitions 2.1 and 2.3 specify coefficient spaces, a complex comparison, and arithmetic de Rham–Betti classes. Theorem 5.13 applies to an abelian variety over K ⊂ ℚ̄ geometrically isogenous to a product of elliptic curves. For L ⊂ ℚ̄ containing at most one CM field of its CM factors, L-de Rham–Betti classes in degree 2k with Tate twist k are L-algebraic. | Useful for comparison data and Tate normalization. Arithmetic descent under the period map is distinct from rational type-(p,p) membership. The geometric comparison is invoked, not supplied as Lean code. Use this version's three authors and updated title. |
| [Ji, *Weight of the De Rham-Betti Structures of Abelian Varieties*, 2605.07009v1](https://arxiv.org/html/2605.07009v1) | Theorems 1.4/4.2 put the homotheties inside the de Rham–Betti group of an abelian variety over the algebraic closure of ℚ. Corollaries 1.3/5.6 exclude nonzero odd-degree de Rham–Betti classes. | Weight constraints on arithmetic period classes; no construction of the classical comparison or general even-degree Hodge-class coverage. |
| [Wiersig, *A fully faithful p-adic Riemann–Hilbert functor for filtered coherent D-modules*, 2609.24123v1](https://arxiv.org/html/2609.24123v1) | Theorem A / Corollary 4.12 proves full faithfulness of the filtered solution functor on bounded good filtered coherent D-modules, for smooth rigid-analytic varieties over a complete discretely valued mixed-characteristic field with perfect residue field. The good filtrations are exhaustive, locally bounded below, compatible with operator order and Rees-coherent; the target uses the positive almost de Rham period sheaf. | Filtered reconstruction reference in a p-adic setting; not the required complex algebraic de Rham–rational singular comparison. |
| [Yun, *Generic vanishing of Dolbeault cohomology of mixed Hodge modules on abelian varieties*, 2610.22678v1](https://arxiv.org/html/2610.22678v1) | Theorem 1.6 identifies twisted support loci; Theorem 1.17 and §7 prove flatness of the extended Fourier–Mukai cohomology over the twistor parameter. Proposition 7.1 excludes parameter torsion in degree zero; Theorem 7.2 supplies truncation closure. | Candidate method for eliminating a generically invisible defect. Requires a matching mixed-Hodge-module family and identification of the defect; geometric boundary support is not automatically torsion in this parameter. |

Barz 2512.04300v2 is already recorded under “Further de Rham references”;
its positive-characteristic logarithmic Cartier comparison remains separate.

### Recent references for geometry, computation and generation (2026-11-08)

These eight preprints were inspected at the stated theorem level. They are
external references, with the candidate interface or missing construction
identified below; none is added as a Lean premise or a dependency. This
survey does not certify their complete proofs. Versioned arXiv links fix
the source statements assessed here.

| Source | Exact material inspected and hypotheses | Existing interface, applicability and remaining obligation |
| --- | --- | --- |
| [Ze Xu, *On motivic multiplicativity of cyclic covers*, 2611.01008v1](https://arxiv.org/html/2611.01008v1) | Theorem 1.1 and §2: a degree-d cyclic cover, d≥2, of a smooth connected projective complex n-fold with trivial Chow groups, branched along a smooth divisor in \|dL\| with L ample, has the stated Chow–Künneth multiplicativity bounds. Part (ii) additionally assumes every positive-codimension Chow class of the base is supported on the branch divisor; it proves a modified-diagonal relation and multiplicativity when d=2. The construction separates the deck-invariant motive from a complementary motive with cohomology only in degree n. | Closest match to `RationalDegreeTransfer.normalizedProjector` in [Transfer.lean](../HodgeConjecture/Realization/Transfer.lean) and the actual Chow transfer in [FiniteFlatTransfer.lean](../HodgeConjecture/Realization/Chow/FiniteFlatTransfer.lean). Identifying that operator with the deck-graph average needs the geometric correspondence and realization comparisons. The branch divisor prevents treating this as a globally étale cover. Multiplicativity alone does not discharge `HodgePullbackGeneratedBy` or `ClassDependentChowBettiGeneration` in [UpstairsGeneration.lean](../HodgeConjecture/Realization/Chow/UpstairsGeneration.lean); middle-degree classes in the complementary piece still need a generation argument. |
| [Olivier Benoist–Samuel Lerbet, *Separating components of real algebraic varieties by cohomological invariants*, 2610.18562v1](https://arxiv.org/html/2610.18562v1) | Corollary 3.4(i): for a smooth real d-fold, d≥1, coniveau at least two for the 2-torsion in integral H^(d+1) implies surjectivity of the degree-d integral-twisted unramified evaluation map to functions on the real components with values in ℤ/2. For G-module coefficients, Lemma 3.6 makes the equivariant-to-unramified map bijective in degrees at most one and surjective in degree two. Corollary 3.9 assumes smooth proper X and that every integral Hodge class in H⁴ lifts to the kernel of real-point evaluation; it concludes equality of two degree-three evaluation images. | Reference for explicit support, purity and lifting hypotheses. No current real-equivariant or unramified-cohomology interface is matched. The target and coefficients differ from the rational complex cycle model. In particular, the Hodge-lifting assumption of Corollary 3.9 must be proved in an application; it does not instantiate the supported Hodge lift in [BoundaryCorrection.lean](../HodgeConjecture/Realization/Chow/BoundaryCorrection.lean). |
| [Quoc-Anh Tran, *Rank two cohomology jump loci on projective varieties*, 2610.36251v1](https://arxiv.org/html/2610.36251v1) | Theorem 1.1 classifies irreducible components of the reduced rank-two jump loci on smooth connected complex projective X by generic projective monodromy type. Its nonrigid dense case uses a torus or an étale quotient of a product with a fixed-determinant, fixed-inertia character-variety component of a proper hyperbolic DM curve. Proposition 5.26 proves étaleness for the particular normalized finite map constructed there, using the preceding Hodge-theoretic setup. | Candidate source for a specialized normalization/étale example; no current character-variety, DM-curve or pro-mixed-Hodge interface is matched. Proposition 5.26 does not prove arbitrary normalized covers étale or supply the extension witness in [FiniteEtaleExtension.lean](../HodgeConjecture/Inputs/FiniteEtaleExtension.lean). The paper's Hodge-subvariety statements concern local-system moduli and do not establish the Chow–Betti generation predicate. |
| [Kehao Cheng, *The Hodge-to-de Rham spectral sequence can be arbitrarily non-degenerate in positive characteristic*, 2610.35243v1](https://arxiv.org/html/2610.35243v1) | Theorem 1.6: over a perfect field of positive characteristic, for n≥1 and i,j≥0 with j≥n−1 and (i,j)≠(0,0), there is a smooth projective variety with a nonzero differential from the specified position on page n, represented by a class surviving the earlier pages. The construction uses finite group schemes and approximation of their classifying stacks. | Scope reference for the general-ring Kähler complex and the actual degree filtration in [SchemeHodgeFiltration.lean](../HodgeConjecture/Realization/DeRham/SchemeHodgeFiltration.lean). Spanning differential forms and proving d²=0 do not imply degeneration. The [degeneration audit](working/0030-hodge-derham-degeneration-audit.md) already separates the bounded P¹ calculation from general characteristic-zero degeneration. No spectral-sequence counterexample or general degeneration theorem is formalized here by this citation. |
| [Shizhang Li–Yuan Yang, *On de Rham–Witt Cohomology of Classifying Stacks*, 2604.03062v1](https://arxiv.org/html/2604.03062v1) | Theorem 1.1 (Corollary 5.12): over any perfect field of characteristic p>0 there is a smooth proper fourfold with asymmetric Hodge–Witt numbers in total degree three. The paper computes low-degree Hodge–Witt cohomology of Bαₚ and uses approximation by smooth proper varieties; §§2–3 develop the associated graded Raynaud-module structures. | Pair with the existing Zhang entry in the earlier de Rham survey for a future characteristic-p direction. No current de Rham–Witt, Raynaud-module or domino-number interface is matched. These Hodge–Witt invariants are defined using slopes and domino numbers; their asymmetry is not a statement about the current complex Betti Hodge decomposition. No general degeneration or prescribed-cycle generation input follows. |
| [Jiun-Cheng Chen–Hsian-Hua Tseng, *On rational curves relative to a divisor*, 2611.05809v1](https://arxiv.org/html/2611.05809v1) | Theorem 1.1: for smooth complex projective X, reduced SNC divisor D, and an integral complete curve C not contained in D with negative (K_X+D)-degree, a dense open subset of C∖D is covered pointwise by rational curves whose normalizations meet D in at most one point. Proposition 5.2 bounds the resulting curve degree using the chosen projective embedding. | Candidate geometric source of actual one-cycles for the carriers in [Basic.lean](../HodgeConjecture/Cycles/Basic.lean). A formal application must construct the curves and their cycle classes, then prove the required image or span statement in the fixed target. Pointwise existence through general points of C does not establish `ClassDependentChowBettiGeneration` for arbitrary Hodge classes or codimensions. |
| [Robert Andrews–Abhibhav Garg–Rafael Oliveira–Éric Schost, *Some algebraic and geometric computations in CH via Chow forms*, 2611.05289v1](https://arxiv.org/html/2611.05289v1) | Results 1.1–1.2 decide vanishing and coefficient support for equidimensional-component Chow forms of projective varieties given by homogeneous rational equations represented by constant-free algebraic circuits. Result 1.4 computes component degrees in FP^CH. Here CH denotes the counting hierarchy. Theorem 4.9 supplies the underlying uniform constant-depth, exponential-size threshold-circuit construction. | Candidate for future explicit support and component computations. A Chow-form encoding would need a proved interpretation in the actual subscheme/cycle carriers of [Basic.lean](../HodgeConjecture/Cycles/Basic.lean), with cycle coefficients and scheme-theoretic multiplicities handled separately, then passage through [RationalChow.lean](../HodgeConjecture/Cycles/RationalChow.lean). The paper's geometric membership tests do not decide membership in the Betti cycle-class image. No Chow-form representation or complexity result is formalized here. |
| [Parsa Bakhtary, *Canonical Projectivization of Algebraic Varieties in Characteristic Zero*, 2611.04314v1](https://arxiv.org/html/2611.04314v1) | Theorem 1.1 fixes a principalization procedure and assigns to a smooth proper characteristic-zero variety a finite smooth-center blowup tower with smooth projective endpoint, natural under semilinear isomorphisms. It preserves the canonical quasi-projective core, and the tower is empty for projective input. Corollary 1.2 lifts every group action by automorphisms to the endpoint. The selection is non-effective. | Candidate reference for projective geometry with a lifted deck action after a smooth proper model has been constructed. The main theorem preserves its specified core; an arbitrary prescribed open needs a separate comparison. Blowup modifications also require separate checks of any needed finite/étale morphism properties. This does not by itself instantiate [FiniteEtaleExtension.lean](../HodgeConjecture/Inputs/FiniteEtaleExtension.lean), the correspondence-composition comparison in [ChowLocalization.lean](../HodgeConjecture/Inputs/ChowLocalization.lean), or prescribed Hodge-class generation. |

Status for all eight entries: **SOURCE INSPECTED / NOT FORMALIZED**.
These are candidate applications and scope checks, not source conclusions
accepted as the missing geometric inputs. The general Chow–Betti
comparison, boundary/action compatibility and prescribed-class generation
obligations in [the gap map](GAP_MAP.md) remain separate. The computational
encoding, if developed, should map to the existing cycle layer rather than
introduce a second cycle or Chow quotient.

### Symmetric-product Chow and transfer reference (2026-11-12)

| Source | Relevant result | Fit to the present proof |
| --- | --- | --- |
| [Youming Chen–Wenchuan Hu, *Chow groups of symmetric products of projective spaces*, arXiv:2610.20239v3](https://arxiv.org/html/2610.20239v3) | Theorem 1.1 proves that the integral cycle-class map for `SP^d(P^n)` is split injective with finite cokernel killed by `d!`, hence its rational cycle-class map is an isomorphism. Lemma 2.1 and Propositions 2.2 and 2.4 give weighted inverse-image and subgroup transfers for a finite coarse quotient, with `q_* tr = [G:H]` on Chow and singular homology and compatibility with cycle classes. Theorem 1.2 exhibits a nonalgebraic integral class of order two. | The transfer formulas are a concrete model for extending the project's rational Chow/Betti transfer comparisons across quotient ramification; their weighted inverse image is not flat pullback. The symmetric products are finite quotients and the paper uses homology, while our general Hodge target is for smooth projective varieties and cohomology. The order-two obstruction disappears rationally and gives no counterexample to the rational Hodge target. We have no actual symmetric-product quotient, weighted transfer, or corresponding Betti transfer formalized here. This source does not discharge the fixed-inertia or prescribed-class-generation gap. |

Status: **SOURCE INSPECTED / CANDIDATE TRANSFER MODEL; NOT FORMALIZED**.

### Actual P¹ zero-point Gysin and cycle comparison (2026-11-07)

The [0035 checkpoint](working/0035-projective-line-zero-point-gysin.md)
uses actual native pair sequences and the already proved small-chain
comparison. No excision, orientation or cycle-comparison premise is supplied.

| Source-matched step | Source and local construction | Scope |
| --- | --- | --- |
| Relative cochains and pair sequence | Native singular restriction, kernel and short exact connecting maps; local `RelativeCochains.lean` | Actual cochain kernels retain original differential; extension by zero proves termwise surjectivity. Pair pullbacks and native boundary naturality are proved. |
| Actual open-cover excision | Existing subdivision/full-to-small quasi-isomorphism, native opposite-complex short-exact comparison; local `ShortExactQuasiIso.lean`, `RelativeUnion.lean`, `RelativeExcision.lean` | Strict relative union gluing and the original restriction quasi-isomorphism give actual excision in all degrees. No dimension comparison or assumed excision is used. |
| Boundary sign | Native `ShortComplex.ShortExact.δ_naturality`; local `RelativeMayerVietoris.lean` | Actual local relative boundary, inverse excision and forgetting equal the old full Mayer–Vietoris boundary. The map `(a, 0)` into the first-minus-second sequence fixes the plus sign. |
| Local oriented Thom class | The actual radial pullback and positively paired circle class; local `Examples/ComplexPointThom.lean` | Actual H²(ℂ, ℂ∖{0}) is identified with singleton H⁰, with unit boundary pairing +1. Local absolute forgetting is zero. |
| Original normal chart and supported class | Original finite evaluation chart and actual pair pullback; local `ProjectiveLinePointSupport.lean`, `ProjectiveLineNormalChart.lean`, `ProjectiveLineNormalChartBoundary.lean` | The zero maps to the original scheme zero and the reciprocal chart is its exact complement. Original simplex maps identify the native pair boundaries. |
| Geometric zero-point cycle normalization | Local Thom, inverse actual excision and original forgetting; local `ProjectiveLinePointGysin.lean`, `ProjectiveLineGysinCycleClass.lean` | The actual Gysin unit is the positive P¹ generator and the ordinary cycle-class image of the original zero-point integral/rational Chow classes. Both maps factor through this distinguished-point Gysin and degree. Other points, chart independence and general Gysin remain open. |

### Actual P¹ Hodge filtration and fixed cycle model (2026-11-07)

The [0034 checkpoint](working/0034-projective-line-hodge-filtration.md)
constructs the geometric filtration before comparing it with the Betti
pieces or using an ordinary cycle map.

| Source-matched step | Source and local construction | Scope |
| --- | --- | --- |
| Actual degree subcomplexes | Native `HomologicalComplex.stupidTrunc`, restriction and extension; local `DegreeFiltration.lean` and `TwoTermDegreeFiltration.lean` | Original terms and differential are retained. Actual inclusions/transitions, level-zero isomorphism and the one-form comparison are proved. A native identity-complex regression distinguishes brutal from smart truncation. |
| Derived image filtration | Original `SheafHypercohomology.hypercohomologyMap` and native bounded-below derived functors; local `HypercohomologyFiltration.lean` and `SchemeHodgeFiltration.lean` | Fᵖ is the actual linear range of the original derived inclusion. No desired filtration subspaces or degeneration premise are supplied. |
| P¹ degree-two computation | Previously proved sheaf-term vanishing and O-term H¹/H² vanishing; local `ProjectiveLineHodgeFiltration.lean` | The actual F¹ map is an isomorphism and F² complex is zero, over every field. This is not a general E₁-degeneration theorem. |
| Actual Betti Hodge pieces | Genuine tensor scalar extension and canonical rational conjugation; local `Betti/ProjectiveLineHodgeStructure.lean` | The independent type-(1,1) decomposition is direct/exhaustive and its filtration is opposed. No cycle-map module is imported in this layer. |
| Geometric filtered comparison | The bounded period map and actual computed filtration; local `ProjectiveLineHodgeComparison.lean` | Both raw and normalized maps preserve all integer levels. Type (1,1) is recovered from actual transported F and its canonical conjugate. This uses no general analytic/Gysin identification. |
| Fixed target model | Existing `RationalHodgeCycleClassModel` and independent ordinary map; local `ProjectiveLineHodgeCycleClass.lean` | Rational Hodge classes are independently geometric; the original infinity class gives every target's explicit witness. Only this constructed fixed-codimension model is asserted. |

### Positive circle pairing and actual P¹ boundary periods (2026-11-07)

The [0033 checkpoint](working/0033-oriented-boundary-period-comparison.md)
retains original native objects and local proved maps. The actual native
connecting formula fixes the sign before the period equivalence is defined.

| Source-matched step | Source and local construction | Scope |
| --- | --- | --- |
| Actual Kronecker pairing and Stokes | Native dual coordinates and `ShortComplex.descHomology`; local `SingularCyclePairing.lean` | Original cochain evaluation on an actual closed native chain descends to actual cohomology and is natural for original simplex maps. |
| Native boundary representative | Mathlib `ShortComplex.ShortExact.δ_apply`; local `SubcomplexConnectingRepresentative.lean` and `SubcomplexDegreeZeroRepresentative.lean` | The actual connecting class is the positive differential of an actual pair lift. Existence and the original H⁰ evaluation bridge are proved. |
| Positive loop and generator | Original complex exponential, actual path simplices and their native faces; local `CircleOrientedCycle.lean` and `CircleOrientedPairing.lean` | Exact endpoint evaluation proves the actual generator pairs +1 with the counterclockwise two-arc cycle; the cycle has no native filling chain. |
| Same actual analytic arcs | Native periodic interval integration and `circleIntegral`; local `LaurentOrientedArcs.lean` | The original Laurent circle integral equals the derivative-weighted integrals on `[-π/2,π/2]` and `[π/2,3π/2]`; native circle maps equal the original complex exponentials. |
| Independent ordinary singular cycle map | The existing proved projective-line Chow degree and actual singular cover generator; local `Betti/ProjectiveLineCycleClass.lean` | Point normalization, principal invariance, rationalization and rational surjectivity hold in actual singular H². This does not identify a separately constructed general Gysin/Poincaré-dual map. |
| Actual tensor and boundary-period comparison | Native tensor scalar extension; local `ProjectiveLineOrientation.lean`, `ProjectiveLineComplexification.lean` and `DeRham/ProjectiveLinePeriodComparison.lean` | Actual analytic and positive boundary pairings uniquely specify the bounded equivalence. Raw Chern period remains `2πi`; the normalized ordinary Chow square is proved. No general analytic-sheaf comparison is asserted. |

### Actual circle and projective-line singular calculations (2026-11-06)

The [0032 checkpoint](working/0032-circle-projective-line-singular-cohomology.md)
uses pinned native Mathlib results and local proofs; no Stacks or other
source conclusion is assumed at the concrete endpoints.

| Source-matched step | Source and local construction | Scope |
| --- | --- | --- |
| Actual cochain homotopy | `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance`; local `SingularHomotopy.lean` transposes the actual chain homotopy through the proved cochain comparison | Original continuous homotopies induce equal actual rational cohomology pullbacks in every degree. |
| Contractible positive-degree vanishing | Native `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`, exact rational dualization, and native `ContractibleSpace.hequiv_unit`; local `SingularContractible.lean` | The original point-chain exactness proves point cohomology vanishes; actual topological contractions give vanishing without finite-dimensionality. |
| Actual circle two-arc calculation | Native complex argument/exponential and interval convexity; local `CircleTopology.lean`, `SingularComponents.lean` and `CircleCohomology.lean` | Actual component evaluation and original continuous pullbacks compute the kernel and image of the actual Mayer–Vietoris boundary. Its quotient gives H¹ as ℚ. |
| Actual P¹ overlap and connecting isomorphism | Native `homeomorphUnitSphereProd`, explicit radial homotopy, and the original P¹ charts; local `PuncturedComplexCircle.lean`, `ProjectiveLineAnalyticCover.lean` and `ProjectiveLineSingularCohomology.lean` | Contractible-chart vanishing proves the native boundary itself is an isomorphism. The forward circle-to-P¹ map is the actual radial pullback followed by this boundary. |
| Rational H² coordinate | The preceding proved maps and the local circle H¹ quotient; `Betti/ProjectiveLineCohomology.lean` | Actual H² of the original complex-point space is ℚ with a nonzero cover generator. The checkpoint above proves its positive boundary-period comparison and independent ordinary cycle map; general analytic/Gysin identification remains open. |

### Projective-line scheme de Rham bridge (2026-11-06)

The [0027 checkpoint](working/0027-projective-line-scheme-comparison.md)
connects the original Čech target to hypercohomology of the constructed
sheaf de Rham complex on the same glued P¹. The scheme bridge uses a field
of any characteristic. Integral Chow classes retain algebraic closure;
rational Chow classes additionally retain characteristic zero.

| Source-matched step | Source and local construction | Scope |
| --- | --- | --- |
| Sheaf forms and actual derived sections | Mathlib's Kähler modules, sheafification and `Functor.rightDerivedFunctorPlus`; local `SheafComplex.lean` and `SheafHypercohomology.lean` | The original structure morphism fixes scalars and restrictions. Hypercohomology is constructed in the actual category of fixed-ring sheaves. No realization or comparison is supplied as a premise. |
| Affine acyclicity | Selected proofs from pinned Axiom [standard-cover vanishing](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Cohomology/Cech/StandardCoverVanishing.lean), [affine vanishing](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Cohomology/Cech/AffineVanishing.lean) and their local algebra/basis helpers | Local rewrites use native Mathlib sheaves and the original section maps. A localized criterion and actual differential bases discharge all P¹ chart/overlap acyclicity inputs in the original coefficient category. |
| Degree-two scheme comparison | Mathlib's homology sequence, derived short-exact-sequence triangles and exact coefficient forgetting; local `TwoOpenModules.lean`, `TwoTermHypercohomology.lean` and `ProjectiveLineSchemeComparison.lean` | The comparison follows actual overlap representatives through the signed Mayer–Vietoris boundary and derived inclusion. It does not choose an isomorphism from matching dimensions. |
| Ordinary Chow-source realization | The original maps from [0026](working/0026-positive-degree-cycle-realization.md), composed with the scheme bridge | Principal invariance, point normalization, rationalization and the rational coefficient bound retain their original ordinary Chow sources. Singular/Betti comparison and general varieties/codimensions remain open. |

This is selective local proof adaptation, with pinned attribution and license
in the [reuse inventory](../third_party/axiom-stacks/README.md). Irrelevant
arithmetic/analysis imports inherited in the restriction helper were pruned.
There is no external Axiom/Stacks Lake dependency and no imported source axiom.
Focused and integration validation of that bridge passed as recorded in
[0027](working/0027-projective-line-scheme-comparison.md).

### Ordinary positive-degree cycle-map construction (2026-11-06)

The selected target is ordinary `CH^p → H^(2p)`. Saito's higher-Chow
results motivate logarithmic and boundary formulas; they are not assumed
as ordinary-cycle algebraicity theorems.

The pinned Axiom snapshot has a genuine
[relative de Rham first Chern class](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/DeRham/FirstChernClass/DeRhamCohomologyFirstChernClass.lean),
formed by logarithmic differentiation and an actual hypercohomology
comparison. It is a source candidate, not a new project hypothesis or an
imported dependency. The local construction selectively adapts its
[exterior Leibniz proofs](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/DeRham/WedgeLeibniz.lean),
[Laurent Euler calculations](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/DeRham/LaurentHomotopy.lean)
and [actual projective-line gluing](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Scheme/Glueing/ProjectiveLine.lean).
The resulting ordinary Čech first-Chern map has actual boundary descent
and nonzero residue normalization. The original ordinary projective-line
Chow-source map now descends through the proved actual principal-divisor
degree law. The P¹ scheme bridge is developed in 0027 above; general-variety
and singular comparisons remain separate. Exact scope is recorded in
[0026](working/0026-positive-degree-cycle-realization.md), with the
[attribution inventory](../third_party/axiom-stacks/README.md).

Status: **LOCAL FORMAL CONSTRUCTION WITH ACTUAL ORDINARY P¹ CHOW SOURCE / GENERAL REALIZATION COMPARISON OPEN**.

### Further de Rham references (earlier 2026-11-05 survey)

These papers are references, not added dependencies or Lean theorem inputs.
The applicability assessments below concern the current realization gaps.

| Source | Exact material inspected | Relevance and limit |
| --- | --- | --- |
| [Scheiblechner, *Effective de Rham Cohomology — The General Case*, 1203.5706v2](https://arxiv.org/pdf/1203.5706v2) | Theorem 1.1 gives degree-bounded differential-form representatives on smooth affine varieties over an algebraically closed field of characteristic zero; §3 describes component idempotents in degree-zero cohomology. | Useful for later explicit computations and extending the component calculation. The representatives are differential forms; this does not construct cycles for arbitrary Hodge classes or formalize the analytic comparison. |
| [Barz, *Logarithmic de Rham Stacks and Non-Abelian Hodge Theory*, 2512.04300v2](https://arxiv.org/html/2512.04300v2) | Theorems 1.9 and 1.16 concern logarithmic Cartier descent for smooth pairs with strict normal-crossing boundary in positive characteristic, and a torsor-twisted Higgs/connection correspondence for curves. | A later reference for logarithmic or characteristic-p work. These categorical correspondences do not supply the present characteristic-zero rational Chow–Betti comparison. |
| [Kreuzer–Long, *On the De Rham Cohomology of Zero-Dimensional Schemes*, 2609.34819v1](https://arxiv.org/html/2609.34819v1) | Definition 2.1, Example 3.2 and Proposition 4.4 concern the naive Kähler complex. Example 3.2 is a one-point nonreduced local complete intersection with three-dimensional `ker d`. Proposition 4.4 uses a Galois extension to reduce to rational support. | Immediate scope reference and source of future counterexamples. Naive cohomology for arbitrary nonreduced algebras need not match topology. The current formally unramified trace and finite split complex comparison retain their stated scope. |
| [Yuanning Zhang, *The stacky approach to de Rham–Witt cohomology*, 2610.28149v1](https://arxiv.org/html/2610.28149v1) | Theorem A (Theorems 3.38 and 4.10, Corollary 3.44), over a perfect field of characteristic p>0, gives a symmetric monoidal de Rham–Witt realization equivalence, restricting to perfect F-gauges and bounded coherent Raynaud-ring complexes with the completed star product. Corollary 3.46 identifies the realization of the F-gauge cohomology of a smooth proper scheme with its de Rham–Witt cohomology. | Relevant to a future p-adic/crystalline direction. F-gauges, the Raynaud ring and the completed product require additional infrastructure; this does not directly fill the current complex Betti or cycle-generation gap. Rechecked 2026-11-08; the existing record is retained here once. |

Status: **SOURCE INSPECTED / NOT FORMALIZED**. Prioritize the zero-dimensional
scope distinction and the effective affine reference. The two stack-theoretic
papers are retained for later work; no change of the main proof route follows.

The [polynomial/component implementation](working/0023-polynomial-derham-components.md)
now proves a bounded degree-zero case directly from Mathlib's Kähler and
polynomial APIs: adjoining a variable preserves the closed-function algebra
over additively torsion-free coefficients, and finite products of affine
lines have the component-idempotent basis. The papers' general component,
degree-bound and nonreduced-counterexample results retain the source-only
status above; none is supplied as a Lean premise.

### Affine de Rham construction and bounded trace (2026-11-05)

| Source-matched step | Exact source | Project proof and scope |
| --- | --- | --- |
| Affine differential and actual cochain complex | [Stacks 0FKF](https://stacks.math.columbia.edu/tag/0FKF) and the defining [equation 0FKG](https://stacks.math.columbia.edu/tag/0FKG) | `CommutativeAlgebra/DeRham/{Differential,Complex}.lean` adapts the construction, uniqueness and square-zero proofs from the pinned Axiom Stacks files. General base change and quotient descent are omitted. The existing Mathlib exterior powers and Kähler modules remain the terms. |
| Degree-zero algebra trace | [Stacks 0FLC, property (1)](https://stacks.math.columbia.edu/tag/0FLC); Mathlib `Algebra.trace_algebraMap_of_basis` | `Realization/DeRham/FiniteUnramifiedTrace.lean` uses the actual algebra trace when source and target are formally unramified over the base, so all functions are closed. A finite basis proves the degree law; the same affine map's geometric rank and computed cycle degree are identified. This trace construction does not supply a general map on forms or a scheme-hypercohomology trace. |
| Finite split Chow/de Rham/Betti squares | Direct comparison of existing finite split geometry and singular cohomology | `SplitComparison.lean` constructs cycle class from actual point coefficients and compares it to `ℂ ⊗[ℚ] H⁰_B`. Pullback, trace, intersection and reduced-point normalization are proved. This supplies no positive-dimensional analytic comparison or class-generation theorem. |
| Complex affine-line degree-zero comparison | Direct proof from Mathlib polynomial evaluation/topology, standard simplices and tensor products | `AffineLineComplexPoints`, `SingularPathConnected` and `AffineLineComparison` construct the actual topology, path-induced cocycle equality, genuine complexification and evaluation/multiplication/polynomial pullback squares. This is the bounded `H⁰` comparison for `ℂ[X]`, not a formalization of general analytic de Rham comparison or positive-codimension cycle classes. |

Status: **FORMAL IN THE STATED BOUNDED SCOPE**. The general upstream
finite-syntomic trace and concrete de Rham Weil theory remain external source
candidates. See [the checkpoint](working/0022-affine-derham-trace-comparison.md)
for the dependency experiment and the smaller integration choice.

### Finite flat Chow pullback and degree (2026-11-05)

| Source-matched step | Exact source | Project proof and scope |
| --- | --- | --- |
| Minimal-prime colength calculation | [Stacks, Lemma 42.3.2, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG), second assertion | `CommutativeAlgebra/Multiplicity/RestrictedDivisors.lean` retains the regular-element quotient case, with one-dimensional quotient. `FlatLocalMultiplicity.lean` combines it with actual flat local base change. Nilpotents remain in the minimal-prime localization lengths. The general Cohen–Macaulay-module case is not claimed. |
| Principal relations and quotient descent | [Stacks, Lemma 42.20.2, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1), relative dimension zero | `FiniteFlatPrincipalDivisor.lean` proves the actual component sum; `FiniteFiberClosedBaseChange.lean` proves the actual closed pushforward square. `FiniteFlatPrincipalRelations.lean` and `FiniteFlatChowPullback.lean` preserve the existing relation spans and descend the same integral/rational maps. Scope: finite flat maps between Noetherian schemes locally of finite type over a field. No ambient integrality, reducedness, or supplied relation-preservation premise is needed. |
| Rank, degree and positive-degree transfer | [Stacks, Lemma 42.15.2, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH), with direct quotient descent | `FiniteFlatRank.lean` identifies the independently computed fiber degree with Mathlib's geometric rank. `FiniteFlatChowDegree.lean` proves the integral/rational Chow degree law from constant rank. `Realization/Chow/FiniteFlatTransfer.lean` instantiates the existing transfer interface when the rank is positive. The maps and operator law are proved, not supplied as input fields. General Betti transfer and Hodge-class coverage remain open. |

Status: **FORMAL / SOURCE SCOPE MATCHED**. Proof adaptations use the pinned
Axiom Stacks snapshot; the [attribution inventory](../third_party/axiom-stacks/README.md)
records the selected source files and preserved license. Validation is in
[the finite flat checkpoint](working/0021-finite-flat-chow-transfer.md).

### Saito: higher Chow groups and open-boundary methods (2026-11-05)

[Morihiko Saito, *Hodge-type conjecture for higher Chow groups*, v5](https://arxiv.org/pdf/math/0201113).
Theorem 0.3 is conditional on projective Hodge algebraicity and Deligne-cycle-map
injectivity. Section 4 uses localization and boundary strata; §5 gives explicit
higher-Chow generators on certain hypersurface complements. Theorem 5.11 assumes
positive `p > n`, `2p - n < dim X`, normal-crossing ample hypersurfaces, and
codimension-`p-n` Hodge algebraicity on the compactification. Relevance to
`BoundaryCorrection.lean` is methodological. Our ordinary Chow groups, general
Betti/Gysin comparison, and prescribed-class generation remain separate obligations.
Status: **SOURCE VERIFIED / NOT FORMALIZED**.

### Analytic background suggested during review (2026-11-05)

The [Mathlog overview of Helmholtz/Hodge decomposition and Poincaré duality](https://mathlog.info/articles/z1zXpvRhX5GibVySPENM)
is background reading, not a source theorem used in Lean. Its displayed
Hodge decomposition reverses the input degrees, its Stokes formula reverses
the integral roles, and its quotient argument does not establish the claimed
specific direct-sum complement. For instance, $(1,0,0)$ is both
$\nabla x$ and $\nabla\times(0,0,y)$, so the claimed unrestricted direct
sum on all smooth vector fields on $\mathbb R^3$ has a nonzero intersection.
For the analytic statement use [Calegari, Theorem 2.3](https://math.uchicago.edu/~dannyc/courses/4manifolds_2018/4_manifolds_notes.pdf):
on a closed oriented Riemannian manifold,
$\Omega^k=d\Omega^{k-1}\oplus\delta\Omega^{k+1}\oplus\mathcal H^k$.
[Deligne, §1](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf)
then distinguishes the Kähler $(p,q)$ decomposition and rational Hodge classes
from the further algebraicity assertion. None supplies the missing general
Chow-to-Betti comparison or class-coverage construction in this repository.

### Axiom Stacks implementation survey (2026-11-04)

The [pinned AxiomMath/Stacks release](https://github.com/AxiomMath/Stacks/tree/f8e70c5dd04bfabcb423d5e325461f527c85a5d6)
contains source proofs of general flat Chow pullback (02S1), the finite locally
free cycle degree formula with its fiber-degree premise discharged (02RH),
and fixed-inertia local étaleness (0BST; separately 09EH in the DVR setting).
[The reuse audit](working/0019-axiom-stacks-reuse-audit.md) records exact
declarations, matches to existing interfaces, overlap, and import costs.
The audit used this repository's former Lean 4.24 baseline; the current
Lean 4.35 migration is recorded [separately](working/0020-lean-4-35-migration.md).
The bounded fiber-residue comparison is now adapted and compiled, with
Apache-2.0 attribution in `third_party/axiom-stacks/`. The actual finite-fiber
cycle map and computed degree formula are proved on this library's existing
objects. The upstream general Chow pullback and inertia results remain
**EXTERNAL SOURCE INSPECTED / NOT PORTED HERE**. In particular,
the current fixed-inertia input remains open in this library, and no general
Chow--Betti or Hodge realization is obtained from the surveyed Weil interfaces.

### Finite cycle/Chow pushforward functoriality (SP113, 2026-10-27)

[Stacks Lemma 42.12.2, 02R5](https://stacks.math.columbia.edu/tag/02R5)
states functoriality of proper cycle pushforward. The new
`Cycles/FinitePushforwardComposition.lean` proves its finite-map case
directly: `Scheme.residueFieldMap_comp` identifies the literal scalar tower,
Mathlib's `Module.finrank_mul_finrank` gives the degree product, and
`Scheme.IdealSheafData.map_comp` identifies the original image carrier.
Finite maps preserve the existing canonical grading by SP102, so the
dimension-dropping branch of general proper pushforward does not occur.
Raw finite-cycle functoriality works over any semiring without a base-field
or Noetherian hypothesis. Arbitrary dimension functions still require the
existing compatibility premises on the graded maps.

`Cycles/FiniteChowPushforwardComposition.lean` inherits composition and
identity on the existing integral/rational quotients. Relation preservation
uses SP107's finite specialization of
[Stacks 02RT](https://stacks.math.columbia.edu/tag/02RT), already proved with
actual image-carrier norms. The Chow theorems retain Noetherian ambient
schemes and a target locally of finite type over a field. No literature
conclusion is imported as an axiom or supplied functoriality premise.

### Chern-character trial (SP112, 2026-10-14)

- [Stacks 0ESY](https://stacks.math.columbia.edu/tag/0ESY), the defining
  alternating-sum formula and Lemma 42.46.7: additivity permits rational
  virtual complexes. The Chern map and its Betti comparison are not built.
- [Stacks Lemma 36.13.2, 08EC](https://stacks.math.columbia.edu/tag/08EC)
  extends bounded coherent complexes from an open of a Noetherian scheme;
  [Lemma 36.11.8, 08E0](https://stacks.math.columbia.edu/tag/08E0) makes the
  extension perfect when the ambient scheme is regular. This supplies a
  classical Chow lift after Chern realization, not a construction of the
  prescribed open object. No source axiom is added to Lean.
- [Stacks 03SF](https://stacks.math.columbia.edu/tag/03SF), finite étale
  Galois refinement, and [02UM](https://stacks.math.columbia.edu/tag/02UM),
  Chern normalization, give zero after splitting pullback for the tested
  finite-monodromy bundles. [02RH](https://stacks.math.columbia.edu/tag/02RH)
  gives the degree identity on cycles, hence on Chow. Rational cancellation
  yields the vanishing on the original open. Only this last linear step is
  formalized by `RationalDegreeTransfer.pull_injective` and `pull_eq_zero_iff`;
  their degree law remains an explicit premise.
- [Stacks 0FB0](https://stacks.math.columbia.edu/tag/0FB0), Definition
  42.50.3 and its pushforward identity: a perfect complex acyclic off the
  boundary has a localized Chern character there. It supplies a boundary
  class, not the required nonzero restriction to the open. This is a
  classical candidate connection, not a formal localized-Chern construction.

### Supported-class extraction (SP111, 2026-10-13)

[Voisin, sections 4.1--4.2](https://webusers.imj-prg.fr/~claire.voisin/Articlesweb/JOMP_V01N01P02Paper.pdf),
Definition 4.1 and the explanation after Conjecture 4.6, relate restriction
vanishing, supported cohomology and component cycle classes. The geometric
specialization is smooth projective complex $X$, degree $2p$, and closed
support of codimension at least $p$.

`Realization/Chow/SupportedClass.lean` proves the finite expansion and
extraction consumer directly, and cites this source in its module docs.
Its `hExact`, basis `b` and `hBasis` remain supplied: general Betti
localization, the top-component basis and its cycle-class comparison are
not formalized. `hRestrict` is the open cycle-class comparison for the
converse. Actual complementary scheme maps prove cycle support via SP110.
There is no imported source axiom or asserted support-existence theorem.

### Smooth ample boundary and open representative (2026-10-13)

This is a source-backed mathematical check in
[TARGET_BRIDGE.md](TARGET_BRIDGE.md#open-representative-the-smooth-ample-boundary-calculation),
not a formal implementation or an imported Lean premise.

| Statement used | Exact source and specialization | Lean relationship / status |
| --- | --- | --- |
| Zero open representative above the affine dimension bound | [Voisin, Hodge Theory and Complex Algebraic Geometry II, Theorem 1.2](https://assets.cambridge.org/97805218/02833/sample/9780521802833ws.pdf): smooth affine complex $d$-folds have CW homotopy dimension at most $d$. Apply to the complement of a smooth ample divisor and degree $2p>d$. | Classical construction $z_U=0$; the required geometric vanishing and general open Betti cycle class are not implemented. |
| Kernel of restriction to a smooth ample complement | [Voisin, II, Theorem 1.1 and equation (1.6)](https://assets.cambridge.org/97805218/02833/sample/9780521802833ws.pdf) give weak Lefschetz and $i_*i^*=[D]\cup-$. For $2p\leq d$, combine with the separately stated localization/Thom sequence to deduce $\ker j^*=L H^{2p-2}(Y)$. | Mathematical deduction; not supplied by actual Chow exactness. The existing SP108 `restrictH` and `pushH` remain explicit geometric inputs. |
| Primitive classes survive this restriction | [Deligne, §4, Example 2](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf) recalls hard Lefschetz. Its direct-sum consequence separates $P_h^{2p}=\ker L^{d-2p+1}$ from $L H^{2p-2}$; the kernel calculation then gives injectivity on $P_h^{2p}$. | Mathematical deduction, not an algebraic projector construction. The finite-cover extension additionally uses positive-degree transfer and cup-product functoriality, whose general geometric instances are not formalized here. |

The remaining prescribed-class existence is not a conclusion of these
sources. SP108 plus restriction proves a conditional equivalence with
ambient algebraicity; this is a scope check on the proposed construction.

### Actual Chow localization (SP110, 2026-10-13)

[Stacks Lemma 42.19.3, 02RX](https://stacks.math.columbia.edu/tag/02RX)
gives the localization sequence for the reduced closed complement of an
open subscheme. `OpenClosedLocalization.lean`, `PrincipalRelationLifting.lean`
and `ChowLocalization.lean` prove its support, relation-lifting and quotient
steps directly. Each module cites the exact tag. The scheme input here is
a Noetherian ambient scheme with a supplied dimension function; hence the
existing finite-sum cycle convention applies. The carrier/function lifting
and semiring-valued cycle exactness need no ambient finiteness. Rational
exactness uses the same principal generators and coefficient compatibility.
The old `ChowLocalizationHypotheses` is now proved by `ofOpenComplement`
for these actual maps; arbitrary supplied maps still require their own
instance. No cohomological localization theorem is imported by this result.

### Marked cycle-to-Chow map (SP109, 2026-10-13)

`Realization/Chow/MarkedCycleMap.lean` constructs a linear combination of
supplied actual homogeneous cycles and applies the existing rational Chow
quotient. Its image and marked-vector formula follow directly by finite
linear algebra. There is no external theorem asserting that such a family
represents an arbitrary Hodge class.

Its finite-pushforward comparison uses the already proved degree-weighted
map of [Stacks Definition 42.12.1, 02R4](https://stacks.math.columbia.edu/tag/02R4)
and the finite specialization of principal/norm compatibility in
[Stacks Lemma 42.18.1, 02RT](https://stacks.math.columbia.edu/tag/02RT).
Both exact tags are cited in the Lean module. The comparison assumes
Noetherian ambient schemes, a finite morphism and a target locally of
finite type over a field, with the canonical field dimension functions.
It uses SP107's proved relation preservation, not an imported premise.
Open compatibility similarly uses the existing actual Chow restriction.
The supplied realization map in the class formula is not asserted to be
a constructed geometric Betti map.

### Geometric candidates and conditional boundary induction (2026-10-13)

These sources support the mathematical investigation in `TARGET_BRIDGE.md`
and the current proof-role/notation registry. SP108 proves its conditional
correction consumer in `Realization/Chow/BoundaryCorrection.lean`, with no
new input record or geometric Betti instance.

| Statement used | Exact source and specialization | Lean relationship / status |
| --- | --- | --- |
| An open Chow class admits an ambient lift | [Stacks Lemma 42.19.3, 02RX](https://stacks.math.columbia.edu/tag/02RX), specifically surjectivity of $CH_k(Y)\to CH_k(U)$ for an open subscheme; rational coefficients follow by scalar extension. | `BoundaryCorrection.isAlgebraicHodgeClass_of_schemeOpenRestriction` uses the already proved `rationalChowOpenRestriction_surjective` and actual closed Chow pushforward. It does not import full localization exactness as a premise. |
| Regular zero loci have the fixed top Chern class | [Stacks Lemma 42.44.1, 0FA9](https://stacks.math.columbia.edu/tag/0FA9), specialized to a rank-$p$ algebraic bundle on smooth $X$ with a regular section whose zero locus has codimension $p$: $[Z(s)]=c_p(E)\cap[X]$. | Research check on a proposed cycle construction; no class-dependent bundle or general Chern-cycle implementation is asserted. |
| Chern-class expressions do not bypass the algebraicity question | [Deligne, The Hodge Conjecture, §2(ii)](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf): on smooth projective complex $X$, algebraic cycle classes are generated by products of Chern classes of algebraic bundles. Only the rational-coefficient consequence is used. | Explains why an assumed algebraic-bundle expression for an arbitrary Hodge class is not the missing construction. |
| Supported cohomological discrepancy has a lower-codimension Hodge lift for a smooth divisor | [de Cataldo--Migliorini, §2 and Theorem 4.1](https://arxiv.org/pdf/math/0504560) supply relative-cohomology functoriality and Hodge compatibility of Gysin maps. For smooth projective $Y$, smooth divisor $i:D\hookrightarrow Y$ and $U=Y\setminus D$, use the ordinary localization/Thom sequence $H^{2p-2}(D)(-1)\to H^{2p}(Y)\to H^{2p}(U)$. **Deduction:** a polarization-orthogonal complement to the kernel of $i_*$ gives a rational Hodge lift of a Hodge class in its image. | Explicit `hBoundaryLift` premise of `BoundaryCorrection.exists_boundary_correction` and its open-restriction consumers; the geometric deduction is not yet instantiated in Lean. This is distinct from Chow localization. The correction additionally requires `RationalHodgeConjectureAt MD`, supplied by a known case or the induction hypothesis in codimension $p-1$, and cycle-class compatibility with closed pushforward. |
| Divisor Hodge classes supply the codimension-one case | [Deligne, §2(iii)](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf), Lefschetz $(1,1)$ on smooth projective complex varieties. | Classical input for the proposed induction; no general Lean implementation of Lefschetz $(1,1)$ or of the induction is claimed. |

The open-locus representative and the boundary hypotheses must be proved
for the chosen construction. A singular boundary is not silently treated
as a smooth divisor. The existing separable function-field splitting and
marked algebra decomposition do not supply this Hodge lift or a parameter
space containing cycles of the prescribed class.

### Finite scheme norm identity and Chow descent (SP107, 2026-10-08)

[Stacks 02RT](https://stacks.math.columbia.edu/tag/02RT) is specialized to
finite dominant maps of integral schemes locally of finite type over a
field. `finitePushforward_principalDivisor` also explicitly requires local
Noetherianity and quasi-compactness, as needed by the existing finite-cycle
principal divisors. The source's equal dimension condition is derived
from the canonical field grading and the existing integral codimension
formula. The proof does not claim the source's general proper case.

The finite affine inverse-image ring is localized over the target chart
prime. `finiteAffineFiberEquiv`, `finiteAffineFiber_stalkEquiv` and
`finiteAffineFiber_localOrder` identify its maximal ideals, local rings
and orders with the original scheme fiber and stalks. The embeddings use
the original generic-stalk function fields. `finiteAffineFiber_residueDegree`
and `finitePushforwardDegree_eq_residueFieldDegree` identify the two
weight conventions. `divisorOrder_norm_eq_sum_fiber` is then the geometric
coefficient form of [02MJ](https://stacks.math.columbia.edu/tag/02MJ).
The already proved finite-type codimension comparison handles support
away from codimension one. No normality, freeness or separability is added.

The actual carrier-to-image map is finite and dominant. Its norm supplies
`PrincipalRelationData.finiteImage`, and the proved commuting square with
closed carrier inclusions identifies the ambient divisors. Span
preservation and quotient descent are proved consequences, not literature
premises. The integral and rational Chow maps use the existing canonical
field grading on Noetherian ambient schemes; no ambient integrality or
dominance is needed. The 02RT and 02MJ URLs are cited in the Lean module
documentation. The semantic registry gives separate LaTeX and Lean names
for the objects and comparisons.

### Full weighted norm--order formula (SP106, 2026-10-08)

`Cycles/LocalOrderNormFormula.lean` proves
[Stacks Lemma 10.121.8, 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
as `localOrder_norm_eq_sum`. Source `A`, `B`, `K`, `L`, `y` correspond to
Lean `R`, `B`, `K`, `L`, `y : Lˣ`. The base is Noetherian, local and a
domain; `B` is a domain finite as an `R`-module. The two fraction-field
structures and compatible towers express the same inclusions. Their
compatibility implies injectivity of `R → B`; the existing lattice proof
derives finite dimensionality of `L/K`. No normality, freeness or
separability is added. The Lean dimension bound is at most one, extending
the source's dimension-one statement to the field case.

`CommutativeAlgebra/FiniteSemilocal.lean` derives the source's semilocal
and finite-residue hypotheses: integrality contracts every upstairs
maximal ideal to the base maximal ideal, and the finite residue algebra
`B/mB` is Artinian. Its maximal spectrum is finite by
[Stacks Lemma 10.53.3, 00J7](https://stacks.math.columbia.edu/tag/00J7),
as formalized in Mathlib. This direct finite-algebra argument replaces
the more general dimension-formula lemma 02MA used in the source proof.
The upstairs dimension bound follows by contracting nonzero primes and
using integrality to reflect maximality. Noetherianity follows from
module-finiteness. Scoped canonical localization maps in
`CommutativeAlgebra/AtPrimeFractionField.lean` retain the original `L`.

For `y=a/b`, the proof combines SP104's actual norm/quotient-length sum
with SP105's local-order comparison, then uses additivity of orders and
multiplicativity of the norm. All residue degrees are computed with the
canonical quotient-field algebra, and `∑ᶠ` is converted to the finite sum
only after proving finiteness. At SP106 the scheme-level divisor identity 02RT was not yet claimed;
SP107 above proves its finite specialization. Both source URLs are cited
in the Lean module docs.

### Localized principal quotients (SP105, 2026-10-08)

The precise comparison is the principal-ideal specialization of
[Stacks Lemma 10.9.13, 02C8](https://stacks.math.columbia.edu/tag/02C8):
localization commutes with module quotients. The Lean construction uses
Mathlib's `IsLocalizedModule.toLocalizedQuotient'`, the uniqueness of
localized modules, and `Submodule.localized'_span`. Its isomorphism is
linear over the actual `Localization S` and sends `[x]/s` to `[x/s]`.
The length equality therefore concerns the existing semilocal summands,
without a new quotient or localization carrier. No domain, Noetherianity,
normality or nonvanishing hypothesis is needed for this comparison.

`Cycles/LocalOrderLocalization.lean` applies the comparison at a prime of
a Noetherian domain of dimension at most one. It derives the localization's
dimension bound from its height and derives its fraction-field property
through the supplied compatible scalar tower. The existing
`localOrder_algebraMap` and `localOrder_div` give the integral and signed
fraction formulas. This formalizes the termwise identification in the proof
of [Stacks 02MJ](https://stacks.math.columbia.edu/tag/02MJ), retaining the
original fraction field. At SP105, deriving all semilocal and scalar-tower
data and assembling the complete source statement remained; SP106 above
completes those steps.

### Semilocal lengths and determinant/norm comparison (SP104, 2026-10-08)

`CommutativeAlgebra/SemilocalLength.lean` directly proves
[Stacks Lemma 10.52.12, 02M0](https://stacks.math.columbia.edu/tag/02M0):
the base is local, the upstairs ring has finitely many maximal ideals all
over the base maximal ideal, their residue extensions are finite, and the
upstairs module has finite length. The conclusion is the residue-degree
sum of actual localized lengths, with finiteness over the base. The more
general intermediate theorem uses the base lengths of the residue fields
as weights. Exactness of localization and induction on finite length are
proved/used explicitly. The residue actions are the canonical quotient
actions, not separately supplied field structures.

`CommutativeAlgebra/LatticeIndex.lean` and `Cycles/LocalOrderDeterminant.lean`
directly prove the relative-lattice-length comparison of
[Stacks Lemma 10.121.7, 02MI](https://stacks.math.columbia.edu/tag/02MI).
The Lean result works over a Noetherian domain of dimension at most one,
with its fraction field, a finite-dimensional vector space and an actual
`Submodule.IsLattice`. The source assumes locality and dimension exactly
one; neither extra restriction is needed for the existing length-based
order used here. The proof follows lattice independence, additivity and
generation by diagonal matrices and transvections. Transvections are
handled by conjugating them to their inverses, an alternative to the
source's change to an integral elementary matrix.

`Cycles/LocalOrderNorm.lean` proves the determinant/norm step in the proof
of [Stacks Lemma 10.121.8, 02MJ](https://stacks.math.columbia.edu/tag/02MJ).
For a finite extension of domains with compatible fraction-field towers,
the image of the finite algebra is proved to be a lattice, finite
dimensionality is derived, and multiplication has determinant equal to
the actual `Algebra.norm`. This gives the order as the base length of the
principal quotient and gives a signed fraction formula. The final theorem
combines 02M0 with this result to obtain weighted localized quotient lengths.
It still takes the semilocal/lying-over/residue-finiteness hypotheses
explicitly. At SP104 the localized-quotient identification, their automatic
instantiation for a finite local-base extension, and the full 02MJ endpoint
remain to be assembled. The geometric law 02RT is not claimed here.

### Local residue-degree length comparison (SP103, 2026-10-07)

`CommutativeAlgebra/LocalLength.lean` directly proves the local-ring case
of [Stacks Lemma 10.52.12, 02M0](https://stacks.math.columbia.edu/tag/02M0).
The hypotheses are a local homomorphism of commutative local rings, finite
residue-field extension and finite length of the upstairs module. The
conclusion is multiplication of length by that actual residue degree,
including finiteness over the base. The proof is induction on finite length.
Its residue-field calculation is the specialization of
[Stacks Lemma 10.52.6, 00IY](https://stacks.math.columbia.edu/tag/00IY) to
`M = κ(B)`, proved using a basis and length additivity.

`Cycles/LocalOrderLength.lean` specializes these results to the existing
principal quotients for a Noetherian domain `B` of dimension at most one,
and then to differences of lengths for fractions. It retains `localOrder`.
All statements are proved in Lean, without source propositions as premises.

At SP103 this did not formalize the semilocal localization sum of 02M0 or the
lattice/determinant comparison of
[Stacks Lemma 10.121.7, 02MI](https://stacks.math.columbia.edu/tag/02MI).
Those were the two inputs to the pending norm-order identity 02MJ and
geometric pushforward identity 02RT. No freeness or normality assumption
has been substituted for those obligations.

### Canonical finite-map grading (SP102, 2026-09-29)

The affine input is Mathlib's existing prime-residue algebraicity instance
in `RingTheory/LocalRing/ResidueField/Instances.lean`, for an integral
coordinate algebra. `specResidueFieldEquiv` and its evaluation formula
identify the affine scalar map; residue-map naturality and actual chart
isomorphisms transport it to `f.residueFieldMap x`. Finiteness of `f`
supplies an integral coordinate algebra on the entire affine preimage.
No stalk-finiteness or stalk-integrality inference is used.

The two structural base actions are the existing `residueFieldBaseAlgebra`
definitions. `residueFieldBaseMap_comp` gives their actual scalar tower;
`trdeg_add_eq` and `trdeg_eq_zero` give the full cardinal
equality before conversion to the integer dimension values. The tower law
reuses the existing bibliography entry `StacksTranscendenceDegreeTower`,
[Lemma 9.26.5, 030H](https://stacks.math.columbia.edu/tag/030H), checked at
this checkpoint. No new commutative-algebra proof or bibliography item is
introduced. Canonical support-degree equality then invokes SP101's
existing homogeneous-cycle preservation theorem, not a replacement map.

Five public theorems correspond to `prop:finite-field-grading`. No source
axiom, literature hypothesis or new global instance is introduced. The
principal/norm identity of 02RT and actual Chow descent remain separate;
this checkpoint only discharges their canonical grading prerequisite.

The next local source is
[Stacks Lemma 10.121.8, 02MJ](https://stacks.math.columbia.edu/tag/02MJ),
checked against its stated hypotheses: `A` is a one-dimensional Noetherian
local domain and `A ⊂ B` is a finite extension of domains. For their fraction
fields `K ⊂ L` and `u ∈ Lˣ`, the norm order is the sum of the local orders at maximal
ideals of `B`, weighted by their residue degrees. Neither normality,
freeness nor separability is a premise. This is a pending local input to
02RT, not a theorem proved at SP102. The existing `Algebra.norm` and
`Units.map` provide the operation; the pinned `Algebra.norm_localization`
requires a free module and does not by itself discharge this general law.

All five public declarations pass the actual standard-three axiom audit,
each observed set exactly `propext`, `Classical.choice` and `Quot.sound`.
Both scoped builds, the focused suite, full build, endpoint dependency
audit and fresh SP101 regression pass. Independent source/scope review,
five-API Lean--TeX parity and historical preservation checks pass. No full
historical central replay or additional fresh neighbor-suite run is claimed.

### Degree-weighted finite cycle pushforward (SP101, 2026-09-29)

The cycle formula reuses the existing bibliography input
[Stacks Definition 42.12.1, 02R4](https://stacks.math.columbia.edu/tag/02R4).
The source treats proper maps in its base-induced dimension-function and
locally finite cycle setting. The new direct Lean construction covers finite
maps and finite sums on existing integral closed supports; restriction to
the existing homogeneous submodules retains an explicit degree-compatibility
hypothesis. It does not claim the full proper-map or canonical-grading theorem.

Image integrality reuses `pointSupport_ambientGenericPoint`,
`IdealSheafData.map_vanishingIdeal` and `closure_image_closure`; the image
ideal is literally the old mapped ideal. Finiteness of the actual `toImage`
uses `isFinite_of_comp_of_isSeparated`; positivity of its field degree uses
`functionFieldMapOfDominant_finiteDimensional`. Closed-immersion agreement
uses the existing actual function-field isomorphism. Linear extension,
supported-submodule restriction and coefficient cast use Mathlib's existing
Finsupp and module APIs. No new commutative-algebra theorem, source axiom,
bibliography entry or hypothesis package is introduced.

The next geometric generator law is precisely the finite specialization of
[Stacks Lemma 42.18.1, 02RT](https://stacks.math.columbia.edu/tag/02RT):
proper dominant integral equal-dimension maps send a principal divisor to
the divisor of the actual function-field norm. Its local proof uses general
Noetherian length-orders. The current ambient smooth/etale setting does not
make all integral relation carriers normal; a DVR-only law is insufficient.
That law and canonical grading compatibility are recorded obligations, not
assumptions silently consumed by SP101. Quotient preservation remains the
later [02S2](https://stacks.math.columbia.edu/tag/02S2) consumer.

All twenty public declarations pass the actual standard-three axiom audit,
each observed set exactly `propext`, `Classical.choice` and `Quot.sound`.
The raw/graded scoped builds, corrected focused suite, full build, endpoint
dependency audit and fresh SP72/SP88 regressions pass. Independent scope
review and twenty-API Lean--TeX parity pass. No full historical central
replay or additional neighbor-suite rerun is claimed.

### Sheet points and the original normalization action (SP100, 2026-09-29)

No new literature premise, bibliography entry or source axiom is introduced.
The two evaluation formulas compose SP99's original projections with
Mathlib's existing `Pi.evalAlgHom`. The original fixing subgroup controls
the chosen representative, giving `D.sheetEmbedding(gH)=g ∘ D.embedding`.
The orbit comparison reuses `functionFieldMapOfDominant_fromSpecStalk`,
`gluedNormalizationFunctionFieldEquiv_automorphism` and
`gluedNormalClosureFunctionFieldEquiv_toCover`. The old inverse-pullback
formula accounts for `g⁻¹` on the scheme side. The pullback universal
property gives the full point identity.

Four public theorems in `GenericSplitFiberAction.lean` correspond to
`prop:split-fiber-sheet-action`. Finite dominance and integrality suffice
for the original field package. Normal stalks of `Y` supply the original
marked refinement; formal unramifiedness is used for the already proved
split-fiber comparison, not for the orbit identity into `Y` alone.
No new spectrum/coproduct presentation, action or evaluator is constructed.

All four declarations pass the actual standard-three axiom audit, with
each observed set exactly `propext`, `Classical.choice` and `Quot.sound`.
Scoped and full builds, the corrected focused suite, the unchanged endpoint
dependency audit, fresh SP99/SP93 regressions and four-API Lean--TeX parity
pass. SP99's separability dependency-direction checks also pass. No full
historical central replay or additional neighbor-suite rerun is claimed.

### Marked split generic fiber (SP99, 2026-09-29)

No new literature premise, bibliography entry or source axiom is introduced.
The original `functionFieldNormalClosureData` and the proved
`functionFieldMapOfDominant_isSeparable` supply the existing
`normalClosureTensorGenericSheetsEquiv`. Apply `Scheme.Spec.mapIso` to that
equivalence, then compose with SP98's `IsPullback.isoPullback`.
Functoriality and the existing tensor evaluation formulas give both
projections. The marked-point proof uses the existing
`NormalClosureData.sheetEmbedding_baseSheet`, these projection laws and
`pullback.hom_ext`. This is the scheme-level form of the existing
`normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv`
square; the manuscript can apply that square directly. No algebraic
splitting or augmentation theorem is reproved.

Four public APIs in `GenericSplitFiber.lean` correspond to
`prop:marked-split-generic-fiber`. Formal unramifiedness is used to derive
separability of the actual finite extension, not assumed as an additional
field input. No normalization, splitting, evaluator or Galois datum is
constructed a second time; no normal-stalk or Noetherian input is needed.

All four declarations pass the actual standard-three axiom audit; each
observed set is exactly `propext`, `Classical.choice` and `Quot.sound`.
Scoped and full builds, the corrected focused suite, two transitive
dependency-direction checks, the unchanged endpoint dependency audit,
fresh SP98/separability regressions and four-API Lean--TeX parity pass.
No historical central replay or additional neighbor-suite rerun is claimed.

### Tensor base change of the actual generic fiber (SP98, 2026-09-29)

No new literature premise, bibliography entry or source axiom is introduced.
The tensor pushout is Mathlib's `CommRingCat.isPushout_tensorProduct`;
`isPullback_Spec_map_isPushout` gives its spectrum square. Flipping that
square and applying `IsPullback.paste_horiz` to SP97 gives the actual
base-change square. The standard `IsPullback.isoPullback` interface
provides the canonical isomorphism and its projection identities.

The single public theorem is
`functionFieldMapOfDominant_baseChange_isPullback`; its manuscript
counterpart is `cor:generic-fiber-base-change`. The original scalar map
on `K(Y)`, tensor order and generic-stalk maps are retained. Only a
commutative `K(X)`-algebra structure is needed on `E`, not a field,
finite extension or separable algebra. Finite dominance and integrality
belong to `p` and its source/target through SP97, not to `E`.
The proof imports no splitting, marked-point, torsor or Hodge-generation
comparison. There is no new public carrier or isomorphism wrapper.

The declaration passes the actual standard-three axiom audit, with observed
set exactly `propext`, `Classical.choice` and `Quot.sound`. Scoped and full
builds, the corrected focused suite, the unchanged dependency audit, a fresh
SP97 regression and the one-API Lean--TeX parity check pass. No historical
central replay or additional neighbor-suite rerun is claimed.

### Actual generic fiber and affine function-field pushout (SP97, 2026-09-21)

No new literature premise, bibliography entry or source axiom is introduced.
`functionFieldMapOfDominant_isPushout_of_affine` reuses the actual section
scalar tower, finite affine-preimage algebra and fraction-field instances.
The faithful scalar action follows from the injective actual generic
embedding. Mathlib's fraction-field pushout instance in
`RingTheory/Algebraic/Integral.lean` then proves `Algebra.IsPushout`.
Both scalar towers in the statement are locally constructed proofs,
not additional hypotheses supplied by a caller.

`functionFieldMapOfDominant_isPullback` uses
`CommRingCat.isPushout_of_isPushout` and
`isPullback_Spec_map_isPushout`. The original affine chart isomorphisms
transport `isPullback_morphismRestrict`; vertical composition and
`IsAffineOpen.fromSpecStalk_eq_fromSpecStalk` identify the actual outer
maps. Thus finite dominance and integrality suffice for the actual
generic-fiber square, without normality, separability or etaleness.
The canonical isomorphism uses the existing `IsPullback.isoPullback`
interface; no new geometric comparison is imported as a hypothesis.

The two public APIs correspond to `prop:actual-generic-fiber` in the
manuscript. Generic points `η_X` and their scheme morphisms `ι_{η_X}`
have distinct notation, also in the existing generic-extensionality proof.
No split-fiber/coset or arbitrary-geometric-fiber statement, torsor, or
cycle-generation conclusion is attributed to these inputs.

Both new declarations pass the actual standard-three axiom audit, each
set exactly `propext`, `Classical.choice` and `Quot.sound`. Scoped and
full builds, the unchanged dependency audit, fresh finite-function-field
and SP96 regressions, and both API parity checks pass. No historical
central replay or other neighbor-suite rerun is claimed.

### Full marked stabilizer and marked deck-group equivalence (SP96, 2026-09-20)

No new literature input, bibliography entry or source axiom is introduced.
The converse to SP90's subgroup inclusion uses the proved contravariant
composition of actual function-field maps, SP93's inverse-action and
marked-embedding comparisons, and
`IntermediateField.mem_fixingSubgroup_iff` on the original embedding's
field range. This is pointwise subgroup membership; no Galois fixed-field
correspondence or separability premise is used.

The other direction reuses `gluedNormalizationAutomorphism_comp_toCover`.
For arbitrary deck maps, SP95's reconstruction supplies the field
automorphism. The original refinement triangle lets an automorphism over
`Y` be viewed over `X`; subgroup membership and reconstruction then give
the full marked action equivalence. The promotion is private, while the
public inverse formula is the actual inverse-deck pullback through the
same field marking. Six public APIs correspond to manuscript theorem
`thm:normalization-marked-stabilizer`, with finite dominance, integral
source/target and normal stalks of `Y` only. No source is cited for a
geometric-fiber, torsor or Hodge-generation conclusion here.

The six new declarations pass the focused standard-three axiom audit;
each observed set is exactly `propext`, `Classical.choice` and `Quot.sound`.
The scoped and full builds, unchanged dependency audit, fresh SP95
regression and six-API Lean--TeX parity checks pass. No historical central
verification replay or additional neighbor regression is claimed.

### Generic extensionality and full deck-group comparison (SP95, 2026-09-20)

No new literature premise, bibliography entry or source axiom is added.
The new generic-stalk square uses Mathlib's
`Scheme.Spec_map_stalkMap_fromSpecStalk` and
`Scheme.Spec_map_stalkSpecializes_fromSpecStalk` on the actual pullback.
`ext_of_isDominant_of_isSeparated` then applies to the generic-stalk
inclusion: its image contains the generic point, hence it is dominant.
The reduced source and relative separatedness are explicit mathematical
hypotheses, derived from existing integrality and affineness for the
normalization application.

SP93's finite-extension field comparison is reused without a replacement
field. Pullback along `d⁻¹` preserves the original base embedding because
`d` is over `X`; conjugation by `e_N` therefore defines a genuine
`K(X)`-algebra automorphism. The existing inverse-action formula and the
new extensionality prove reconstruction, surjectivity and the full group
equivalence. These are kernel-proved consequences, not imported deck-group
or torsor assertions. Eight public APIs match manuscript statements
`lem:generic-pullback-extensionality` and
`thm:normalization-full-deck-group`. Source scope for the earlier
integral-closure localization citation is unchanged.

Validation passes the two scoped builds, 27 focused examples and all
eight standard-three axiom audits, the 3224-job full build, the unchanged
six-primary/two-support dependency audit and a fresh SP94 regression
(26 examples, seven axiom reports, two dependency assertions). The
92-page PDF is rebuilt and visually checked. Exact validation and
preserved-history scope is recorded under A11ca in
[the claim ledger](CLAIM_LEDGER.md).

### Arbitrary-class generation and normalized descent (SP94, 2026-09-20)

No new literature premise, bibliography entry or source axiom is introduced.
The seven public APIs in `Realization/Chow/UpstairsGeneration.lean` give
a conditional rational-linear argument using the already existing
`RationalDegreeTransfer` data. Positive degree and the cohomological
push-pull identity are fields of the explicitly supplied transfer;
the Chow/cycle-class pushforward comparison and recipe-generation
condition are explicit proposition parameters.

The kernel-checked calculation sends an upstairs cycle representing
`pull_i α` to `degree_i⁻¹ • pushCH_i z`, whose downstairs cycle class is
`α`. No citation is used to supply the generation premise. No statement
about algebraic-cycle degrees alone is treated as a proof of the Betti
transfer identity. The actual geometric maps must later refer to the
same cover and discharge both displayed laws. Manuscript statements
`def:upstairs-generation` and `thm:upstairs-generation-descent` use the
same explicit maps and hypotheses.

Validation passes the scoped build, 26 focused examples, seven
standard-three axiom audits, two direct-descent dependency checks, the
3222-job full build and the unchanged six-primary/two-support dependency
regression. The single 92-page PDF is rebuilt and visually checked.
Detailed counts and preserved-history guards are recorded under
A11bz in [the claim ledger](CLAIM_LEDGER.md). No new geometric source
input has been discharged by these conditional calculations.

### Marked function-field comparison and action faithfulness (SP93, 2026-09-20)

The existing citation [Stacks, Lemma 10.36.11, Tag
0307](https://stacks.math.columbia.edu/tag/0307), with bibliography key
`StacksIntegralClosureLocalization`, supports the fraction-field
reduction only: integral closure commutes with localization, and a
finite ambient extension of the base fraction field is algebraic.
Consequently the original integral-closure chart has the ambient field
as its fraction field. This citation is not a source for the chart
gluing, action faithfulness, or a full deck-group or fiber comparison.
The primary page was rechecked live for SP93. The manuscript reuses
this existing bibliography entry; no new literature premise is introduced.

Lean uses `integralClosure.isFractionRing_of_finite_extension` and
`IsLocalization.algEquiv` on the original coordinate rings, followed
by actual open-immersion generic-stalk maps. Generic `Spec.map` and
affine-chart germ formulas identify the ring coordinates under pullback;
fraction-field uniqueness and actual chart squares yield chart
independence, preservation of the base map and the inverse-pullback
action formula. Faithfulness follows from surjectivity of the field
equivalence, without importing a deck-group reconstruction theorem.
The checkpoint has 19 public APIs across four production modules.

The marked theorem cancels the existing canonical affine-preimage
normalization isomorphism and retains exactly `D.embedding` through
the defining integral-coordinate formula of `normalizationMap`.
Finite dominance, integral `X/Y` and normal
stalks of `Y` suffice; no normality of `X`, etaleness, separability or
Noetherianity is added. The manuscript counterparts are
`prop:normalization-function-field-comparison` and
`cor:normalization-marked-function-field`. No source axiom is introduced.

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

Next address reconstruction of arbitrary deck transformations and full
deck-group comparison; fibers, torsors, normal stalks from smooth geometry
and Chow--Betti generation remain separate.

### Integrality of the original glued normalization (SP92, 2026-09-20)

[Stacks, Lemma 28.3.3, Tag 01OM](https://stacks.math.columbia.edu/tag/01OM)
gives the criterion for irreducibility through a nonempty covering
family of irreducible affine opens with nonempty pairwise intersections.
[Stacks, Lemma 28.3.4, Tag 01ON](https://stacks.math.columbia.edu/tag/01ON)
identifies integral schemes with reduced irreducible schemes.
Both primary pages were checked for SP92. The manuscript adds keys
`StacksIrreducibleAffineCover` and `StacksIntegralReducedIrreducible`;
no source axiom or geometric input package is introduced.

`normalizationChartToGlued_range_inter_nonempty` constructs an actual
common affine refinement of the original base opens. Its normalization
is nonempty because its coordinate ring is a domain. Chart naturality
places its image in both global chart ranges. The irreducibility proof
uses these irreducible open images and their intersections and proves
global nonemptiness explicitly. SP91's domain stalks and
`isReduced_of_isReduced_stalk` give global reducedness; the existing
`isIntegral_of_irreducibleSpace_of_isReduced` gives the integral instance.

All four APIs need integral `X` and arbitrary `N/K(X)`, without
algebraicity, finite degree, separability, base normality, Noetherianity
or separatedness. The manuscript counterpart is
`prop:normalization-global-integral`. Original chart maps, carriers,
germs and field markings are retained. Integrality does not identify
the intrinsic function field with arbitrary ambient `N`.

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
Chow--Betti generation remain separate.

### Normal local rings of the original glued normalization (SP91, 2026-09-20)

[Stacks, Lemma 10.37.2, Tag 034L](https://stacks.math.columbia.edu/tag/034L)
states that the integral closure of a ring in a field is a normal domain.
[Stacks, Lemma 10.37.5, Tag 00GY](https://stacks.math.columbia.edu/tag/00GY)
states that localization preserves normality. Here the multiplicative
sets are prime complements and avoid zero, so the domain property is
preserved as well.
Both primary pages were checked for SP91. The manuscript reuses the
existing bibliography keys `StacksIntegralClosureNormal` and
`StacksNormalLocalization`; no new bibliography object or source axiom
is introduced.

`normalizedCoordinateRing_isIntegrallyClosed` allows any commutative
`B` mapping to a field `N`. Its direct proof uses
`IsIntegrallyClosedIn.of_isIntegralClosure`, the injective fraction-field
map from `IsFractionRing.liftAlgHom`, and
`AlgHom.isIntegrallyClosedIn`. The ambient `N` need not be the fraction
field of the integral closure, and no algebraicity hypothesis is used.
`normalizedAffineModel_stalk_isIntegrallyClosed` applies
`isIntegrallyClosed_of_isLocalization` and `StructureSheaf.stalkIso`.
The affine coordinate ring is a domain because it is a subring of `N`.

The original `gluedNormalizationOpenCover` covers every global point.
`IsOpenImmersion.stalk_iso` for each original chart map identifies its
local ring with the global local ring. The remaining two APIs transfer
the domain and integral-closedness properties through these actual
isomorphisms. Integral `X` and arbitrary `N/K(X)` suffice; no normality
of the base, finite degree, separability or Noetherianity is required.
The manuscript counterpart is `prop:normalization-global-normal`.
This proves normality as a local-ring assertion; global integrality and
the marked function-field identification are separate.

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
Normal stalks from smooth geometry, faithfulness, fiber/torsor comparison
and Chow--Betti generation remain separate obligations.

### Compatible global normalization and marked-subgroup actions (SP90, 2026-09-20)

No new literature input, bibliography object or primary-page source
verification is needed for this checkpoint. The generic action
reuses `normalClosureNormalizationSchemeIso`, with its existing
`Spec(sigma^-1)` convention, on the original normalization charts.
Direct ring-map extensionality proves naturality with respect to
their actual restrictions. `NatIso.ofComponents` packages the
diagram automorphism; `HasColimit.isoOfNatIso` descends it to the
same glued scheme, and `HasColimit.isoOfNatIso_ι_hom` gives the exact
chart formula. Chartwise morphism extensionality proves compatibility
with the base, identity and multiplication. `Over.isoMk` packages
the action into the existing deck-transformation group without
changing the underlying global automorphism.

The marked affine input is proved directly for the existing
`NormalClosureData` and compatible `B/K/L/N` scalar towers. Subgroup
inverse closure and `IntermediateField.mem_fixingSubgroup_iff` show
that the inverse automorphism fixes the embedded intermediate field.
Extensionality then proves equality of the original normalization
ring maps. The actual marked theorem cancels the existing
`finiteAffinePreimageNormalizationIso`, using its proved comparison
with the chart refinement; it does not cancel the generally nonmonic
map `p`. SP87's exact global chart formula and extensionality give
compatibility with `lambda`, and the same `Over.isoMk` construction
packages the fixing-subgroup action over `Y`.

The ten generic APIs need integral `X` and an arbitrary extension
`N/K(X)`, without algebraicity or separability. The four actual
marked APIs need finite dominant `p`, integral `X` and `Y`, and
explicitly integrally closed stalks of `Y` only; the fifth marked
API is the generic affine statement above. There is no etaleness,
normal-stalk premise on `X`, Noetherianity, perfectness, source axiom
or new geometric input package. Original fields, chart carriers and
germ-derived scalar maps are retained. Manuscript counterparts are
`prop:normalization-global-action` and
`prop:normalization-marked-action`.

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

The fixing-subgroup condition is sufficient, not an exact-stabilizer
theorem. Faithfulness, fiber comparison, torsor or Galois-cover
identification, global normality, normal stalks from smooth geometry
and Chow--Betti generation remain separate.

### Surjectivity of the original global normalization and marked refinement (SP89, 2026-09-20)

[Stacks, Lemma 10.36.17, Tag 00GQ](https://stacks.math.columbia.edu/tag/00GQ)
is the existing lying-over input: an injective integral ring map
induces a surjective map on prime spectra. It does not require a
finite module, an algebraic ambient field extension or a Noetherian
base. The citation is already in the manuscript as `StacksLyingOver`;
no new bibliography object or source axiom is added.

For `gluedNormalizationToBase_surjective X N`, the original chart
algebra maps injectively into its integral closure inside `N`, and
that map is integral by construction. Lying over gives surjectivity
of the actual chart normalization map. Its original affine-base
isomorphism and SP86's target-local property comparison transfer the
property to the existing global `mu_N`. Integral `X` and any field
extension `N` of its original function field suffice, without
algebraicity, finite degree, normality of `X`, Noetherianity or
separatedness.

The second API, `gluedNormalClosureToCover_surjective p hY`, uses the
already proved SP81 surjectivity of the original chart refinement
and SP87's exact marked chart formula. A point of `Y` lies in the
inverse image of an affine neighborhood of its image in `X`; the
actual surjective chart map lifts it and the formula identifies its
global image. This requires only finite dominant `p`, integral `X`
and `Y`, and explicitly integrally closed stalks of `Y`. It does not
use etaleness or normal stalks of `X`, nor does it cancel surjectivity
from `p lambda`. All maps, field markings, carriers and germ-derived
scalars are retained.

The manuscript counterpart is `prop:normalization-global-surjective`,
which states the two scopes separately and combines them with the
existing finite-etale conclusions under SP86/SP88's stronger inputs.
No new geometric hypothesis package is introduced.

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

Compatible Galois-action descent, global normality, normal stalks from
smooth geometry and Chow--Betti generation remain separate.

### Finite etaleness of the actual global marked refinement (SP88, 2026-09-20)

The primary pages for [Stacks, Lemma 29.45.14, Tag 035D](https://stacks.math.columbia.edu/tag/035D)
and [Lemma 29.37.19, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
were checked. The first proves that `f` is finite if `f` followed by
`g` is finite and `g` is separated. Finiteness of `g` is not required.
The second proves etaleness of `f` when both `g` and the composite
are etale. Their role is the standard cancellation step in
`cor:normal-closure-refinement-finite-etale`; neither supplies the
actual normal-closure construction or its normal-stalk inputs.

`isFinite_of_comp_of_isSeparated` directly proves the first statement
in Lean using the graph factorization: the graph is a closed immersion
when `g` is separated, and the following map is a base change of the
finite composite. It does not add a generic postcomposition-property
instance or require integral schemes, normality, Noetherianity or a
field. Mathlib's `IsEtale.of_comp` supplies the etale cancellation.
The manuscript states and cites these standard facts without
repeating their proofs.

`gluedNormalClosureToCover_finite_etale p hX hY` then applies these
facts to SP87's actual marked refinement. It assumes integral `X`
and `Y`, dominant finite etale `p`, and explicitly integrally closed
stalks on both schemes. The exact SP87 triangle and SP86 finite-etale
structural map supply the composite; finite `p` is separated. The
original map, field marking, normalization carriers and germ-derived
scalars remain unchanged. No re-gluing, replacement chart or source
axiom is introduced. The definition of the refinement still retains
SP87's weaker finite-dominant and normal-stalk-of-`Y` hypotheses.

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

Surjectivity, global normality and the compatible global Galois
action remain separate. In the latter, the full group acts over `X`
while only the subgroup fixing the marked `K(Y)` preserves the
refinement. Normal stalks from smooth geometry and Chow--Betti
generation are not supplied by these cancellation results.

### Descent of the original marked refinement (SP87, 2026-09-20)

No new literature input is needed for
`prop:normal-closure-marked-refinement`. The exact project input is
the already proved restriction compatibility of the actual marked
affine refinement. After composing its target chart with the actual
inclusion into `Y`, this square supplies the naturality of
`affineNormalClosureRefinementCocone`. The existing scheme colimit
mapping property supplies `gluedNormalClosureToCover`.

Mathlib's colimit inclusion/descent formula identifies each actual
chart restriction with the original marked map. The previously proved
affine factorization and chartwise morphism extensionality give
`p lambda = mu_(N_p)`. The same extensionality proves uniqueness from
the exact marked chart formulas; it does not prove uniqueness of all
maps making only the triangle over `X` commute. Thus this checkpoint
uses the fixed normal-closure marking throughout, without replacing
the field, normalization carriers, or germ-derived scalar maps.

The five public APIs in `GluedNormalClosureRefinement.lean` assume
integral `X` and `Y`, finite dominant `p : Y -> X`, and explicitly
integrally closed stalks of `Y`. There is no etaleness or normal-stalk
input on `X`, Noetherianity, perfectness, new source axiom, or new
geometric hypothesis package. The previous general gluing references
remain background; no new primary-page source verification is claimed
for this checkpoint.

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

Global finite-etale and surjectivity properties of the refinement and
Galois-action descent remain separate. In the latter, the full group
acts over `X`, and only the subgroup fixing the marked `K(Y)` preserves
the refinement to `Y`. Global normality, normal stalks from smooth
geometry and Chow--Betti generation are not supplied by colimit descent.

### Target-local properties and actual global finite-etale normal closure (SP86, 2026-09-19)

The primary pages for [Stacks, Lemma 29.11.3, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8),
[Lemma 29.45.3, Tag 01WI](https://stacks.math.columbia.edu/tag/01WI)
and [Lemma 29.37.2, Tag 02GJ](https://stacks.math.columbia.edu/tag/02GJ)
were checked for affineness, finiteness and etaleness respectively.
These provide the corresponding target-locality statements; the
lemma numbers here record the current primary pages, with stable
tags used for citation. Their role is background for
`prop:normalization-target-local`, not a premise claiming that an
arbitrary chart normalization is finite etale.

The exact Lean input is
`IsZariskiLocalAtTarget.iff_of_iSup_eq_top`, applied to the actual
nonempty affine opens. The new cover lemma works for any scheme,
including the empty scheme. The property comparison uses
`MorphismProperty.cancel_left_of_respectsIso` and SP85's exact
`normalizationChartPreimageIso_hom_comp_restrict` identity. Thus the
property is tested on the original map
`pi_U = normalizedModelToBase Γ(X,U) N` followed by `hU.isoSpec.inv`.
Mathlib's affine-morphism instance and its target-local finite/etale
instances supply the three concrete consumers.

`FiniteEtaleGluedNormalClosure.lean` then invokes the already proved
SP81 theorem `finiteEtaleAffineNormalClosureToChart_finite_etale` on
each original chart. For dominant finite etale `p : Y -> X` of
integral schemes with explicitly integrally closed stalks of both
schemes, this proves finite etaleness of `mu_(N_p)` for the original
marked normal closure and the actual generic map induced by `p`.
This is the manuscript `cor:normal-closure-global-finite-etale`.
No Noetherian or perfect-field premise and no new source axiom or
geometric hypothesis package is introduced. The locality references
do not supply the normal-stalk inputs or the finite-etale chart proof.

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

Marked refinement and compatible Galois-action descent, global
normality and surjectivity, normal stalks from smooth geometry and
Chow--Betti generation remain separate obligations.

### Actual global inverse-image normalization charts (SP85, 2026-09-19)

[Stacks, Lemma 27.2.1, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
was checked on its primary page. Basis-indexed schemes over their base
opens, with compatible transitions identifying smaller charts with
inverse images, glue over the base; the resulting inverse-image charts
recover the original schemes compatibly. This is the relative-gluing
context for `prop:normalization-global-chart`, not an additional Lean
premise or a replacement for the existing colimit construction.

The seven APIs in `GluedNormalizationChart.lean` prove the exact global
chart range from SP84's actual open cover and structural formula,
SP83's transition ranges, and common principal neighborhoods. The
equality of opens then combines Mathlib's `Scheme.Hom.isoOpensRange`
and `Scheme.isoOfEq` into the actual inverse-image scheme isomorphism
`e_U`. Its inclusion, inverse-inclusion, restricted structural-map
and restriction-naturality identities are direct morphism equalities.
The cancellation arguments use existing open-immersion monomorphisms;
no new source axiom or geometric input package is added.

Integral `X` and its fixed original function-field extension suffice,
with the same normalization carriers and germ-derived scalar maps.
No finite-degree, normality, Noetherianity, separatedness or affineness
of intersections is assumed. SP86 supplies target-local affine/finite/etale
transport above. Marked refinement and Galois-action descent, global normality, normal
stalks from smooth geometry and Chow--Betti generation remain separate.

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

### Actual affine diagram and global gluing (SP84, 2026-09-19)

[Stacks, Lemma 26.14.1, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
and [Lemma 26.14.2, Tag 01JC](https://stacks.math.columbia.edu/tag/01JC)
were checked on their primary pages. The former constructs the glued
locally ringed space with open cover and mapping property; the latter
shows that gluing schemes gives a scheme. They supply the standard
scheme-gluing background for `prop:normalization-gluing`, not the
specific common-refinement proof for this normalization diagram.

The precise Lean consumer is Mathlib's
`Mathlib/AlgebraicGeometry/Gluing.lean`, `Scheme.IsLocallyDirected`:
a small thin indexing category, open-immersion diagram maps, and
`(F comp Scheme.forget).IsLocallyDirected` give `HasColimit` and
`Scheme.IsLocallyDirected.openCover`. Its canonical colimit inclusions
are open immersions; `Scheme.IsLocallyDirected.ι_eq_ι_iff` identifies
equal chart images by a common smaller-chart point.
`colimit.ι_desc`, `colimit.w` and `colimit.hom_ext` give the exact
structural formula, transition naturality and mapping extensionality.

`AffineNormalizationDiagram.lean` supplies all these hypotheses for
the actual inclusion-ordered nonempty affine charts, with their same
fixed ambient field and original scalar maps. The locally directed
instance is proved directly from SP83's exact range and injectivity
and the common-principal-neighborhood input 01IW. This does not assume
separatedness or affine intersections. `GluedNormalization.lean`
constructs the actual glued scheme and its map to the original `X`.
No literature axiom, gluing hypothesis package, or replacement
normalization carrier is introduced. Integral `X` and the fixed field
extension suffice, without finite degree, normality or Noetherianity.

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

SP85 above supplies the exact global chart inverse-image identification;
SP86 supplies global affine/finite/etale properties under its stated hypotheses.
Marked refinement and Galois-action
descent, normal stalks from smooth geometry and Chow--Betti generation
remain separate.

### Coherent affine inverse-image opens (SP83, 2026-09-19)

[Stacks, Lemma 26.11.5, Tag 01IW](https://stacks.math.columbia.edu/tag/01IW)
was checked on its primary page. Every point in the intersection of two
affine opens has a neighborhood principal in both. There is no
separatedness assumption and no assertion that the entire intersection
is affine. The exact Mathlib input is
`exists_basicOpen_le_affine_inter`; the manuscript states the input and
cites `StacksCommonPrincipalNeighborhood` without repeating its proof.

The ten project APIs in `AffineNormalizationCoherence.lean` and
`AffineNormalizationOpenImmersion.lean` prove the actual same-field
restriction laws and use those neighborhoods for pointwise injectivity,
local open immersion, and the exact inverse-image range. The generic
principal-localization inputs retain the SP82 scopes 0307/01I3.
`IsOpenImmersion.of_forall_source_exists` is the existing Mathlib
local criterion; no literature axiom or geometric input package is added.
The 2740-job scoped build passes cleanly.
SP83 is validated: the focused suite passes 21 examples and ten exact
standard-three axiom audits. With the unchanged SP82 and SP81 suites,
the total is 85 examples and 57 audits, all clean. The full build passes
3205 jobs with only the two existing Challenge placeholder warnings;
the unchanged dependency audit passes six primary contracts and two
support reports. The 83-page PDF (839977 bytes), final log, seven-page
visual review and all ten API parity checks pass. The static central
inventory is 997 checks, 565 examples and 889 reports; its historical
prefix is unchanged and was not re-elaborated in full.

These results supply nested affine comparisons, not a completed global
gluing construction, an identification using sections of non-affine
overlaps, a global Galois action, or Chow--Betti generation.

### Same-ambient localization and actual affine restriction (SP82, 2026-09-19)

The primary page for [Stacks, Lemma 10.36.11, Tag
0307](https://stacks.math.columbia.edu/tag/0307) was checked. It states
that integral closure commutes with localization for an arbitrary ring
map and multiplicative subset. In the same-ambient specialization,
compatible localization and ambient algebra structures identify the
localized ambient ring with the original one because all denominators
are already units there. This does not require normality,
Noetherianity, separability or finite degree. Reuse the existing
`StacksIntegralClosureLocalization` bibliography entry; SP78's earlier
fraction-field specialization retains its original validation scope.

[Stacks, Lemma 26.6.6, Tag
01I3](https://stacks.math.columbia.edu/tag/01I3) was checked: principal
localization gives an open immersion `Spec(B_f) -> Spec(B)` onto `D(f)`.
[Lemma 10.17.4, Tag
00E2](https://stacks.math.columbia.edu/tag/00E2) identifies inverse images
of basic opens under the actual spectrum map. These are the exact
geometric sources for the principal-open range and restriction target.
They do not assert that localization at an arbitrary multiplicative
subset is an open immersion. The existing [Lemma 26.5.4, Tag
01HV](https://stacks.math.columbia.edu/tag/01HV), parts (3) and (5),
identifies the actual section rings and restriction maps on basic opens;
its existing bibliography key is `StacksAffineStalk`.

SP82's strict map naturality, generic identity/composition laws and
actual-chart comparisons are direct project constructions, not added
source axioms or hypotheses imported wholesale from these pages.
The proved marked-refinement square uses the actual whole-preimage
normalization isomorphism's restriction naturality and the unchanged
field marking. It requires finite dominant `p` and normal stalks on
the inverse images, but no etaleness, base-normality or Noetherianity.
The actual structural square requires dominance only beyond the
integral/nonempty affine chart hypotheses. Both squares apply to
nonempty affine inclusions, not just principal opens.

The final inventory is 28 APIs: 17 generic localization, nine actual
restriction and two marked normal-closure restriction declarations.
All compile cleanly in the 2764-job scoped build. The focused suite
passes 39 examples and 28 enforced standard-three axiom audits without
warnings or errors. Three fresh neighbor suites also pass; the four
suites total 107 examples and 71 audits, without warnings or errors.
The full build passes 3203 jobs with only the two unchanged Challenge
warnings. The unchanged dependency audit passes six primary contracts
and two support reports. All 28 API parity checks and independent
review pass. The 81-page PDF (835379 bytes), clean final log and
seven-page visual review pass. The static central inventory is 987
checks, 565 examples and 879 reports; its historical prefix is unchanged
and was not re-elaborated in full. The SP82 parity-queue entry records
the complete validation. The manuscript reuses `StacksIntegralClosureLocalization`
and adds only `StacksPrincipalLocalizationOpen` (01I3); this ledger's
00E2/01HV checks document the precise underlying geometric source scope,
not duplicate bibliography entries. The citations and generic composition
identities do not assemble actual overlaps, cocycles, global gluing or
the compatible Galois action. Deriving normal stalks from smooth geometry
and Chow--Betti generation remain separate.

### The actual finite etale affine refinement (SP81, 2026-09-19)

The primary pages for [Stacks, Lemma 29.37.3, Tag
02GN](https://stacks.math.columbia.edu/tag/02GN),
[Lemma 29.37.4, Tag 02GO](https://stacks.math.columbia.edu/tag/02GO), and
[Lemma 29.37.9, Tag 02GP](https://stacks.math.columbia.edu/tag/02GP) were
checked: etale morphisms are closed under composition and base change,
and open immersions are etale. [Lemma 29.37.19, Tag
02GW](https://stacks.math.columbia.edu/tag/02GW) states that a morphism
between schemes etale over the same base is etale. These exact stability
and cancellation statements support the scheme-morphism steps, not the
construction of the marked normalization, its factorization identities,
or any global gluing assertion.

The pinned Mathlib scheme predicate uses locally standard-smooth
presentations of relative dimension zero. Its general converse from
`Algebra.Etale` is not available. The direct generic theorem
`piTensorProduct_ringHomProperty` instead transports a property stable
under isomorphism, identity, composition and base change to the existing
finite-index tensor source. `piTensorProduct_isEtale` in
`EtaleTensorSource.lean` specializes this argument to those
local presentations, starting from the actual intermediate scheme-etale
map. It does not assert a new algebraic-to-scheme equivalence.

`FiniteEtaleNormalClosure.lean` applies SP80's actual evaluation
surjectivity and complementary-idempotent kernel through Mathlib's
`isOpenImmersion_SpecMap_iff_of_surjective`. Hence `Spec(ev_B)` is an
open immersion of the existing normalization into the tensor source,
and its structural composite is scheme-etale. The actual affine-chart
constructor retains the original function-field normal closure, whole
inverse image and normalization isomorphism. Both chart section rings
are normal from the explicit stalk hypotheses; no Noetherian-base
premise is used. Ring finiteness gives scheme finiteness. Exact
factorization through the restricted original morphism then gives
etaleness of the actual marked refinement; the original composite over
`X` is proved separately. Boundary separation uses full visibility.

Both actual morphisms are surjective by
`RingHom.IsIntegral.specComap_surjective`, after proving the actual
normalization maps integral and injective. The exact standard counterpart
is [Stacks, Lemma 10.36.17, Tag
00GQ](https://stacks.math.columbia.edu/tag/00GQ), whose primary page was
checked. Chart surjectivity needs only dominance, integral schemes and
the nonempty affine chart, without finiteness, etaleness or either
normal-stalk hypothesis. Refinement surjectivity uses finite dominant
`p` and the normal stalks on its inverse image, with no etaleness or
base-normality premise. These weaker surjectivity hypotheses are distinct
from those of the finite-etale endpoints.

All 19 APIs compile without warnings in the 2761-job scoped build:
seventeen main declarations and two helpers. The 81-page PDF (831678 bytes), clean
final warning/reference/box scan, visual review of pages 12, 13, 61, 72
and 78, and independent geometry/Lean--TeX review pass. The focused suite
passes 25 examples and 19 enforced standard-three axiom audits without
warnings. Five fresh neighbor suites also pass; the six suites total
146 examples and 89 enforced audits, with no warnings or errors. The
full build passes 3200 jobs with only the two unchanged Challenge
warnings. The unchanged dependency audit passes six primary contracts
and two support reports. All nineteen API parity checks pass. The static
central inventory is 959 checks, 565 examples and 851 reports; its
historical prefix is unchanged and the historical file was not
re-elaborated. The SP81 parity-queue entry records the complete validation.
These are
direct project constructions using proved Mathlib
stability APIs, with no literature axiom, replacement marking or new
input package. Localization/overlap compatibility, cocycle gluing,
the global Galois action, normal stalks from smooth geometry and
Chow--Betti generation remain separate obligations.

### The actual integral evaluation factor (SP80, 2026-09-19)

The primary page for [Stacks, Lemma 10.151.4, Tag
02FL](https://stacks.math.columbia.edu/tag/02FL) was checked. For an
unramified ring map, the diagonal multiplication map is a localization
at a single element, with the associated idempotent/separability-tensor
description. This is the exact standard source for the unramified
diagonal input used here. It does not itself supply the integral trace
section, prove integral-evaluation surjectivity, identify the marked
normalization, or prove a global Galois refinement.

`SeparabilityTrace.lean` proves directly that contraction by the algebra
trace of a central separability tensor equals its product; multiplying
one tensor factor by an element then recovers that element under trace
contraction. `UnramifiedIntegralFactor.lean` uses Mathlib's actual
`Algebra.FormallyUnramified.sec` and `Algebra.intTraceAux` to construct
`r:T -> S` over a normal base domain `B`, for its fraction field `K`,
finite `N/K`, `T=IntCl_B(N)`, and `f:S -> T` with `S/B` formally
unramified and essentially of finite type. Generic spanning of the
actual image makes the transported tensor central on `N`; the trace
identity gives `f∘r=id`. Its value `E=r(1)` is idempotent and the
kernel is `(1-E)`. The section respects the source action through `f`.
This needs neither normality nor flatness of `S`, Noetherianity of `B`,
nor a separately assumed surjection.

`normalizationTensorEvaluation_span` derives the required spanning
condition from SP78's full evaluator square and the proved generic
surjectivity. For the actual finite normal etale intermediate model,
`NormalizationIntegralFactor.lean` specializes the section to `ev_B`,
identifies `P_B/(1-E_m)` with the existing `IntCl_B(N)` by that evaluator,
and derives finite etale structure on the whole normalization. Finiteness
comes from the proved quotient of the finite tensor source. For
etaleness, `IsLocalization.away_of_isIdempotentElem` uses the actual
surjection and kernel formula; `Algebra.Etale.of_isLocalization_Away`
and composition then apply. Under separability,
`β_Σ(1⊗E_m)=e_m` compares the integral selector with SP79's existing
generic one. The actual integral factor and finite-etale result do not
add a separability premise.

These are validated direct project proofs against the pinned Mathlib
APIs. No literature axiom or new source-input package is
introduced. The whole-source integral-closedness route is bypassed, not
proved, and is not attributed to Tag 02FL. All 28 APIs compile without
warnings; the 3198-job full build passes with only the two unchanged
Challenge warnings. The focused suite and five fresh neighbors pass
153 examples and 88 enforced standard-three axiom audits. The unchanged
dependency audit passes six primary contracts and two support reports.
The central inventory is 940 checks, 565 examples and 832 reports; the
historical prefix is unchanged and was not rerun in full. The 79-page
PDF (826296 bytes), eight-page visual review and independent
mathematical/Lean--TeX reviews pass; the SP80 parity-queue entry records
the complete validation. The focused suite
verifies the actual scheme-chart ring specialization from normal stalks
without Noetherianity. SP81 implements the named affine cover and actual
finite-etale morphisms, with validation complete. Localization/overlap
compatibility, cocycles, gluing, the global Galois action, normal stalks from smooth geometry and
Chow--Betti generation retain their separate obligations.

### The selected generic evaluation factor (SP79, 2026-09-18)

[Stacks, Lemma 10.143.4, Tag
00U3](https://stacks.math.columbia.edu/tag/00U3) states that an algebra over
a field is etale exactly when it is a finite product of finite separable
field extensions. The primary page was checked. This citation supplies
the standard classification underlying generic factor splitting; it does
not identify the selected evaluation factor, extend its idempotent to
an integral model, or prove whole-chart etaleness.

The Lean implementation is direct, not a literature axiom or a new input
package. `NormalClosureFactor.lean` obtains finite-dimensionality from
the existing finite tensor theorem without separability, and etaleness
from extension separability and the existing tensor-etaleness theorem.
Mathlib then gives Artinianness and reducedness. In
`ReducedArtinianFactor.lean`, `IsArtinianRing.equivPi` decomposes a
reduced Artinian algebra by its actual maximal ideals. Splitting off
`ker(f)` and using `Ideal.quotientKerAlgEquivOfSurjective` gives a product
equivalence whose first component is the given surjection `f` itself.
The selected idempotent is the inverse image of `(1,0)`; its
idempotence, value, kernel-annihilation equivalence, complementary
principal-kernel formula and uniqueness are proved directly.

Applied to the existing marked tensor evaluation, these constructions
give `Φ_m:P_K ≃_K N × Q_m` and `e_m=Φ_m⁻¹(1,0)`, with
`pr₁∘Φ_m=ev_K` as algebra homomorphisms. No unital section from `N`
to the full tensor product is asserted. There are nine generic and seven
normal-closure APIs. Both leaves compile without warnings, the full
3195-job build passes with only the two existing Challenge warnings,
and the focused suite and four fresh neighbor suites pass 123 examples
and 60 enforced standard-three axiom audits. The fresh unchanged
dependency audit passes six primary endpoint contracts and two support
reports; PDF and independent review pass. Validation completed on
2026-09-19, following the 2026-09-18 source check;
the SP79 parity-queue entry records detailed validation.

The integral selector, its comparison with this canonical generic
idempotent, and the actual finite etale normalization are proved in
SP80 above. The trace-section route bypasses
whole-source integral-closedness. These integral statements and gluing
are not consequences claimed for Tag 00U3; the SP79 validation record
retains its original scope.

### Tensor base change and the full evaluator square (SP78, 2026-09-18)

The primary page for [Stacks, Lemma 10.36.11, Tag
0307](https://stacks.math.columbia.edu/tag/0307) was checked: integral
closure commutes with localization. For the map `B -> L`, localization
at the non-zero-divisors of `B` identifies the base with its fraction
field `K`, while those elements are already units in `L`. Algebraicity
of `L/K` makes every element integral over `K`, so the localized integral
closure is `L`. Normality, Noetherianity, separability and finite degree
are not needed for this specialization. This is the standard source
for the one-factor normalization comparison, not for factor splitting,
whole-chart etaleness or gluing.

Lean uses the proved Mathlib `IsIntegralClosure.isLocalization`,
`Algebra.isPushout_of_isLocalization` and `Algebra.IsPushout.equiv` APIs
to construct `normalizedCoordinateRingBaseChangeEquiv`, preserving the
actual scalar map and integral-closure inclusion on pure tensors.
`PiTensorBaseChange.lean` proves the generic finite-index tensor
base-change equivalence directly from the tensor universal properties,
with inverse laws and factorwise algebra congruence on existing carriers.
The generic base-change theorem needs commutative rings and a finite
index, not a field or flatness premise; factorwise congruence itself
requires no finiteness of the index.
Their composition identifies `K⊗_B P_B` with `P_K` for the same marked
closure. The full evaluator square is equality of the resulting algebra
homomorphisms, not an added commuting-square hypothesis.

The three generic finite-family evaluation helpers are relocated unchanged
to `FiniteTensorProduct.lean` without name changes or duplication. No
literature axiom or new geometric input package is introduced. There are
thirteen new APIs, distinct from the three relocated helpers. The central
inventory is 896 checks, 565 examples and 788 reports; its historical
prefix is unchanged and was not rerun in full. The 76-page PDF (812185
bytes) passes its build, warning scan and visual checks. Both new leaves
compile without warnings. The focused suite passes 25 examples and 13
enforced standard-three axiom audits, including three actual function-field
cases. The full build passes (3189 jobs; only the two existing Challenge
placeholder warnings). Fresh SP77, SP76 and SP74 reruns pass 28/17, 23/7
and 22/7, respectively: 98 examples and 44 enforced axiom audits across
the four suites. The fresh unchanged dependency audit passes six primary
endpoint contracts and two support reports.

SP79 supplies generic direct-factor/idempotent splitting under
separability. SP80 proves the integral selector, its exact generic
comparison and the actual finite etale normalization through a trace
section. SP81 implements the actual affine cover and morphisms, with
validation complete. Localization/overlap compatibility, cocycles, gluing
and the global Galois action remain separate and are not attributed to
Tag 0307.

### Finite tensor source and marked evaluations (SP77, 2026-09-18)

These are direct project proofs against the pinned Mathlib APIs, not new
literature input packages or axioms. `FiniteTensorProduct.lean` upgrades
the existing finite-index tensor reindexing, empty/singleton and binary
regrouping equivalences to algebra equivalences. Induction on the finite
index type then uses `Module.Finite.tensorProduct` for finiteness and etale
base change/composition plus `Algebra.Etale.of_equiv` for etaleness. Each result
states only its corresponding property of the copied algebra. The exact
standard etale-stability counterpart is [Stacks, Lemma 10.143.3, Tag 00U2,
parts (2) and (3)](https://stacks.math.columbia.edu/tag/00U2): composition
and base change preserve etaleness. The live source was checked and the
manuscript cites it for the source tensor algebra only. It does not
identify the target normalization with a direct factor or prove its
etaleness.

`NormalClosureTensor.lean` uses `PiTensorProduct.liftAlgHom` to multiply
a finite family of algebra maps. For the embeddings of `L` into the
existing marked `N`, its image is an intermediate field via
`subalgebraEquivIntermediateField`. The factor formula puts every
conjugate field in that image, and `normalClosure_le_iff` and the
normal-closure top identity prove surjectivity. The actual evaluation
kernel is maximal by `RingHom.ker_isMaximal_of_surjective`; the existing
`Ideal.quotientKerAlgEquivOfSurjective` constructs its quotient equivalence
to `N`. This uses the marked datum's finiteness and normal-closure property,
not separability, perfectness or a supplied surjectivity assumption.

`NormalizationTensor.lean` uses the existing `normalizationMap` to
restrict each of those same embeddings to the existing integral closures.
Its factor and pure-tensor formulas identify the resulting integral
evaluation with the field evaluation after inclusion into `N`. SP70's
`normalizedCoordinateRing_finite` and `normalizedCoordinateRing_etale`
transport the properties of an actual finite normal intermediate model,
and the new finite-index tensor results make the integral source finite
and etale. The source-property theorems omit the four unused assumptions
`Algebra B K`, `Algebra B N`, `IsScalarTower B K L`, and
`IsScalarTower B K N`; the evaluation maps retain their needed scalar
compatibility. No whole-chart etaleness of the target normalization is
invoked or supplied as a new hypothesis.

All 17 new APIs compile. The central inventory is 883 checks, 565 examples
and 775 reports after appending 17 checks and reports; its historical
prefix is unchanged and was not rerun in full. The 76-page PDF (805454
bytes) passes its build, warning scan and visual checks; independent code
and Lean--TeX review pass. The full build passes (3187 jobs; only the two
existing Challenge placeholder warnings). The new suite passes 28
examples and 17 enforced standard-three axiom audits without warnings.
Fresh SP76 and SP74 reruns pass 23/7 and 22/7, respectively: 73 examples
and 31 audits in these three suites. The fresh unchanged dependency audit
passes six primary endpoint contracts and two support reports.

The quotient over the fraction field alone does not identify a direct
factor. SP78 above constructs the canonical comparison
`K⊗_B P_B ≃ P_K` and full evaluator homomorphism equality left open at
SP77; the preceding validation figures retain their SP77 scope. SP79
constructs the selected generic factor and canonical idempotent under
separability. SP80 proves the integral factor and whole-ring
finite-etale normalization directly by a trace section.
These conclusions and subsequent overlap/gluing arguments do
not follow from the pure-tensor identity alone. The existing Stacks
citations for normalization and Galois closure keep their original
scope; Tag 02FL is used only for the unramified diagonal input.

### Finite normal-closure normalization and actual affine cover (SP76, 2026-09-18)

The exact standard input is
[Stacks, Lemma 10.161.8, Tag 032L](https://stacks.math.columbia.edu/tag/032L):
normality and Noetherianity of a domain, together with a finite separable
extension of its fraction field, give a finite integral closure. There
is no dimension-one, Dedekind or perfect-field requirement. The live
statement was checked against the hypotheses of Mathlib's
`IsIntegralClosure.finite` in
`RingTheory/DedekindDomain/IntegralClosure.lean`. The manuscript states
and cites the result rather than repeating its proof; Lean invokes the
checked Mathlib theorem, not a source axiom.

`FiniteNormalClosure.lean` applies this API to the existing
`normalizedCoordinateRing`, then to the marked normal closure using its
proved finite-dimensionality and separability. This constructs the
second finite normalization model instead of requiring another supplied
finite normal algebra `S`. A one-intermediate-model constructor reuses
the canonical normalization map and the existing full-visible separation
theorem. For actual finite dominant formally unramified integral-scheme
morphisms, the function-field construction supplies the field and marking;
the existing whole affine inverse-image normalization isomorphism supplies
the visible scheme and map. Base-chart normality/Noetherianity and normal
stalks on that inverse image remain explicit. Finite etale morphisms
satisfy formal unramifiedness. No new carrier, package or source axiom
is introduced. The full build passes (3180 jobs; only the two existing
Challenge placeholder warnings). The new suite passes 23 examples and
seven enforced standard-three axiom audits; fresh consumer, affine-chart
and normal-closure reruns pass 24/29, 18/11 and 22/7. The central inventory
has 866 checks, 565 examples and 758 reports after appending seven checks
and reports; its historical prefix is unchanged and was not rerun in full.
The 74-page PDF (788608 bytes) passes its build, warning scan and visual
checks; independent code and Lean--TeX reviews pass. The fresh unchanged
dependency audit passes six endpoint contracts and two support reports.

SP80 proves the actual integral normalization factor and whole-ring
finite-etale structure using the actual finite etale intermediate algebra
and an integral trace section. This is a direct
construction, not a consequence attributed to generic etaleness,
finiteness or full-visible separation. SP81 implements the actual affine
cover and morphisms, with validation complete. Localization/overlap
compatibility, cocycles, gluing and the global Galois action remain
separate, as do normal stalks from smooth geometry and
Chow--Betti generation. The preceding SP76 source and validation records
retain their original scope.

### Local separability and consumer hypothesis cleanup (SP75, 2026-09-18)

The checked arguments now state their actual field hypotheses. Fourteen
fixed-field, invariant-ring, selector/tensor and trace/pole signatures
use `Algebra.IsSeparable K L`. The two existing separability/Galois
helpers move from `NormalClosureConstruction.lean` into `NormalClosure.lean`
under their unchanged names. The trace bound uses `D.isSeparable`
directly, without inserting an unnecessary Galois premise.

Core-freeness uses normality and finiteness already supplied by the
normal-closure datum, not perfectness or separability. Its hypothesis
removal propagates to eleven full-visible, inertia, sheet and projector
consumers. No purity, unramifiedness, finite-model or other geometric
input is removed. The sole remaining perfect-field specialization is the
old `NormalClosureData.isGalois` wrapper, which derives local separability
from the existing finite marked extension and delegates to
`isGalois_of_isSeparable`. No new library declaration, source axiom or
interface is introduced.
The new consumer suite passes 24 regressions and 29 enforced
standard-axiom audits; the trace and pole suites pass 14/11 and 12/9.
Fresh SP74 and finite-affine-cover reruns pass 22/7 and 20/17. The
central inventory has 859 checks, 565 examples and 751 reports after
appending 29 checks and reports; its historical prefix is unchanged
and was not rerun in full. The 74-page PDF (785575 bytes) passes its
build, warning scan and visual checks, and independent Lean--TeX review
passes. The full build passes (3179 jobs; only the two existing Challenge
placeholder warnings). The fresh unchanged dependency audit passes six
endpoint contracts and two support reports. Earlier
dated source/validation records retain their original checkpoint scope,
while the active table below reflects the generalized signatures.

SP76 above implements the `IsIntegralClosure.finite` specialization
identified at SP75, without a dimension-one or Dedekind premise. The
preceding validation figures retain their original checkpoint scope.
Normality of `B` remains explicit; etaleness of the `N`-model and
scheme-level refinement/gluing require subsequent geometric arguments.

### Constructed marked normal closure and Galois bridge (SP74, 2026-09-18)

`NormalClosureConstruction.lean` uses Mathlib's
`IntermediateField.normalClosure` inside `AlgebraicClosure L`. The
canonical `L` inclusion supplies the marked embedding; the existing
normal-closure and finite-dimensional instances populate the existing
`NormalClosureData` fields. Its embedding formula is the original
upstairs-to-algebraic-closure map, not an untracked choice of embedding.

The manuscript attributes normal-closure existence to
[Stacks, Lemma 9.16.3, Tag 09DT](https://stacks.math.columbia.edu/tag/09DT):
for a finite extension, a minimal finite normal overfield exists, with
uniqueness up to the marked extension isomorphism. For containment in an
already chosen algebraic normal ambient field, it cites
[Stacks, Lemma 9.16.5(1), Tag 0BMG](https://stacks.math.columbia.edu/tag/0BMG):
a finite intermediate extension lies in a finite normal intermediate
extension. Here the ambient field is `AlgebraicClosure L`, algebraic
and normal over `K` because `L/K` is finite. These are mathematical
attributions, not Lean source axioms; the constructor uses checked
Mathlib normal-closure instances. The cited proofs are not repeated in
the manuscript.

For an arbitrary supplied marked normal closure `D`, every embedded
copy of a separable `L/K` lies in `separableClosure K N`.
`normalClosure_le_iff` and the normal-closure top identity therefore make
`N/K` separable. Combining this with `D.normal` proves Galoisness.
These direct proofs assume separability of this extension, not perfectness
of every algebraic extension of `K`.

`FunctionFieldNormalClosure.lean` uses SP72's actual generic-stalk algebra
and finite-dimensionality to construct the marked datum, preserving its
canonical embedding into the upstairs function field's algebraic closure.
SP73's separability theorem supplies Galoisness under scheme formal
unramifiedness; etaleness is a sufficient specialization. No literature
axiom, parallel package or replacement generic map is introduced.

At SP74, the old perfect-field-based fixed-field, core-free and selector
consumer signatures remained unchanged. SP75 above connects the local
separability result to them; no perfectness theorem or scheme-level
Galois refinement is asserted. Normal stalks, gluing and Chow--Betti
generation remain separate. The 74-page PDF build, warning scan, visual
checks and independent core/scheme/manuscript review pass. The full
build, twenty-two focused regressions, seven enforced standard-axiom
audits, the fresh SP73 rerun (sixteen regressions and three audits), and
the fresh unchanged dependency audit (six endpoint contracts and two
support reports) pass. The central inventory has 830 checks, 565 examples
and 722 reports after seven checks and reports are appended; its preserved
historical prefix was not rerun in full.

### Separability of the actual generic extension (SP73, 2026-09-18)

`Boundary/Normalization/SeparableFunctionField.lean` implements the
previously inspected route with direct Lean proofs. Scheme formal
unramifiedness supplies the actual affine section-algebra property through
`FormallyUnramified.formallyUnramified_of_affine_subset`. The upstairs
function field is the localization of the whole inverse-image section
ring, so `Algebra.FormallyUnramified.of_isLocalization`, `comp` and
`of_comp` carry that property to the actual `K(X) -> K(Y)` algebra.
The last step uses SP72's proved scalar tower, not an independently
postulated compatibility of field and section maps.

For a finite morphism, SP72 finite-dimensionality supplies essential
finite type. `Algebra.FormallyUnramified.isSeparable` from Mathlib's
`Unramified/Field.lean` then proves separability. The formal-unramified
endpoint only requires an affine morphism; the separability endpoint
requires finite. Scheme etaleness is a sufficient specialization,
not an added premise of the general theorem. No normality, perfectness,
characteristic-zero or literature axiom is used.

SP74 above constructs marked normal-closure field data; the actual global
Galois refinement remains separate. Separability of this particular extension does
not imply or discharge the existing downstream perfect-base-field
hypotheses. Normal stalks from smoothness, gluing and Chow--Betti generation
remain separate. The 73-page PDF build, warning scan and visual checks
pass. The full build, sixteen focused regressions, three enforced
standard-axiom audits, the fresh SP72 rerun (eighteen regressions and
eleven audits) and the fresh unchanged dependency audit (six endpoint
contracts and two support reports) pass. The central inventory has 823
checks, 565 examples and 715 reports after three checks and reports are
appended; its preserved historical prefix was not rerun in full.

### Actual dominant function fields and finite extension (SP72, 2026-09-18)

These are direct Lean proofs, with no newly postulated literature input.
`Cycles/FunctionFieldMap.lean` uses dense range to obtain nonempty inverse
images and preservation of the generic point. The map is the actual
generic-stalk map after the canonical stalk identification.
`Scheme.stalkMap_germ` supplies its section-germ square; stalk-map
composition proves contravariant functoriality. Its open-immersion
specialization is the already existing `functionFieldIsoOfOpenImmersion`,
not a second field carrier or a separately assumed comparison.

`Boundary/Normalization/FiniteFunctionField.lean` turns that square into
`IsScalarTower` on every nonempty base open. On a nonempty affine chart,
SP71's `finiteAffinePreimage_moduleFinite` gives the finite section
algebra, and `functionField_isFractionRing_of_isAffineOpen` identifies
both actual function fields as fraction fields. Injectivity through the
actual generic map yields the faithful section action. Mathlib's
`Module.Finite.of_isLocalization` then proves finite-dimensionality over
the downstairs function field. The global theorem selects an affine
neighborhood of the generic point, without requiring a supplied chart.

No normality, etaleness or Noetherianity is used in SP72. Marked normal-closure
field data, still open at SP72, are constructed in SP74 above.
Its separability input, still open at SP72, is derived in SP73 above;
no global Galois refinement, normal-stalk theorem, gluing or Chow--Betti
generation is concluded here. The manuscript follows the exact same
maps and hypotheses. Its 72-page PDF build, warning scan, visual checks
and independent core/manuscript review pass. The full build, eighteen
focused regressions, eleven enforced standard-axiom audits, the fresh
SP71 rerun (eighteen regressions and eleven audits) and the fresh unchanged
dependency audit (six endpoint contracts and two support reports) pass.
The central inventory has 820 checks, 565 examples and 712 reports, with
eleven checks and reports appended; its historical prefix is unchanged
and was not rerun in full.

The API route inspected at SP72, now implemented in SP73 above, uses
`Algebra.FormallyUnramified.of_isLocalization`, `comp` and `of_comp` to
pass from the actual etale affine section algebra to formal
unramifiedness of `K(X) -> K(Y)`, then
`Algebra.FormallyUnramified.isSeparable` in `Unramified/Field.lean`.
SP72 finite-dimensionality supplies the essential-finite-type premise.
This proves separability of this extension in SP73, not that the
base field is perfect or a replacement for downstream perfectness inputs.

### Actual finite-morphism affine charts (SP71, 2026-09-18)

This checkpoint uses direct Lean proofs against existing Mathlib APIs,
not a newly assumed literature input. `AffineEtaleAlgebra.lean` derives
`affine_appLE_smooth` from the scheme-level locally standard smooth
presentations, then target-locality of `RingHom.Smooth`. Together with
the existing affine formal-unramifiedness theorem and
`Algebra.FormallyEtale.of_unramified_and_smooth`, it proves etaleness of
the actual affine chart algebra and its global-sections specialization.

`AffineNormality.lean` uses `IsAffineOpen.isLocalization_stalk'` and
`IsIntegrallyClosed.of_isLocalization_maximal`: normality of the actual
stalks on a nonempty affine open of an integral scheme implies normality
of its section ring. This does not derive the stalk input from smoothness.

`FiniteAffineChart.lean` gets the finite section algebra from
`IsFinite.finite_app`, the affine inverse image from `hU.preimage p`, and
its actual fraction field from
`functionField_isFractionRing_of_isAffineOpen`. It applies the proved
normal-sections lemma and SP70 normalization identification. The equality
over the original scheme `X` uses `Spec_map_appLE_fromSpec` and the
canonical affine presentation, rather than postulating a compatibility
square. Finiteness and etaleness then transport to the normalization.

There is no new source axiom, geometric input bundle, cover carrier or
function-field replacement. Smooth-to-normal-stalks, construction of the
actual global Galois refinement and its marked generic field data,
gluing, and Chow--Betti generation remain separate. The manuscript
follows the same hypotheses. Its 72-page PDF build, warning scan, visual
checks and independent Lean--TeX review pass. The full build, eighteen
focused regressions, eleven enforced standard-axiom audits, the fresh
SP70 rerun (twenty regressions and seventeen audits) and the unchanged
dependency audit (six endpoint contracts and two support reports) pass.
The central inventory has 809 checks, 565 examples and 701 reports after
eleven checks and reports are appended; the preserved historical prefix
was not rerun in full.

### Finite affine normalization and full visibility (SP70, 2026-09-18)

The selected branch uses direct local Lean algebra and the existing
normal-closure sheet-action results. Supplied finite normal affine
algebras with the marked fraction fields identify with the existing
normalizations; finiteness and etaleness are transported through these
identifications in `Boundary/Normalization/FiniteAffineCover.lean`.
The identification uses `IsIntegralClosure` and integrality; finiteness
is transported with `Module.Finite.equiv`, and etaleness with
`Algebra.Etale.of_equiv`. The finite normal constructor itself does not
require etaleness. Surjectivity of the visible open gives empty conjugate
boundaries, and over perfect `K` the existing core-free action supplies
a moved sheet for each nontrivial subgroup. The moving and combined
boundary ideals are then top, proving separation directly in
`Boundary/Normalization/FullVisibleBoundary.lean`. The sheet argument
uses `intermediateFixingSubgroup_normalCore_eq_bot`,
`exists_sheet_moved_of_normalCore_eq_bot` and
`inertiaInvisibleAt_conjugateSheet_iff`; no regular-pair theorem is used.

No literature conclusion is introduced as an axiom or an input package.
The construction still requires the actual normal affine algebras and
marked normal-closure field data. It does not formalize the global
existence of a finite etale Galois refinement, deduce normality from
etaleness in general, or glue the affine models over a smooth projective
base. The single manuscript records the same affine identification and
full-visible separation, with the same hypotheses. The 71-page PDF build,
warning scan, visual checks and independent Lean--TeX review pass. The
full build, twenty focused regressions, enforced standard-axiom audits
for all seventeen new declarations and fresh unchanged dependency audit
pass. The central inventory's historical prefix is preserved; only the
seventeen new declaration checks and reports are appended, and the
historical suite was not rerun in full.

### Geometric-input audit and algebra controls (SP69, 2026-09-18)

The [input audit](working/0018-geometric-pair-input-audit.md) separates
three scopes: current Lean package facts, elementary geometric examples
not instantiated in Lean, and research-only commutative-algebra controls.
No new source hypothesis, axiom, production declaration or manuscript
statement is introduced. All eight named diagnostics in
`RegularPairGeometryControls.lean` and their enforced standard-axiom
audits pass without warnings; the full library build passes as well.
The unchanged historical inventory and manuscript/PDF were not rerun
or rebuilt for this audit.

For the characteristic-zero map `k[x] -> k[t,t^-1]`, `x -> t^2`, write
the target as `k[x][t]_t/(t^2-x)`. The defining polynomial is monic and
its derivative `2t` is invertible. Thus
[Stacks, Definition 10.144.1, Tag 00UB](https://stacks.math.columbia.edu/tag/00UB)
identifies the presentation as standard etale, and
[Stacks, Lemma 10.144.2(1), Tag 00UC](https://stacks.math.columbia.edu/tag/00UC)
implies the visible map is etale. These exact sources justify only that
visible-map assertion. The boundary and ideal calculations
`J_fix=J_mov=J_fm=(t)` are the audit's elementary calculation for the
involution `t -> -t`; neither source constructs a Lean `NormalizedCover`
or establishes separation.

For a chosen `f` in a Noetherian ring `T`, multiplication by `g` on
`T/(f)` is injective exactly when `g` avoids its associated primes.
Finiteness of those primes follows from Lemma 10.63.5; their union is
the set of zero divisors by Lemma 10.63.9, both in
[Stacks, Section 10.63, Tag 00L9](https://stacks.math.columbia.edu/tag/00L9).
Combining those statements with
[Stacks, Lemma 10.15.2, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
gives the mathematical existence test: the moving ideal must be
contained in none of these finitely many primes. This is a derived
source/API analysis, not a new Lean theorem or a proof of that avoidance
for the geometric moving ideal. The positive and bad-first-element
controls in `Q[y][x]` only test the algebraic distinction.

The full-visible option uses local results rather than a new literature
input: `NormalClosureData.intermediateFixingSubgroup_normalCore_eq_bot`
and `exists_sheet_moved_of_normalCore_eq_bot` give a moved sheet over
perfect `K`; surjective `j.base` would make all pulled-back boundaries
empty and their ideals top. Pairing a nonzero fixed-locus element with
`1` is then possible. No surjectivity hypothesis is in `NormalizedCover`,
and this positive subclass has not been implemented at SP69. The next
step is to select and construct actual geometry, not to cite the desired
avoidance or landing conclusion as though it followed from these sources.

### Direct algebraic criterion and sibling landing audit (SP68, 2026-09-18)

`Boundary/Normalization/HeightOneBoundaryPole.lean` refines its existing
construction to any specified nonzero `f`, without requiring `f in J`, through
`exists_heightOne_boundary_denominator_of_ne_zero`; the former existential
theorem is retained as a wrapper. In
`Boundary/Normalization/RegularPairBoundary.lean`,
`not_le_heightOne_of_regularPair` uses that result and Mathlib's existing
`IsSMulRegular` quotient-module API. For `f,g in J` with `f != 0`, if `g`
acts injectively modulo `f`, so does `g^n`. The relation `t g^n in (f)` then
forces `t in (f)`,
contradicting the constructed denominator's avoidance of the height-one
prime. This is a local proof in the current repository, with a Noetherian
domain as hypothesis; normality and trace theory are not needed.

The normalization consumer
`conjugateBoundarySeparation_of_fixedMoving_regularPairs` uses the existing
fixed-locus and moving-boundary summands, Noetherian `B`, and the supplied
finite normalization model. Separated-summand pairs are a sufficient
condition, not a necessary or equivalent reformulation of separation;
the generic theorem also accepts both elements in the combined ideal.
Its pair witnesses are explicit hypotheses,
not a new input package, axiom or copied vanishing theorem. The quotient
injectivity condition is the non-zero-divisor part of
[Stacks, Definition 10.68.1, Tag 00LF](https://stacks.math.columbia.edu/tag/00LF).
That reference is terminology only: this criterion permits `(f,g)=T`
(even a unit `f`), whereas a regular sequence in the cited definition also
requires a nonzero final quotient. The theorem is proved directly and
does not assume the source definition as a literature premise.
SP68 passes the full build, ten focused regressions and enforced
standard-axiom checks for all three new declarations. The previous
boundary-pole suite was freshly rerun after the refinement: all twelve
examples and nine-declaration allowlist checks pass. The appended
umbrella-export checks, fresh unchanged dependency audit, independent
Lean--TeX review and 70-page single-manuscript build and visual checks
pass. The historical verification inventory prefix is preserved; the
entire inventory was not rerun.

The sibling sources were checked for an independent all-section landing
argument. In `collision-ideals/CollisionIdeals/Planar/Research/`:

- `SecantFrameTraceLanding.lean:36`,
  `boundarySeparation_of_secantFrameTraceLanding`, explicitly assumes the
  containment giving landing for every actual boundary section. Its later
  vanishing consumer retains that hypothesis.
- `SecantFrameCandidate.lean:195`,
  `evaluatedSecantFrameDenominatorIdeal_ne_bot`, proves nonvanishing by
  clearing the finite family of evaluated secant/frame coefficients.
- `FiniteDenominatorCounterexample.lean:102`,
  `polynomial_finiteClearing_not_uniformLanding`, proves that the finite
  clearing statement does not imply uniform landing on the generated
  overring. This is a polynomial negative control, not a Keller example.

The archived manuscript
`manuscript-archive/secant-projectors-and-boundary-inertia-for-planar-keller-maps.tex:3395--3446`
likewise records uniform secant-frame landing as an equivalent separation
target in its Hartogs setup, not an independently proved landing theorem.
The current sibling `paper/paper2.tex` instead treats generic-degree-two
Keller rigidity; it supplies no general Hodge boundary-transfer result.
No sibling module, all-section landing hypothesis or Keller rigidity is
imported here. This audit motivates the direct regular-pair construction
target; it does not disprove or solve the alternative geometric landing
problem.

### Direct geometric adaptation: actual boundary poles (SP67, 2026-09-18)

`Boundary/Normalization/SectionLocalization.lean`,
`Boundary/Normalization/HeightOneBoundaryPole.lean` and
`Boundary/Normalization/BoundaryPole.lean` duplicate and adapt the arguments
of the sibling `collision-ideals/CollisionIdeals/Planar/Research/` files
`BoundarySectionLocalization.lean`, `HeightOneBoundaryPole.lean` and
`BoundaryPoleWitness.lean`. The finite-generation clearing step from
`LocalizationDenominator.lean` is a private helper here. No sibling module,
Jacobian endpoint or source axiom is imported.

Local fraction presentations construct a section directly in Mathlib's
structure sheaf. The sibling's newer `LocalizedModule` implementation is
adapted to the pinned `IsLocalization.mk'` construction in
`Localization.AtPrime`; `IsLocalization.map_units` and
`IsLocalization.mk'_spec` verify compatibility by cross multiplication.
The existing generic-germ algebra map identifies the resulting rational
function. An ideal-power denominator provides these presentations on `V` contained in
`D(J)`. At a height-one prime containing `J != 0`, local dimension one
puts the localized ideal in the radical of a nonzero principal ideal.
Finite generation first supplies an ideal power and then one denominator
outside the prime. The resulting `t/f` is an actual section outside the
base, not a supplied geometric-pole hypothesis.

The pinned Mathlib lacks the sibling's
`Mathlib.RingTheory.KrullDimension.LocalRing` and
`ringKrullDim_eq_one_iff_of_isLocalRing_isDomain`. The adapted proof uses
`IsLocalization.AtPrime.ringKrullDim_eq_height`,
`Ring.krullDimLE_one_iff_of_noZeroDivisors`,
`IsLocalRing.eq_maximalIdeal` and `Ideal.radical_eq_sInf`, followed by
`Ideal.exists_pow_le_of_le_radical_of_fg`. It does not add normality or a
DVR hypothesis to repair that API mismatch. The generic construction
assumes a Noetherian domain; the normalization specialization derives
Noetherianity from `B` and the supplied finite model. Perfect `K` is needed
only when invoking B2's trace-dual denominator for the trace-pole and
uniform-landing separation statements.

The existing `Submodule.colon`, `normalizationTraceDual` and actual
boundary-section carrier are retained. The pointwise trace-pole witness is
proved, and uniform landing for every nontrivial subgroup is an explicit
premise of the separation implication. The independent geometric landing
construction remains B4; neither a candidate ideal's name nor a finite
coefficient bound proves this premise. The full build, twelve focused
regressions and enforced standard-axiom checks for all nine declarations
pass. The appended umbrella-export checks, fresh unchanged dependency
audit, independent Lean--TeX review and 69-page single-PDF build and visual
checks also pass. Earlier checkpoint validation records below remain
historical evidence, not new test runs; the full historical inventory was
not rerun.

### Direct algebraic adaptation: normalization trace dual (SP66, 2026-09-18)

`Boundary/Normalization/TraceDualBound.lean` and
`Boundary/Normalization/NormalizationTraceBound.lean` adapt the finite
trace-dual-span denominator argument from the sibling
`collision-ideals/CollisionIdeals/Planar/Research/NormalizationTraceBound.lean`.
No sibling module is imported. The Hodge construction directly reuses
Mathlib's `Submodule.traceDual B K (1 : Submodule T N)` rather than copying
the sibling's `TraceIntegralSubmodule` carrier. The normalization alias
`normalizationTraceDual C` has the same underlying Mathlib submodule.

The pinned Mathlib provides an integral generic basis through
`FiniteDimensional.exists_is_basis_integral` and a trace-dual basis through
`(Algebra.traceForm K N).dualBasis` using
`traceForm_nondegenerate`. It does not provide the newer sibling
API `b.traceDual`; the local proof adapts to the actual pinned bilinear-form
API. `IsLocalization.exist_integer_multiples_of_finite` supplies a common
denominator for that finite basis, which then clears its entire `T`-span.
The hypotheses are explicit: the two fraction-field structures, integral
closure, and finite separability. No normality of `B`, Noetherianity or
free normalization hypothesis is introduced for the denominator theorem.

The `NormalizedCover` specialization reuses the existing fraction field,
the supplied finite normal closure and its derived Galois structure over
a perfect base field. Noetherianity is introduced only for the subsequent
bounded-overring consumers; the normalization's supplied module finiteness
and its actual integral closure then discharge B0's hypotheses. The
transporter remains `Submodule.colon`. No nonzero geometric landing
multiplier, affine-plane rigidity, global purity or defect-vanishing premise
is imported. The full build and fourteen focused regressions pass. All
eleven new declarations pass an enforced allowlist containing only
`propext`, `Classical.choice` and `Quot.sound`. The unchanged dependency
audit, independent Lean--TeX review and updated single-PDF checks pass.
Completed SP65/SP64 validation blocks below remain historical evidence
for those checkpoints.

### Direct geometric adaptation: actual affine and boundary sections (SP65, 2026-09-17)

`Boundary/Normalization/AffineSections.lean` and `BoundarySections.lean`
adapt the actual generic-germ boundary-section construction from the sibling
`collision-ideals/CollisionIdeals/Planar/Research/BoundarySections.lean` to
this repository's pinned Mathlib and existing `NormalizedCover`. No sibling
module is imported. The generic construction uses
`Scheme.germToFunctionField`, `Scheme.germToFunctionField_injective`,
`functionField_isFractionRing_of_affine`, `IsLocalization.algEquiv`, and
the existing affine section algebra structure. It proves compatibility
with constants and restriction, then takes `AlgHom.range` and
`AlgEquiv.ofInjective`. The full-open comparison uses `Scheme.ΓSpecIso`.
Only a domain, its specified fraction field and nonempty open are required;
normality and Noetherianity are not section-map hypotheses.

The normalization specialization uses
`integralClosure.isFractionRing_of_finite_extension` and the already supplied
normal closure's finite dimensionality to identify the existing `N` as
the fraction field. `IsFractionRing.ringHom_ext` proves that the action on
the normalization is faithful; a nontrivial subgroup therefore has nonzero
fixed-locus ideal and nonempty fixed--moving boundary complement. Its actual
section image is a `T`-subalgebra of `N`; the underlying module is the
existing `.toSubmodule`. The Hodge adaptation introduces no extra section
module carrier or global algebra instance.

This is direct-proof provenance, not a literature hypothesis or a copied
Jacobian vanishing theorem. Actual trace duality, its uniform denominator,
uniform landing of every boundary section, and a pole/separation comparison
are not consequences of this embedding. The full build and sixteen focused
regressions pass; all twenty-one new declarations pass an enforced allowlist
containing only `propext`, `Classical.choice` and `Quot.sound`. The unchanged
dependency audit and the updated single-PDF checks also pass. SP64's completed
full-inventory checks below remain historical evidence for SP64 only.

### Direct algebraic adaptation: bounded overrings (SP64, 2026-09-17)

`Boundary/Normalization/BoundedOverring.lean` adapts the proof of
`subalgebra_eq_bot_of_nonzero_mul_mem_base` from the sibling
`collision-ideals/CollisionIdeals/Planar/Research/MonogenicLanding.lean`.
The Hodge file is self-contained with Mathlib imports only. The mathematical
inputs are `Module.Finite.of_injective`, `IsIntegral.of_finite` and
`IsIntegrallyClosed.isIntegral_iff`; the transporter is Mathlib's existing
`Submodule.colon`. Normality, Noetherianity, the same fraction field, and
nonzero uniform multipliers are explicit hypotheses. The product multiplier
and proper-overring zero-colon consequence are proved locally.

This is direct-proof provenance, not a literature axiom or a copied
Jacobian vanishing endpoint. No affine-plane finite-etale rigidity, global
purity axiom, secant landing hypothesis or actual trace-dual realization is
imported. The full build and focused verification pass, and all three
declarations use only the permitted standard logical axioms.

Status vocabulary in this file distinguishes finding a source from proving
the bridge to the project's interface:

- `FORMAL / SOURCE VERIFIED`: the Lean result is proved, and the cited source
  has the same mathematical content in its stated range.
- `FORMAL / BACKGROUND ONLY`: the Lean result is proved directly, while the
  cited source supplies related geometric context rather than the displayed
  theorem.
- `FORMAL / SOURCE VERIFIED ON FINITE-TYPE SUBCASE`: the Lean result is more
  general, while the cited source verifies the ordinary finite-type case.
- `SOURCE IDENTIFIED / BRIDGE OPEN`: an exact theorem is known, but the
  hypotheses needed to apply it are not yet represented or proved at the
  current Lean interface.
- `NEARBY SOURCE / NOT DISCHARGED`: the source supplies the expected geometric
  construction only after additional identifications or convention checks.
- `FORMAL ALGEBRA / GEOMETRIC INSTANTIATION OPEN`: the algebraic consequence
  is proved in Lean, but Mathlib does not yet construct the geometric objects
  needed to instantiate it.
- `UNVERIFIED`: no exact source-to-interface match has yet been recorded.
- `OPEN`: the mathematical construction itself is not present.

| Input or background result | Lean location | Exact source | Hypothesis match | Status |
| --- | --- | --- | --- | --- |
| The collision Noether different detects the non-unramified locus | `collisionNoetherDifferentIdeal_le_prime_iff_kaehlerDifferential_annihilator_le` and `collisionDifferentDetectsRamificationAt_of_essFiniteType` in `Boundary/NoetherDifferentRamification.lean` | [Stacks, Lemma 49.6.8, Tag 0BVU](https://stacks.math.columbia.edu/tag/0BVU). The enclosing section, which defines the Noether different, is [Section 49.6, Tag 0BVK](https://stacks.math.columbia.edu/tag/0BVK); 0BVK is not the lemma tag. | Stacks assumes a finite-type map `A -> B` and identifies `V(D)` with the primes where the map is not unramified. The Lean theorem assumes `[EssFiniteType R S]`, a localization-friendly condition that includes `FiniteType` via Mathlib's `EssFiniteType.of_finiteType`, and proves the prime-containment equivalence for the same ideal `mu(ann(ker mu))`. This is a support/radical result, not equality with the classical Dedekind different. | FORMAL / SOURCE VERIFIED ON FINITE-TYPE SUBCASE |
| A separated étale self-collision space splits into its diagonal and open complement | `separatedEtaleCollisionSchemeDecomposition` in `Collision/EtaleDecomposition.lean` | [Stacks, Section 41.6, Tag 024S](https://stacks.math.columbia.edu/tag/024S), specifically [Proposition 41.6.1, Tag 024T](https://stacks.math.columbia.edu/tag/024T) | Proposition 41.6.1 says a section of an unramified and separated morphism is open and closed. For an étale separated `f`, the relative diagonal is such a section in `X x_Y X`; the Lean construction proves the resulting clopen coproduct decomposition through Mathlib. | FORMAL / SOURCE VERIFIED |
| Extension of a finite étale cover across a regular compactification boundary | `LiteratureInputs.FiniteEtaleExtension`, `FiniteEtaleExtensionHypothesis`, and `chosenExtension` in `Inputs/FiniteEtaleExtension.lean`; no geometric instance is connected to `CompactifiedSubgroupProjectorExtension` | [Stacks, Lemma 58.31.2, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W), with the reflexive-algebra construction in [Lemma 58.21.5, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6) and essential surjectivity under local purity in [Lemma 58.21.6, Tag 0EY7](https://stacks.math.columbia.edu/tag/0EY7) | Tag 0H2W starts with a finite étale cover of a dense open in a locally Noetherian scheme, assumes codimension-one unramifiedness and regular local rings along the boundary, and produces a finite étale extension over the whole scheme. Tags 0EY6 and 0EY7 describe the depth-two/reflexive-algebra and local-purity mechanisms. These results extend the cover; they do not themselves construct a Chow-correspondence idempotent. The repository must still instantiate the base, boundary, intermediate cover, regularity, and codimension-one unramifiedness hypotheses. | SOURCE IDENTIFIED / SELECTED INPUT; GEOMETRIC BRIDGE OPEN |
| Extension of deck transformations once the finite étale cover extends | `FiniteEtaleExtension.restriction`, `DeckExtensionHypothesis`, `deckEquiv`, and `liftDeckAction` in `Inputs/FiniteEtaleExtension.lean`; restriction is the actual pullback/conjugation map | [Stacks, Lemma 58.10.3, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF) | Under its Noetherian-topology and connected punctured strict-henselization hypotheses, restriction from finite étale covers of the whole scheme to the open is fully faithful. Thus automorphisms of an extended cover extend uniquely. The local connectedness hypotheses and their match to the intended compactification have not been proved here. | SOURCE IDENTIFIED / CONDITIONAL ACTION LIFT FORMAL; GEOMETRIC BRIDGE OPEN |
| Rigidity/triviality of the selected connected finite-etale normalization | `FiniteEtaleNormalizationRigidity` in `Boundary/Normalization/GlobalExtension.lean` | For the sibling's special base `A^2_C`: SGA 1, Exposé XII, Théorème 5.1 ([primary edition](https://arxiv.org/abs/math/0206203); [DOI](https://doi.org/10.1007/BFb0058656)), combined with contractibility of the analytic space `C^2` | SGA 1 supplies the algebraic/analytic finite-cover comparison; contractibility of `C^2` then makes connected finite topological covers trivial. Together these support the former planar application. The Hodge interface allows an arbitrary affine base `Spec B`; it must additionally identify that base, prove the normalization connected, and supply the topological step, or instead assume/prove the appropriate finite-étale fundamental-group statement. | SPECIAL-BASE SOURCE IDENTIFIED / GENERAL BRIDGE OPEN |
| Collision Noether different equals the classical Dedekind different | `CollisionDifferentComparison` in `Boundary/HeightOneDifferent.lean` | Pending exact source | Requires the precise local presentation, complete-intersection/monogenic, or other sufficient hypotheses. This equality is not implied by Tag 0BVU and is no longer needed to obtain the pointwise non-unramified-locus criterion under `EssFiniteType`. | UNVERIFIED |
| Ramification corresponds to the relative inertia index at the base sheet | `HeightOneInertiaRealization` in `Boundary/ExtensionCriterion.lean`; one-way theorem `NormalizationInertia.Diagram.baseClass_inertiaSaturated_of_different_not_le` in `Boundary/Normalization/ExtensionBridge.lean` | Pending exact source for the full equivalence. Nearby background used by the sibling is [Stacks, Section 15.113, Tag 0EXQ](https://stacks.math.columbia.edu/tag/0EXQ) for extensions of DVRs and [Section 58.13, Tag 0BSD](https://stacks.math.columbia.edu/tag/0BSD) for decomposition and inertia groups. The one-way Lean step uses Mathlib's `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. | The full equivalence must include the normal closure, valuation extension, flatness/localization, and residue-separability hypotheses. For extension existence, Lean now uses only unramifiedness implies ramification index one plus the explicit `ConjugateRamificationRealization` equality. The sibling Jacobian-collision lemma has exactly this one-way shape and does not discharge the full interface; its `inertia_nontrivial` and index-comparison fields are also supplied data. | ONE DIRECTION FORMAL / FULL IFF UNVERIFIED |
| Normalization in a fixed field is the fixed subring of the normal-closure normalization | `fixedFieldNormalizationEquivFixedRing` and `intermediateNormalizationEquivFixedRing` in `Boundary/Normalization/InvariantIntermediate.lean` | The algebra equivalence is proved directly in Lean. Its geometric interpretation is compatible with functoriality of relative normalization in [Stacks, Lemma 29.54.5, Tag 035J](https://stacks.math.columbia.edu/tag/035J) and restriction to opens in [Lemma 29.54.6, Tag 035K](https://stacks.math.columbia.edu/tag/035K). Invariants and flat base change are treated in [Lemma 15.112.7, Tag 0BRH](https://stacks.math.columbia.edu/tag/0BRH). | The Lean proof is elementwise and needs no purity or unramifiedness. The marked specialization assumes `Algebra.IsSeparable K L` to identify the fixed field of the fixing subgroup with the marked copy of `L`. Tags 035J/035K supply scheme-level background; 0BRH is not used to prove the displayed equivalence and must not be cited as if it did. | FORMAL / BACKGROUND ONLY |
| Prime inertia at a prime is the stabilizer kernel of the induced residue-ring action | `primeInertiaSubgroup`, `mem_primeInertiaSubgroup_iff`, and `mem_primeInertiaSubgroup_of_smul_sub_mem` in `Boundary/Normalization/PrimeInertia.lean` | [Stacks, Lemma 58.12.4, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST), in the definition of the subgroup `I` used there | Tag 0BST takes exactly the elements stabilizing `Q` and inducing the identity modulo `Q`. Lean realizes this as the kernel of `Ideal.Quotient.stabilizerHom`, mapped from the stabilizer into the ambient group, and proves the equivalent condition `g • Q = Q` together with `g • x - x ∈ Q` for every `x`. This construction itself uses no purity or DVR hypothesis. | FORMAL / SOURCE VERIFIED |
| For marked finite normal-closure data with separable `L/K`, an integrally closed affine base is the full invariant normalization ring | `baseEquivFullInvariantNormalizationRing` in `Boundary/Normalization/PrimeInertia.lean` | The equivalence is proved directly in Lean; [Stacks, Lemma 15.112.10, Tag 0BRK](https://stacks.math.columbia.edu/tag/0BRK) supplies normal-domain/Galois integral-closure background | Lean assumes `Algebra.IsSeparable K L`, `IsIntegrallyClosed B`, and the marked finite normal-closure data, then combines the fixed-field theorem with `IntCl_B(K) ≃ B`. Without integrally closedness the full invariant ring is generally the normalization of `B` in `K`, not `B`. Tag 0BRK is background and is not the proof of the displayed algebra equivalence. | FORMAL / BACKGROUND ONLY |
| The prime-inertia fixed ring is unramified at the selected prime | The canonical generic `InertiaFixedRingUnramifiedAt` and lossless unbundling lemma are in `Inputs/FixedInertia.lean`; `NormalizationPrimeInertiaFixedRingUnramifiedAt` specializes it in `Boundary/Normalization/PrimeInertia.lean`; localized subgroup descent is `fixedRing_isUnramifiedAt_of_inertia_le_localized` in `Boundary/Normalization/FixedRingUnramified.lean`, with the height-one/DVR bridge in `Boundary/Normalization/FixedRingLocalization.lean` and exact normal-closure composition in `Boundary/Normalization/PrimeInertiaDescent.lean` | [Stacks, Lemma 58.12.4, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST); DVR specialization [Lemma 15.114.9, Tag 09EH](https://stacks.math.columbia.edu/tag/09EH) | Tag 0BST assumes a finite group acting on a ring `S` and proves the stronger statement that `S^G → S^I` is étale at the contraction of `Q`, for the exact prime inertia `I`. The Lean proposition uses `FullInvariantNormalizationRing = S^G` and records only the resulting unramifiedness conclusion. Mathlib contains neither theorem. Tag 09EH applies only when the base is a DVR, the field extension is finite Galois, `S` is its integral closure, and `Q` is the selected maximal ideal; it proves étaleness after localization and does not by itself justify the arbitrary-base proposition or global étaleness. Lean now performs the `I ≤ H` descent through selected localizations, proves height-one contraction for finite fixed rings, derives the local DVR in the finite normalization over a Noetherian base, and composes valuation containment with that descent over the literal source `S^G`. No transport to an arbitrary `B` is inferred. The canonical record is moved, not duplicated; it assumes the selected consequence rather than proving the full source theorem. Source application still requires the full invariant base and actual inertia identification. | SOURCE IDENTIFIED / SOURCE INPUT OPEN |
| DVR fixed-inertia étaleness at the selected prime | `ramificationIdx_eq_one_and_isSeparable_of_inertia` in `Boundary/Normalization/DvrInertiaEtale.lean` and `inertia_fixedSubalgebra_etale_atPrime` in `Boundary/Normalization/DvrInertiaFixedRing.lean`; `primeInertiaSubgroup_eq_inertia` in `Boundary/Normalization/PrimeInertia.lean`; the generic étale-to-unramified consumer in `Boundary/Normalization/FixedInertiaEtaleBridge.lean` | [Stacks, Lemma 15.114.9, Tag 09EH](https://stacks.math.columbia.edu/tag/09EH); adapted from AxiomMath/Stacks at pinned revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`, `StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean` | Under a DVR base, finite Galois field extension, integral closure, and selected maximal prime, Lean proves the localization of the actual inertia fixed subalgebra is étale. The adapted modules carry Apache-2.0 attribution and use only standard Lean axioms. This proves the étaleness component of Tag 09EH; the original height-one normalization needs a localization and fixed-ring comparison before the project's `hI` follows. It is not Tag 0BST. | FORMAL (DVR) / ORIGINAL-NORMALIZATION TRANSPORT OPEN |
| Height-one contraction and the local DVR for finite fixed rings | `fixedPoints_hasGoingDown`, `fixedPoints_primeHeight_under_eq_one`, `localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one`, and `fixedSubgroupNormalizationRing_localization_isDiscreteValuationRing` in `Boundary/Normalization/FixedRingLocalization.lean` | Finite-group invariant integrality and transitivity of primes over one contraction: [Lemma 15.112.8, Tag 0BRI](https://stacks.math.columbia.edu/tag/0BRI); lying over [Lemma 10.36.17, Tag 00GQ](https://stacks.math.columbia.edu/tag/00GQ); going up [Lemma 10.36.22, Tag 00GU](https://stacks.math.columbia.edu/tag/00GU); height/dimension convention [Definition 10.60.3, Tag 00KF](https://stacks.math.columbia.edu/tag/00KF); DVR criterion [Lemma 10.119.7, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD); localization preserves Noetherianity and normality [Tags 00FN](https://stacks.math.columbia.edu/tag/00FN) and [00GY](https://stacks.math.columbia.edu/tag/00GY); integral-closure normality [Tag 034L](https://stacks.math.columbia.edu/tag/034L) | Lean derives going down specifically for a finite fixed-ring extension: lift the lower endpoint by lying over, lift the chain by going up, then conjugate the terminal prime to the selected prime using 0BRI. This is not a claim that arbitrary integral extensions have going down. The domain hypothesis makes a nonzero height-one prime contract nontrivially, so its contraction has height exactly one. Noetherianity and normality then make only the selected localization a DVR; neither global dimension one nor global Dedekindness is concluded. Tag 0BRH concerns flat base change of invariants and is deliberately not used for invariant integrality. | FORMAL / SOURCE VERIFIED |
| Centered valuation inertia is contained in prime inertia at the center | `Diagram.valuationInertia_sub_centerPrime` and `Diagram.valuationInertia_le_normalizationPrimeInertiaGroup` in `Boundary/Normalization/PrimeInertia.lean` | Proved directly in Lean, porting `inertia_sub_mem_ramifiedPrime` from the sibling Jacobian-collision repository; [Stacks, Section 58.13, Tag 0BSD](https://stacks.math.columbia.edu/tag/0BSD) is background for valuation inertia | `ValuationCenteredAt` alone proves that every valuation-inertia element acts trivially modulo the contracted center prime, hence `I_val ≤ I_Q`. The reverse direction uses the separate localization bridge recorded in the next two rows. | FORMAL / BACKGROUND ONLY |
| A centered height-one valuation is the normalization localization over a Noetherian base | `Diagram.hasValuationLocalizationAt_of_isNoetherianRing` in `Boundary/Normalization/LocalizationBridge.lean` | Integral closures are normal domains: [Stacks, Lemma 10.37.2, Tag 034L](https://stacks.math.columbia.edu/tag/034L); a finite algebra over a Noetherian ring is Noetherian: [Lemma 10.31.1, Tag 00FN](https://stacks.math.columbia.edu/tag/00FN); a Noetherian local normal domain of dimension one is a DVR: [Lemma 10.119.7, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD); the center condition gives the local factorization: [Lemma 26.13.1, Tag 01J6](https://stacks.math.columbia.edu/tag/01J6); valuation-ring maximality under domination: [Definition 10.50.1, Tag 00I9](https://stacks.math.columbia.edu/tag/00I9) | The finite normalization is supplied by `C.finiteNormalClosureModel`; no general normalization-finiteness theorem is inferred. Lean proves that its height-one localization is a valuation ring, extends the centered map locally, and uses `bijective_rangeRestrict_comp_of_valuationRing` in the common fraction field `N` to obtain an isomorphism. The only additional public hypothesis is `[IsNoetherianRing B]`. Centeredness without this hypothesis, or without direct localization data, is insufficient. | FORMAL / SOURCE VERIFIED |
| Localization identifies prime inertia with valuation inertia | `ValuationLocalizationAt.primeInertia_le_valuationInertia`, `Diagram.valuationInertia_eq_normalizationPrimeInertiaGroup_of_localization`, and its Noetherian specialization in `Boundary/Normalization/LocalizationBridge.lean` | Prime inertia is the stabilizer acting trivially on the residue quotient in [Stacks, Lemma 58.12.4, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST); valuation inertia background is [Section 58.13, Tag 0BSD](https://stacks.math.columbia.edu/tag/0BSD) and the DVR definition [Definition 15.114.3, Tag 09EC](https://stacks.math.columbia.edu/tag/09EC) | Lean proves the comparison directly: a prime stabilizer extends uniquely to the localization, common-field compatibility identifies that extension with the valuation action, and triviality modulo the center becomes triviality on the valuation residue field. Combined with the centeredness inclusion, this yields `I_val = I_Q` and the missing implication `I_val ≤ H → I_Q ≤ H`. The cited Stacks items support the definitions but do not state this exact project-specific equality as a standalone theorem. | FORMAL / BACKGROUND ONLY |
| The diagonal/separability element gives the marked singleton sheet selector | `formallyUnramifiedElem_isIdempotent` and `NormalClosureData.collisionToGenericSheets_elem_eq_baseSheetSelector` in `Boundary/Normalization/SelectorComparison.lean` | [Stacks, Lemma 10.151.4, Tag 02FL](https://stacks.math.columbia.edu/tag/02FL) | Tag 02FL supplies an idempotent in the tensor square cutting out the diagonal for an unramified finite-type map. Mathlib's `Algebra.FormallyUnramified.elem` supplies this element under formal unramifiedness and essential finite type, so the Lean theorem has a broader localization-friendly hypothesis. Lean proves idempotence and, coordinate by coordinate, that the chosen-representative evaluation morphism sends the element to the base-sheet characteristic function. The selector proof does not assume the stronger separable-extension tensor equivalence, which Lean proves separately. | FORMAL / SOURCE VERIFIED ON FINITE-TYPE SUBCASE |
| Galois/torsor collision decomposition `coprod_G X ~= X x_Y X` | `GaloisCollisionDecomposition` in `Correspondence/GaloisCollision.lean` | [Stacks, Lemma 66.14.2, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7), with torsor terminology from [Definition 39.11.3, Tag 049A](https://stacks.math.columbia.edu/tag/049A) and the canonical pseudo-torsor isomorphism from [Definition 39.11.1, Tag 0498](https://stacks.math.columbia.edu/tag/0498) | Tag 07S7 starts with a finite locally free group scheme, a free action, and an additional representability hypothesis; it constructs the scheme quotient `X/G`, an fppf torsor, and hence `G x_S X ~= X x_(X/G) X`. The project instead stores an abstract group action and the coproduct isomorphism with two exact projection equations. In the general case, applying the source still requires the constant-group-scheme/coproduct identification, identification of `Y` with the quotient, and reconciliation of `(g,x) |-> (g*x,x)` with the project's `(id,g)` projection convention. The regular split instance is now proved directly by `SplitGaloisSheets.regularCollisionDecomposition`, without using this source as an axiom; its exact torsor convention is recorded below. | NEARBY SOURCE / GENERAL MATCH OPEN; SPLIT INSTANCE FORMAL |
| Existence of a raw Chow-class lift from a dense open | `ChowLocalizationHypotheses`, `ChowLocalization.projectorClosure_nonempty`, and `exists_boundary_of_convolutionDefect` in `Inputs/ChowLocalization.lean`; no general geometric Chow-sequence instance | [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA) and the localization sequence [Lemma 42.19.3, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX) | In the dimension-function setup of Situation 42.7.1, for a scheme locally of finite type over the base and the reduced closed complement of an open, cycle closure gives a lift on cycle groups, and localization gives `CH_k(boundary) -> CH_k(compactification) -> CH_k(open) -> 0`. Consequently a generic Chow class has some lift. If restriction is separately proved to respect correspondence composition, the defect of a lift of a generic idempotent restricts to zero and localization identifies it as boundary-supported. The package assumes the selected rational-linear sequence. SP56 supplies coefficient and quotient scalar-extension comparisons, and SP62 supplies the actual integral/rational open restriction maps. SP63 proves their surjectivity through actual reduced-closure cycle lifts. The actual closed-complement kernel/image comparison remains a subsequent proof obligation before this localization sequence can be instantiated. Its conditional raw-lift and boundary-image consequences are now formal. Neither cited result supplies that multiplicative compatibility, says that the defect vanishes, or gives an idempotent correction. | SOURCE IDENTIFIED / CONDITIONAL CONSEQUENCES FORMAL; GEOMETRIC AND IDEMPOTENCE BRIDGES OPEN |
| Composition of Chow correspondences and contravariant graph classes | Needed to instantiate the multiplication and graph map in `RationalChowCorrespondenceModel` | [Stacks, Section 45.3, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ), especially [Lemma 45.3.1, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0) and [Lemma 45.3.4, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3) | For smooth projective schemes over a fixed field `k`, Tag 0FG0 gives associative composition of rational Chow correspondences and Tag 0FG3 sends morphisms to graph classes contravariantly. If the cover and its subgroup action extend to such a smooth projective model and that variance convention is matched to the project's graph-algebra convention, the normalized sum of the extended graph classes is therefore an idempotent. The repository has not constructed that model/action, proved the convention match, or connected its Chow algebra to the current abstract interface. | SOURCE IDENTIFIED / CONCRETE MODEL OPEN |
| Finite-locally-free pull--push gives a normalized transfer projector | `normalizedPullPush_isIdempotent` and `RationalDegreeTransfer` in `Realization/Chow/TransferProjector.lean` | [Stacks, Lemma 42.15.2, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH) | Tag 02RH proves `f_* f^* = d` on cycles for a finite locally free morphism of degree `d`. Lean proves the resulting rational linear-algebra identity from an explicit equation `push.comp pull = d • id`. The project's finite split Chow operations are constructed below. The general finite-locally-free geometric instantiation of this transfer interface, and equality of its generic restriction with the subgroup graph average, still require the appropriate Chow and torsor collision comparisons. | FORMAL ALGEBRA / GEOMETRIC INSTANTIATION OPEN |
| Idempotent extension across a compactification in an Abelian-type motivic setting | Potential special-case realization of the existence direction of `CompactifiedSubgroupProjectorExtension`; no Lean bridge yet | Jörg Wildeshaus, [*Intermediate extension of Chow motives of Abelian type*](https://arxiv.org/abs/1211.5327), Theorem 0.1(d), with realization compatibility in Theorem 0.2 | The theorem extends idempotent endomorphisms to the motivic intermediate extension for direct factors of Abelian-type Chow motives arising from Kuga families over pure Shimura varieties and their Baily--Borel compactifications. This is much closer to the projector gap than branch-locus purity, but it is a special geometric theorem: applying it requires identifying the repository's objects and projector with that setting. It does not establish the present abstract inertia-saturation equivalence. | NEARBY SOURCE / SPECIAL-CASE BRIDGE OPEN |
| General cycle extraction, support control, and refined-convolution compatibility | Remaining parts of `RationalChowCorrespondenceModel` in `Realization/Chow/Model.lean` | No single source-to-interface proof yet | The raw localization and smooth-projective graph results above do not cover arbitrary proper-support convolution or prove that a chosen compactified lift remains idempotent. | OPEN |
| Identification with a separately prescribed Hodge projector | `PrescribedChowProjectorLift.realizes` in `Realization/Chow/GaloisProjector.lean` | No source/proof yet | This is application-specific and contains the core algebraicity burden | OPEN |

## Split-point checkpoint

| Input or background result | Lean location | Exact source | Hypothesis match | Status |
| --- | --- | --- | --- | --- |
| Cycles on a finite split scheme have the actual point-subscheme basis | `SplitZeroCycles.Cycles`, `.pointCycle`, `.coordinates`, and `.coordinates_pointCycle` in `Realization/Chow/Examples/SplitZeroCycles.lean` | [Stacks, Definition 42.8.1, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR), with [Example 42.7.2, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM) and [Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO) for dimension | The ambient scheme is finite over a field. Its actual integral closed subschemes are all dimension-zero reduced rational points, and the indexing type is finite, so locally finite cycle support is equivalent to a finite coefficient sum. The cycle module is defined on those actual subschemes before constructing coordinates. Over the field base, the source's cycle dimension is ordinary dimension. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Rational equivalence vanishes, and the additive Chow group has point coordinates | `SplitZeroCycles.IntegralCurve`, `.PrincipalDivisorData`, `.relations_eq_bot`, and `.chowCoordinates` in `Realization/Chow/Examples/SplitRationalEquivalence.lean` | [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW) | The source indexes relations by integral closed curves and units in their function fields. Lean constructs this actual indexing type and proves it empty using dimension zero. The unique principal-divisor map from that domain has empty range; its generated relation submodule is zero. The constructed quotient is therefore linearly equivalent to the cycle module, for integral and rational coefficients. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Rational Chow coefficients agree with scalar extension of the integral Chow group | `SplitZeroCycles.rationalizationEquiv` in `Realization/Chow/Examples/SplitZeroCycleBaseChange.lean`; `.chowRationalizationEquiv` and `.chowRationalizationEquiv_tmul_pointCycle` in `Examples/SplitRationalEquivalence.lean` | Direct project proof using Mathlib's tensor-product and finite-function-module APIs | Point coordinates first identify rational cycles with rational scalar extension of integral cycles. The proved quotient-by-zero equivalences then give `ℚ ⊗[ℤ] CH_0(Z_I;ℤ) ≃ₗ[ℚ] CH_0(Z_I;ℚ)`, sending each tensor point generator to the corresponding rational point class. | FORMAL / DIRECT PROOF |
| Multiplicity one in the fundamental cycle of a split inverse image | `SplitPointGeometry.pointStalkIso`, `.stalkMap_length_of_isOpenImmersion`, and `.stalk_length_of_iso_to_split` in `Correspondence/Examples/SplitPointMultiplicity.lean` | [Stacks, Definition 42.9.2, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU) | The actual point-fiber is a reduced finite split scheme, identified over its ambient scheme by `pointFiberIso`. Its inclusion is a base change of an open and closed point immersion. The actual stalk map is an isomorphism, and Lean computes length one with scalar action through that stalk map, exactly the ambient-stalk multiplicity in the definition. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Proper pushforward sends a rational point to its actual image with degree one | `SplitPointGeometry.imageIntegralSubschemeMap`, `.imageIntegralSubschemeIso`, and `.residueFieldMap_finrank_of_isIso`; `SplitZeroCycles.pushforward` | [Stacks, Definition 42.12.1, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4) | The split map is finite, hence proper. The source and image integral subschemes have dimension zero. The actual restriction map to the scheme-theoretic image is an isomorphism, and its induced residue-field extension has degree one. Extension from point generators gives the proper pushforward formula. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Flat pullback is the fundamental cycle of the actual point fiber | `SplitPointGeometry.pointFiberIso` and `.pointIdealSheaf_comap_mapOfFunction`; `SplitZeroCycles.pullback` and `.pullback_pointCycle` | [Stacks, Definition 42.14.1, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB) | Every map induced by finite split labels is finite étale, hence flat of relative dimension zero. The actual scheme fiber and inverse-image ideal sheaf are identified, and each fiber point has ambient-stalk multiplicity one. Thus the cycle formula copies a target coefficient to precisely its inverse-image point generators. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| External product sends point generators to the actual product-point fundamental cycle | `SplitZeroCycles.externalProduct_pointCycle`; `SplitPointGeometry.pointInclusion_productIso`; `SplitPointGeometry.stalkMap_length_of_isOpenImmersion` | [Stacks, Section 42.61, Tag 0FBU](https://stacks.math.columbia.edu/tag/0FBU) | For schemes locally of finite type over the field, the cited external product is characterized by bilinearity and the fundamental cycle of products of integral subschemes. Here those subschemes are rational point components, their actual product is the corresponding point-pair inclusion, and its multiplicity is one. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Intersection on finite split Chow groups is diagonal pullback of external product | `SplitZeroCycles.externalProduct`, `.intersection`, `.chowExternalProduct`, and `.chowIntersection`; `SplitPointGeometry.diagonal_productIso` | [Stacks, Section 42.62, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0), with [Lemma 42.59.5, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4) | The ambient finite split scheme is smooth of dimension zero, and its diagonal is étale and flat. External point products are actual product points with multiplicity one. The cited flat-Gysin comparison specializes the standard intersection definition to diagonal flat pullback. Lean constructs that finite-split operation and proves its coefficient formula; the source supplies the comparison of definitions, not a new Lean axiom or a general Gysin implementation. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Point-pair Chow cycles compose as matrices | `SplitChowCorrespondence.comp`, `.matrixCoordinates_comp`, `.diagonal`, `.diagonal_comp`, `.comp_diagonal`, and `.comp_assoc` in `Realization/Chow/Examples/SplitChowComposition.lean` | [Stacks, Section 45.3, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ), with [Lemma 45.3.1, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0) | Finite split schemes are smooth projective over the field. Their actual product is identified with the split point-pair scheme. Composition is defined by the cited pull--intersection--push formula using the constructed Chow operations. Lean computes its point coefficients and proves the matrix law, diagonal identity, and associativity, with outputs in rows and inputs in columns. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Exact additive presentation of split scheme-span coefficients | `SplitPointGeometry.span_pointDecomposition_iso`; `SplitSpanRealization.additiveRelations_eq_ker` and `.quotientRealizationEquiv` | Project-specific proof from actual scheme coproducts and matrix normal form; no external source axiom | For an arbitrary field and finite label set, use actual split-presentable span classes. The generators are all finite point-decomposition differences. Their generated two-sided ideal is exactly the realization kernel, so the additive quotient is the matrix algebra. `SplitChowCorrespondence.spanQuotientEquiv` now identifies this quotient with the actual Chow endomorphism algebra, using the proved composition law and respecting point generators. | FORMAL / DIRECT PROOF |
| Actual Chow endomorphisms identify with the additive split-span quotient | `SplitChowCorrespondence.EndAlgebra`, `.mul_eq_comp`, `.matrixAlgEquiv`, `.spanQuotientEquiv`, `.spanQuotientEquiv_pointSpanClass`, and `.spanQuotientEquiv_ofSchemeSpan` in `Realization/Chow/Examples/SplitChowAlgebra.lean` | Direct project proof from the geometric composition theorem and the exact additive quotient | The Chow algebra keeps geometric composition and the diagonal as multiplication and unit. Its coefficient map is therefore an algebra equivalence. Composing its inverse with the previously proved span-quotient equivalence gives the Chow identification and its actual point-generator formula. For every finite split span, its image is proved equal to the proper pushforward of its carrier's fundamental cycle along the pair map. | FORMAL / DIRECT PROOF |
| Chow correspondence action agrees with matrix-vector action | `SplitChowCorrespondence.action`, `.chowCoordinates_action`, `.action_comp`, and `.diagonal_action` in `Realization/Chow/Examples/SplitChowAction.lean` | [Stacks, Section 45.3, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ) | The source defines correspondence pushforward by `p2_* (c · p1^* z)` on smooth projective schemes. The implemented action uses the constructed Chow operations in exactly that formula. Its point-coordinate computation is matrix-vector multiplication and proves compatibility with composition and the diagonal. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Integral closed subschemes and coordinate primes of a finite split scheme | `SplitPointGeometry.existsUnique_pointIso_of_isIntegral`, `.labelEquivIntegralClosedSubscheme`, and `.not_one_le_topologicalKrullDim_of_isClosedImmersion`; `SplitFieldQuotient.existsUnique_prime_eq_ker_eval` and `.evalQuotientEquiv` | Direct project proof using Mathlib scheme, prime-spectrum, and topological-dimension APIs | Over any field and finite label set, an actual integral closed immersion factors uniquely through a reduced rational point by a scheme isomorphism. Canonical ideal-sheaf subschemes are classified, not only their supports. Every actual closed subscheme has dimension at most zero. The separate coordinate-ring calculation classifies all prime quotients. | FORMAL / DIRECT PROOF |
| Actual complex points and their evaluation topology | `SplitComplexPoints.existsUnique_eq_evalPoint`, `.isEmbedding_evaluation`, `.pointDiscreteTopology`, `.schemeMorphism_toBase`, and `.productHomeomorph` in `Realization/Betti/Examples/SplitComplexPoints.lean` | Direct project proof from algebra homomorphisms, prime kernels, `Spec.map`, and ordinary complex topology | Points are actual complex-algebra homomorphisms from `ℂ^I`, not a relabelled scheme support. Their topology is induced by evaluations of all coordinate-ring elements into ordinary `ℂ`. The classification makes this Hausdorff subspace finite, hence discrete. Actual point morphisms are over the complex base and natural for the scheme maps; the product comparison respects both projections. | FORMAL / DIRECT PROOF |
| Degree-zero singular cocycles and cup product | `SingularDegreeZero.simplexEquivSingularSet_face`, `.coboundary`, `.H0`, `.equivFunctions`, `.cup`, and `.pullback` in `Realization/Betti/SingularDegreeZero.lean` | [Hatcher, Algebraic Topology, §3.1 p.198 and §3.2 p.206](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) | Actual continuous maps from the standard topological simplices form the cochain indices; the two face restrictions agree with Mathlib's singular set. Unreduced degree zero has no incoming boundaries, so cohomology is the coboundary kernel. Discreteness proves all one-simplices constant and yields point functions. The degree-zero Alexander--Whitney cup is pointwise multiplication; pullback precomposes actual simplices. No assertion identifies locally constant functions with singular `H^0` on arbitrary spaces. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Finite degree-zero transfer | `SingularDegreeZero.transfer` and `.eval_transfer` in `Realization/Betti/FiniteTransfer.lean`; `.zeroSimplexLiftEquiv` and `.transfer_simplex_eq_sum_lifts` in `Realization/Betti/ZeroSimplexTransfer.lean`; `SplitBetti.pushforward` and `.coordinates_pushforward` | [Hatcher, Algebraic Topology, §3.G p.321](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) | The source defines transfer for an `n`-sheeted cover by summing simplex lifts. Here the spaces are finite discrete: lifts of a constant simplex are exactly its actual inverse-image points, with the actual singular zero-simplex lift bijection and sum formula proved in Lean. Apply the construction componentwise, with the finite number of sheets allowed to vary and empty fibers contributing zero. A globally constant positive degree is not assumed. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Normalized cycle class of an actual complex point | `SplitBetti.cycleClass` and `.cycleClass_pointCycle` in `Realization/Betti/Examples/SplitCycleClass.lean` | [Deligne, The Hodge Conjecture, §1 pp.1--2](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf) | The source defines the cycle class by Poincaré duality with the complex orientation. For a finite disjoint union of complex points, each point is a positive oriented component and its dual is its characteristic zero-cocycle. Lean constructs that normalized map between independently defined actual Chow and singular degree-zero objects and proves bijectivity. The source supplies the comparison of this finite-dimensional normalization with the conventional cycle class, not a general Poincaré-duality implementation or a new axiom. | FORMAL SPECIALIZATION / SOURCE VERIFIED |
| Chow and cohomological operations and correspondence action agree | `SplitBetti.cycleClass_pushforward`, `.cycleClass_pullback`, and `.cycleClass_intersection`; `.action`, `.cycleClass_action`, `.realization`, and `.realization_cycleClass` in `Realization/Betti/Examples/SplitCorrespondenceAction.lean` | Direct project proof from the actual geometric and singular operations, with the preceding source normalizations | The point formulas prove proper pushforward equals finite transfer, flat pullback equals continuous-map pullback, and diagonal intersection equals singular cup. The cohomological action is independently the pull--cup--transfer expression `p2_* (cl(c) ∪ p1^*u)`. Its equality with the geometric Chow action follows from these compatibilities, not a definition by transport through the cycle-class equivalence. Composition and the diagonal give an algebra representation into actual singular-cohomology endomorphisms, packaged in `RationalCorrespondenceAction`. | FORMAL / DIRECT PROOF |
| Effective degree-zero Hodge structure on actual Betti complexification | `SplitHodgeStructure.Complexification`, `.complexCoordinates`, `.rationalEmbedding_injective`, `.bigrading_effective`, `.bigrading_direct`, `.bigrading_exhaustive`, and `.conjugation_tmul` in `Realization/Betti/Examples/SplitHodgeStructure.lean` | [Deligne, The Hodge Conjecture, §1](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf); [Deligne, Théorie de Hodge II, §§2.1.5--2.1.12](https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf) | The rational space is constructed singular `H^0` of actual finite complex points; its tensor complexification is identified with complex point functions. Lean explicitly specifies the effective type-`(0,0)` bigrading and proves the finite-dimensional, directness, exhaustion, and conjugation laws. The geometric source identifies the degree-zero decomposition: nonnegative form bidegrees with sum zero leave only `(0,0)`. Weight zero alone would not suffice. No analytic forms/de Rham complex or general Hodge comparison theorem is formalized here. | FORMAL SPECIALIZATION / SOURCE VERIFIED; CHECKPOINT VERIFIED |
| Rational Hodge subspace and Hodge morphisms are independent of cycle classes | `SplitHodgeStructure.rationalHodgeClasses`, `.mem_rationalHodgeClasses`, `.rationalHodgeClasses_eq_top`, `.complexifyMap`, `.IsHodgeMorphism`, and `.all_isHodgeMorphism` | [Deligne, The Hodge Conjecture, §1 pp.1--2](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf); [Deligne, Théorie de Hodge II, §§2.1.11--2.1.12](https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf) | The rational Hodge submodule is the inverse image of the complex `(0,0)` piece along the actual rational-to-tensor embedding. Morphisms are actual rational maps whose scalar extensions preserve every bigrading piece. Only after these definitions are made is every rational class, and every rational map between the finite type-`(0,0)` spaces, proved Hodge. The cycle-class map does not enter either definition. | FORMAL SPECIALIZATION / SOURCE VERIFIED; CHECKPOINT VERIFIED |
| The degree-zero Tate line is the actual distinguished point summand | `SplitChowTateBlock.optionSchemeIso` and its inclusion identities; `SplitBettiTateBlock.blockCoordinates` and `.blockCoordinates_snd` | [Deligne, Théorie de Hodge II, Definition 2.1.13](https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf); [Stacks, Lemma 45.4.3, Tag 0FGC](https://stacks.math.columbia.edu/tag/0FGC), and [Lemma 45.4.6, Tag 0FGF](https://stacks.math.columbia.edu/tag/0FGF) | The Tate convention gives `ℚ(0)` type `(0,0)`. The motive unit is `Spec ℂ`, and equal-twist direct sums are disjoint unions. Lean proves the actual scheme coproduct isomorphism and decomposes its actual singular cohomology by restriction. The Stacks interpretation is background for this correspondence block; a general motive category or a nonzero Tate twist is not claimed as a Lean construction. | FORMAL / SOURCE VERIFIED ON THIS BLOCK; CHECKPOINT VERIFIED |
| Geometric graph encoding and lower-left Chow detection | `SplitChowTateBlock.encode`, `.decode`, `.decode_encode`, and `.encode_isIdempotent`; `SplitBettiTateBlock.realization_encode`, `.cycleClass_decode`, `.construction`, and `.detection` | Direct project proof from the actual Chow operations and Betti action, whose exact source matches are recorded above | Encoding adds the distinguished point-pair cycle to proper pushforward along `i↦(*,i)`; decoding is actual flat pullback along that column. Encoding is affine, decoding linear. The action uses the already constructed geometric Betti representation in fixed coproduct coordinates. The lower-left comparison holds for every Chow correspondence, not just encoded classes. | FORMAL / DIRECT PROOF; CHECKPOINT VERIFIED |
| Concrete finite Hodge, graph-lifting, and Palomar target equivalences | `SplitBettiTateBlock.hodgeModel`, `.hodgeCompatibility`, `.hodgeConjectureAt`, `.hodgeConjectureAt_iff_palomarTargetSquare`, and `.hodgeConjectureAt_iff_hodgeMorphismLift` | Direct project specialization of `Realization/Chow/TateGraphProjector.lean` | The model uses actual rational Chow, actual singular degree-zero cohomology, the independent rational Hodge subspace above, and the proved cycle-class map. The geometric encoding/detection instantiate the previously supplied interfaces. Cycle-class bijectivity gives the finite codimension-zero target; the generic theorem supplies the equivalent graph and universal one-idempotent squares. | FORMAL / DIRECT PROOF; CHECKPOINT VERIFIED |
| Actual regular split torsor and homogeneous sheet cover | `SplitGaloisSheets.regularTorsorIso`, `.regularCollisionDecomposition`, `.regularAction_existsUnique`, `.quotientMap`, and `.quotientMap_surjective` in `Correspondence/Examples/SplitGaloisSheets.lean` | [Stacks, Definition 39.11.1, Tag 0498](https://stacks.math.columbia.edu/tag/0498), [Definition 39.11.3, Tag 049A](https://stacks.math.columbia.edu/tag/049A), and [Example 58.5.1, Tag 0BN8](https://stacks.math.columbia.edu/tag/0BN8) | Finite G gives the constant split group and its regular action. The actual collision isomorphism is constructed from the label bijection and actual product/coproduct isomorphisms; its graph-sheet convention has projections x and a*x, the swapped order of the source definition. The actual map g↦gD is finite, étale, proper, and surjective for any subgroup D. No quotient group or normality of D is assumed. | FORMAL SPECIALIZATION / SOURCE VERIFIED; CHECKPOINT VERIFIED |
| Split torsors versus connected Galois covers and normal closures | Scope of the same geometry module and working note 0015 | [Stacks, Section 58.7, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF); [Theorem 9.21.7, Tag 09DW](https://stacks.math.columbia.edu/tag/09DW) | The connected Galois-cover definition is not applied to a nontrivial disjoint union of complex points. In field Galois theory, normality characterizes Galois intermediate extensions; a homogeneous set G/D exists without it. These sources fix terminology and scope, not premises of the constructed split torsor. | SOURCE VERIFIED / TERMINOLOGY ONLY |
| Residual ideal realizes as actual Chow and then actual Betti cohomology | `SplitGaloisResidual.residualCycles`, `.residualChowEquiv`, `.residualChow_mul`, and `.residualChow_residualClass`; `SplitGaloisMarkedComparison.residualRealization` | Direct project proof using the actual cycle, intersection, and cycle-class definitions cited above | The map is the actual point-cycle sum before taking its Chow class; zero extension at the marked sheet proves its inverse. Point intersection proves multiplicativity. The generated Chow class is minus the complement's fundamental class, and composition with the independently constructed cycle class gives the residual cohomology map. No arbitrary target class or inverse Betti representative defines the map. | FORMAL / DIRECT PROOF; CHECKPOINT VERIFIED |
| Actual diagonal embedding and invertible Chow shear | `SplitChowDiagonal.diagonalAlgHom`, `.diagonalAlgHom_injective`, and `.diagonalAlgHom_single`; `SplitChowShear.shearUnit` and `.shear_point_shear_neg` | Direct project proof from actual proper pushforward and geometric correspondence composition; convention [Stacks, Section 45.3, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ) | The diagonal embedding is actual diagonal pushforward of weighted point cycles. The shear is diagonal plus column pushforward; the column product vanishes, proving the inverse and conjugation identity. It is an invertible Chow correspondence, not a scheme automorphism or a redefinition of the fixed Betti action. The valid sheet-to-Chow algebra map does not give an ambient Chow-to-sheet restriction. | FORMAL / DIRECT PROOF; CHECKPOINT VERIFIED |
| Marked action comparison and multiplicative residual rigidity | `SplitGaloisMarkedComparison.markedEmbedding_action`, `.comparison`, `.projectorLift`, and `.palomarTargetSquare`; `MarkedAugmentedAlgebra.generatedClass_sq_eq_neg` and `.generatedClass_eq_neg_one_of_surjective` | Direct project proof using the fixed actual Betti action and the marked augmented algebra laws | The constant-unit source decomposition is compared with the actual geometric Chow shear and the residual point-cycle map. The actual diagonal-then-shear embedding intertwines full sheet multiplication with the constructed Betti action. The target is the independently generated negative fundamental class. For any multiplicative residual map into a rational algebra, the marked residual acts as minus the identity on the image; surjectivity forces its image to be minus the target unit. This is not class-dependent coverage. No nontrivial compactification or purity input is used in the already proper split geometry. | FORMAL / DIRECT PROOF; CHECKPOINT VERIFIED |

### General finite cycles and integral graph restriction (A11p / SP31)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Finite cycles on actual integral closed subschemes | `SchemeCycles.IntegralClosedSubscheme`, `Cycles`, and `fundamentalCycle` | [Stacks, Definition 42.8.1, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR) | The generators are the actual ideal-sheaf subschemes. The underlying Lean module uses finite support and no grading; SP39 defines homogeneous submodules inside this same module for a supplied dimension function. The source permits locally finite support in its dimension-function setting. The existing finite split cycles are definitional specializations. SP40 constructs the intrinsic Noetherian principal-relation quotient; arbitrary proper, flat and intersection operations do not follow from the underlying cycle-module construction. | FORMAL FINITE-CYCLE CONSTRUCTION / SOURCE SCOPE VERIFIED |
| Open restriction of integral generators and weighted graph sums | `SchemeCycles.openRestriction`, `openRestriction_comp`; `FiniteEtaleExtension.graphCycle_restriction`, `graphCycleLinearMap_restriction` | Direct proof from actual ideal-sheaf comap and the graph pullback theorem; compare [Stacks, Lemma 42.14.4, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE) and [Definition 42.9.2, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU) | Nonempty open inverse images are proved integral, and empty intersections contribute zero. An integral graph is a coefficient-one generator. This directly proves the ungraded integral-generator restriction and its linear extension; the source's general dimension-graded statement and generic-length multiplicities for arbitrary closed subschemes are not assumed or formalized by this construction. No Chow convolution is introduced. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |

### Graph intersection and integral ambient multiplicity (A11q / SP32)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Scheme-theoretic composition of closed graphs | `graphIntersectionIdeal_eq_ker`, `graphIntersectionIso`, `graphCompositionIso`, `graphIntersectionIdeal_map_p13` in `Correspondence/GraphComposition.lean` | Direct Lean proof using Mathlib's ideal-sheaf Galois connection, closed-immersion lifts, and pullback universal properties | The ideal is the supremum of actual graph-ideal comaps, not just equality of supports. Separatedness suffices. The first/last map is an isomorphism onto the composite graph; no Chow product, ambient projection properness, or new literature premise is assumed. | FORMAL / DIRECT PROOF |
| Integral fundamental multiplicity over the ambient stalk | `SchemeCycles.genericStalk_length_of_isClosedImmersion`, `integralSubscheme_genericStalk_length` in `Cycles/IntegralMultiplicity.lean` | Direct Lean proof; the local coefficient is the one used in [Stacks, Definition 42.9.2, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU) | The generic source stalk is a field and the actual ambient stalk map is surjective, giving a simple ambient module of length one. Unlike SP31's coefficient-one definition, this proves the ambient-length calculation. It is not a proof of a Chow intersection-product formula or of general nonintegral multiplicities. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |

### Closed-support cycle images and relative graph-slice pull–push (A11r / SP33)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Closed-immersion and closed-support cycle images | `closedImageSubschemeIso`, `closedImageSubschemeIso_genericPoint`, `closedImageCycle_eq_residueDegree_smul`, `closedImmersionPushforward_comp` | Direct Lean proof; compare [Stacks, Definition 42.12.1, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4) | The source-to-image map is proved an isomorphism with generic degree one through its actual residue map. The current finite ungraded map covers closed immersions; the supportwise generator requires its own closed composite. The full dimension-graded proper pushforward, including dimension drop and higher degrees, is not constructed here. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Open graph/slice geometry | `graphMorphism_isOpenImmersion`, `graphIntersectionIdeal_subschemeι_isOpenImmersion`, `graphSliceMorphism_isOpenImmersion` | Direct proof from Mathlib's étale diagonal; compare [Stacks, Proposition 41.6.1, Tag 024T](https://stacks.math.columbia.edu/tag/024T) | The source treats sections of unramified maps; Lean proves the étale specialization. Separatedness supplies closedness. Finiteness and integrality are not needed for openness. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Graph-slice cycle pull–push | `graphRightPullback_graphCycle`, `graphSlicePullPush_graphCycle`, `graphIntersectionCycle_image_p13` | Direct ideal-sheaf and cycle proof; operation definitions compare with [Stacks 02RB](https://stacks.math.columbia.edu/tag/02RB) and [02R4](https://stacks.math.columbia.edu/tag/02R4) | Pullback is the existing open restriction along an actual pair isomorphism. Closed slice pushforward gives the integral intersection cycle, and its outer image is supportwise degree one. No cycle is assigned to a reducible inverse-image graph, no general intersection product is assumed, and the relative products are not identified with absolute Chow correspondence products. | FORMAL / DIRECT PROOF |

### Structural-base product and cycle comparison (A11s / SP34)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Closed relative-to-structural product inclusions | `pairBaseComparison`, `tripleBaseComparison` and their closedness instances | [Stacks, Lemma 26.21.9, Tag 01KR](https://stacks.math.columbia.edu/tag/01KR); Mathlib's actual pullback comparison and stability of closed immersions | For actual maps `p : Y → S`, `b : S → B`, separatedness of `b` alone gives the closed pair inclusion; the triple is formed from two such maps over the common middle factor. Only when `B = Spec k` are these the absolute products over the field. | FORMAL / SOURCE SCOPE VERIFIED |
| Deck, graph, intersection, and whole-cycle slice compatibility | `forgetDeckBase`, `GraphBaseComparison`, `GraphCycleBaseComparison`, `SchemeCycles.openRestriction_iso_eq_pushforward_inv` | Direct proofs from slice-category functoriality, actual scheme morphisms and ideal images, and canonical cycle-map composition | Deck forgetting is injective, not asserted surjective. Integral graph/intersection images need separated `p,b` and integral `Y`. The full-cycle right-pullback square needs only separated `b`; the slice square also needs separated `p`. No arbitrary cycle-product or Chow equivalence is asserted. | FORMAL / DIRECT PROOF |
| Further Chow-operation obligations | SP40 constructs the actual principal-relation quotient with closed-pushforward and isomorphism descent | [Stacks, Lemma 42.19.3, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX), [Lemma 42.20.2, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1), and [Lemma 42.20.3, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2) | SP58 supplies the actual integral-open function-field and local-order comparison; SP59 adds actual open-support restriction, its coefficient formula and integral principal-divisor restriction for locally Noetherian, quasi-compact target. SP60 supplies graded open restriction and the actual open/closed finite-cycle square. SP61 proves both ambient principal-divisor branches, graded generator transport and preservation of the integer relation span and rational equivalence. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General proper/flat and Gysin comparisons are also separate from the proved closed/isomorphism cases. SP52 constructs the field-based dimension function. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. Localization, geometric target identification and broader operation laws remain as recorded there. None of these broader source hypotheses or maps is supplied merely by naming the intrinsic quotient a Chow group. | OPEN / SOURCE TARGET VERIFIED |

### Actual local divisor coefficients and transport (A11t / SP35)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Signed order from actual local quotient lengths | `localOrder`, `principalQuotient_length_ne_top`, `localOrder_algebraMap`, `localOrder_fraction`, `localOrder_map_unit` in `Cycles/LocalOrder.lean` | Mathlib `Ring.ord`, `Ring.ordFrac`; [Stacks, Definition 10.121.2, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD) | Nonzero fraction-field elements have integer orders from finite lengths. The algebra API permits a Noetherian domain of dimension at most one; the scheme application uses its actual local rings of dimension exactly one, matching the cited definition. No DVR or normality assumption is needed. | FORMAL / EXISTING DEFINITION SPECIALIZED |
| Point index, local coefficients and their actual transport | `DivisorPoint`, `divisorPointOfAffineHeightOne`, `divisorOrder_iso`; `functionFieldEquiv_algebraMap`; `ord_ringEquiv`, `ordFrac_ringEquiv` | Direct Lean proofs; coefficient convention [Stacks, Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ); support interpretation [Lemma 28.10.3, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ) | The index is literal points with one-dimensional stalk. Affine height-one primes supply it. Actual scheme isomorphisms give the point/stalk/function-field maps and preserve signed orders. The identification with actual codimension-one cycle generators is supplied separately by SP36 below. | FORMAL LOCAL TRANSPORT |
| Intrinsic Chow construction and the geometric base setup | `principalRelations`, `ChowGroup`, and `classMap` in `Cycles/PrincipalRelations.lean` | [Stacks, Definition 42.17.1, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO), and [Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW) | SP38--SP40 construct actual finite principal Weil cycles, their homogeneity for a supplied dimension function, the subgroup generated by their ambient carrier images, and the quotient. The finite relation prescription matches the cited definition on compatible quasi-compact data. The source's general base-induced dimension function and locally finite type over a universally catenary base are not reconstructed by the intrinsic Noetherian-X interface; SP41 supplies an actual closure-dimension grading in dimension at most one and general finite-type dimension bounds, and SP47 supplies the affine prime-spectrum unit step. SP48 constructs the actual affine dimension functions; SP49 supplies the structural scheme-residue actions and actual affine/open residue comparisons. SP52 proves the common-chart laws and constructs the global function over a field. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FORMAL INTRINSIC CONSTRUCTION / GEOMETRIC BASE INSTANTIATION OPEN |

### Actual codimension-one supports and their transport (A11u / SP36)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Scheme points and actual integral closed subschemes | `pointSupport`, `ambientGenericPoint`, `pointEquivIntegralClosedSubscheme` in `Cycles/PointSupport.lean` | [Stacks, Lemma 26.12.4, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3), and [Lemma 26.11.1, Tag 01IS](https://stacks.math.columbia.edu/tag/01IS) | For any scheme `X`, the first map is the actual vanishing-ideal subscheme of the point closure, with reducedness proved on its affine quotient charts. Its support is irreducible. The inverse applies the closed inclusion to the source generic point. Uniqueness of reduced structure gives equality of ideal-sheaf objects, not merely equality of closed sets. Both inverse laws are proved without assumptions on the ambient scheme. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Chain codimension, local dimension, and the prime-divisor index | `pointClosureOrderIso`, `support_coheight_eq_stalkDim`; `supportCodimension_eq_stalkDim`, `divisorPointEquivPrimeDivisor` | [Stacks, Lemma 28.10.3, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ) | `supportCodimension` is genuine coheight in the inclusion-ordered irreducible closed subsets containing the actual support. The theorem identifies this with the dimension of the ambient stalk at the generic point, using an affine neighbourhood and prime localization. Restricting to value one identifies `DivisorPoint` with actual integral codimension-one supports. No ambient integrality, Noetherianity, or absolute-dimension subtraction is assumed. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Actual image and coefficient transport on prime supports | `ambientGenericPoint_closedImageSubscheme`, `closedImage_pointSupport`, `primeDivisorEquiv_val`, `closedImmersionPushforward_pointSupport`, `primeDivisorOrder_iso` in `Cycles/DivisorSupport.lean` | Direct support-image and existing local-order proofs; coefficient definition [Stacks, Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ) | The generic-point image formula needs only the closedness of the support composite. An ambient scheme isomorphism preserves codimension and its prime-divisor equivalence agrees with the actual ideal-sheaf image; an arbitrary closed immersion is not claimed to preserve ambient codimension. The coefficient is the existing order reindexed at the support's ambient generic point. Its invariance assumes integral locally Noetherian source and target and uses the proved contravariant function-field map. Finiteness is supplied separately by SP37; SP38 assembles the resulting cycles and lifts this coefficient identity to their actual isomorphism transport. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |

### Local finiteness and finite coefficient support (A11v / SP37)

The rows below record the proved interfaces and their verified source scope.

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Height-one finiteness and actual affine fraction presentations | `heightOne_mem_minimalPrimes_span`, `finite_heightOne_primes_containing`; `exists_affine_fraction`, `sectionToFunctionField_through_stalk`, `affineGerm_isUnit_iff`, `divisorOrder_eq_zero_of_affine_fraction` | Direct Lean proofs using Mathlib's principal-ideal/minimal-prime, localization and actual scheme-function-field APIs | Minimality of a height-one prime over a nonzero element needs a domain, not normality or a global dimension bound; Noetherianity supplies finite minimal-prime sets. Fraction presentation needs an integral scheme and a nonempty affine open. Unit-germ detection uses its actual localization at a prime. The coefficient-zero consequence adds local Noetherianity and uses the existing length-based order; it does not assert that nonnegative order implies local regularity. | FORMAL / DIRECT PROOF |
| Local finiteness of the actual nonzero prime-divisor supports | `finite_divisorPoints_in_affine`, `primeDivisorSupports_locallyFinite` in `Cycles/DivisorFiniteness.lean` | [Stacks, Lemma 31.27.4, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL); the family notion is [Definition 5.28.4, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS) | The source and Lean both assume an integral locally Noetherian scheme and a nonzero rational function. The index is the actual prime divisors with nonzero signed coefficient, and the family consists of their closed supports. Affine finiteness plus the equivalence between meeting an open and having generic point in that open proves `LocallyFinite`, not merely finiteness of divisors through each point. Only the source's nonzero-coefficient conclusion is used; no separate theorem for all nonregular germs is claimed. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Quasi-compactness gives finite coefficient support | `finite_primeDivisorOrder_support`, `finite_divisorOrder_support` in `Cycles/DivisorFiniteness.lean` | The quasi-compact specialization described in [Stacks, Section 31.27, Tag 0BE0](https://stacks.math.columbia.edu/tag/0BE0); Mathlib `LocallyFinite.finite_of_compact` | Add only quasi-compactness (`CompactSpace X`) to the integral locally Noetherian hypotheses. Every integral support is nonempty, so local finiteness makes the nonzero-coefficient index finite; the existing support/point equivalence gives the second version. No Hausdorffness or properness is needed. This is finite support of coefficient functions, not a constructed graded principal divisor or Chow relation. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |

### Finite principal-divisor cycles and isomorphism transport (A11w / SP38)

The rows below record the proved interfaces and their verified source scope.

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Finite principal Weil divisor in the existing cycle module | `principalDivisor`, `principalDivisor_apply`, `principalDivisor_support`, `principalDivisor_eq_zero_iff` in `Cycles/PrincipalDivisor.lean` | [Stacks, Definition 31.27.5, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3), using the coefficient convention [Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ) | The source uses an integral locally Noetherian scheme and locally finite Weil divisors. Lean adds quasi-compactness and uses SP37 to assemble the finite sum in the existing ungraded integer cycle module. The coefficient is the actual local order on codimension-one integral supports and zero elsewhere; the cycle support is exactly the included nonzero-coefficient index. Its zero criterion concerns these coefficients, not global invertibility of the rational function. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Products of rational functions give sums of principal cycles | `principalDivisor_one`, `principalDivisor_mul`, `principalDivisor_inv`, `principalDivisor_div`, `principalDivisorAddHom` | [Stacks, Lemma 31.27.6, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP) | Under the same integral, locally Noetherian, quasi-compact hypotheses, the previously proved local-order group laws give equality of actual finite cycles. The bundled additive homomorphism uses an additive tag on the multiplicative group of actual function-field units; it is not a linear or algebra homomorphism from the function field. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Actual support and coefficient transport through an isomorphism | `closedImageSubschemeEquiv`, `closedImmersionPushforward_iso_eq_lmapDomain`, `closedImmersionPushforward_iso_apply_image`, `closedImmersionPushforward_iso_apply` in `Cycles/IsomorphismTransport.lean` | Direct proofs from actual ideal-sheaf image and the existing degree-one closed-immersion cycle pushforward | Any scheme isomorphism and any semiring of coefficients. The support equivalence is literal closed image, with the inverse induced by the inverse isomorphism. Existing pushforward is proved to reindex coefficients by this equivalence; no ambient integrality, Noetherianity, quasi-compactness or general proper-pushforward theory is needed for these cycle formulas. | FORMAL / DIRECT PROOF |
| Principal cycles commute with actual isomorphism pushforward and pullback | `principalDivisor_iso`, `openRestriction_principalDivisor` in `Cycles/PrincipalDivisorTransport.lean` | Direct proofs from the preceding coefficient transport and SP36's actual local-order invariance, with the order convention [Stacks, Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ) | Source and target are integral, locally Noetherian and quasi-compact. For an actual isomorphism `e : X ≅ Y` and `f ∈ k(Y)×`, closed pushforward sends `div_X(e^* f)` to `div_Y(f)`. Existing open restriction along `e` gives the inverse identity. This is isomorphism pullback only, not a theorem for arbitrary open immersions or the general proper norm formula. It introduces neither a dimension grading nor rational-equivalence relations. | FORMAL / DIRECT PROOF; SOURCE CONVENTION VERIFIED |

### Dimension functions and homogeneous principal divisors (A11x / SP39)

The rows below record the proved interfaces and their verified source scope.

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Explicit dimension functions and closed restriction | `DimensionFunction`; `closedImmersion_covBy`, `DimensionFunction.comapClosedImmersion`, its identity/composition laws, and `supportDegree_comapClosedImmersion` | [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9); restriction is proved directly | Both strict monotonicity for proper specializations and the unit step for immediate specializations are retained, expressed in the actual closure-inclusion order on scheme points. A closed immersion is an order embedding with order-convex image, so literal composition restricts the supplied dimension function. These results need no ambient integrality or Noetherianity and do not construct a dimension function for every scheme. | FORMAL / DIRECT PROOF; SOURCE VERIFIED |
| Actual prime-support degree drop and image degree | `primeDivisor_covBy_genericPoint`, `supportDegree_primeDivisor`, `supportDegree_closedImageSubscheme` in `Cycles/DimensionFunction.lean` | The codimension-one implication in [Stacks, Lemma 42.16.1(1), Tag 02RK](https://stacks.math.columbia.edu/tag/02RK), proved directly from the supplied dimension function | On an integral scheme, coheight one gives an actual cover below its generic point and hence degree δ(η)−1; no Noetherianity is required. Degree is δ at the actual ambient generic point, not a difference of absolute Krull dimensions. The image formula only needs closedness of the support composite and does not assert preservation of ambient codimension. The cited source uses a dimension function induced from its finite-type base setup; that general induction is not constructed here. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Homogeneous submodules of the existing finite cycles | `cyclesOfDegree`, `mem_cyclesOfDegree_iff`, `cyclesOfDegree_disjoint`, `closedImmersionPushforward_mem_cyclesOfDegree` in `Cycles/CycleDegree.lean` | Direct proofs using Mathlib `Finsupp.supported`; degree-indexed cycle convention [Stacks, Definition 42.8.1, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR) | For any semiring and supplied dimension function, these are supported submodules of the existing finite-cycle module, with coefficientwise membership and pairwise disjointness. They are not a new free cycle module or a constructed direct-sum equivalence. The converse degree test for a fundamental cycle explicitly needs nontrivial coefficients. Existing closed pushforward preserves degree for compatible actual support degrees; the next row derives that compatibility for restricted dimension functions. | FORMAL / DIRECT PROOF; SOURCE CONVENTION VERIFIED |
| Principal-divisor homogeneity and actual ambient closed images | `principalDivisor_mem_cyclesOfDegree`, `closedImmersionPushforward_mem_cyclesOfDegree_comap`, `closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree`, `principalDivisor_closedSupport_mem_cyclesOfDegree` in `Cycles/PrincipalDivisorDegree.lean` | [Stacks, Definition 42.17.1, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO), using the principal Weil cycle of [Definition 31.27.5, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3) | For integral locally Noetherian quasi-compact X and supplied δ, the existing finite principal divisor lies in degree δ(η_X)−1. Existing closed pushforward preserves degrees computed by actual restriction of δ, with no extra compatibility premise. For an actual integral closed carrier W, its pushed principal divisor has ambient degree δ(ξ_W)−1; only W must be locally Noetherian and quasi-compact, not the ambient scheme. SP39 proves the requisite homogeneity; SP40 subsequently constructs the actual principal-relation subgroup and its quotient. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |

### Actual principal relations, Chow quotient and closed/isomorphism descent (A11y / SP40)

The rows below record the proved interfaces and their verified source scope.

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Actual carrier divisors and their closed images | `idealSubscheme_isLocallyNoetherian`, `idealSubscheme_compactSpace`, `ambientPrincipalDivisor`, `closedImmersionPushforward_ambientPrincipalDivisor`, `exists_ambientPrincipalDivisor_image` in `Cycles/PrincipalDivisorImage.lean` | Direct actual affine-quotient, closed-embedding and support-to-image proofs, using SP38's principal-divisor isomorphism theorem | Closed carriers inherit local Noetherianity and quasi-compactness from the ambient scheme, or transport these properties through their actual support isomorphism. The ambient divisor is literally existing closed pushforward of the carrier divisor. Its image function is explicitly the inverse of the contravariant function-field isomorphism applied to the source function, not a promised norm or unspecified witness. The divisor-image theorem needs a closed immersion and only source-carrier finiteness; it imposes no ambient integrality or separate properness hypothesis. | FORMAL / DIRECT PROOF |
| Actual principal generators and exact finite-sum/source matching | `PrincipalRelationData`, `principalRelation`, `principalRelation_zpow`, `principalRelations`, `mem_principalRelations_iff_exists_list`, `principalRelationData_family_locallyFinite_iff` | [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW); product convention [Lemma 31.27.6, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP) | The actual index is an integral closed carrier of degree n+1 together with a unit in its own function field. On Noetherian X the generated integer submodule equals unweighted finite lists of these actual relations, because integer weights are absorbed as function powers. Quasi-compactness makes local finiteness of the actual nonempty carrier family equivalent to a finite index, including zero divisor generators. Thus the finite prescription matches the source on compatible dimension-function data; local finiteness of divisor-cycle supports alone is not substituted for carrier local finiteness. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Quotient by the constructed principal relations | `RationallyEquivalent`, `rationallyEquivalent_iff_exists_list`, `ChowGroup`, `classMap`, `classMap_eq_iff`, `classMap_eq_zero_iff`, `classMap_surjective`, `classMap_principalRelation` in `Cycles/PrincipalRelations.lean` | [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), with the preceding finite-case matching | The quotient is of the existing homogeneous integer cycles by the actual generated submodule. Difference membership defines rational equivalence, and the class-map equality, kernel, surjectivity and generator-zero laws are proved. It uses a Noetherian ambient scheme and supplied dimension function, with no ambient integrality assumption or arbitrary relation input. This constructs an additive integral Chow group; SP56 subsequently proves its rational coefficient comparison. General intersection products and the correspondence algebra remain separate. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Closed pushforward preserves generators, relations and quotient classes | `gradedClosedImmersionPushforward` in `Cycles/GradedPushforward.lean`; `PrincipalRelationData.closedImage`, `gradedClosedImmersionPushforward_principalRelation`, `principalRelations_le_comap_closedImmersionPushforward`, `chowClosedImmersionPushforward` and its class-map/identity/composition laws in `Cycles/ChowPushforward.lean` | Closed-immersion specialization of [Stacks, Lemma 42.20.3, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2), proved directly from actual carrier-image transport | For Noetherian source and target, the existing geometric map restricts to homogeneous cycles, carries each actual generator to the one on its actual image, preserves the span, and descends to the quotient. The general helper allows a numerical equality of actual support degrees; the canonical restricted dimension function proves it. Relation preservation is a theorem, not part of that numerical compatibility input. General proper pushforward is not constructed. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Isomorphism equivalence with actual open-restriction inverse | `gradedIsoEquiv`, `gradedIsoEquiv_symm_val`, `principalRelations_map_gradedIsoEquiv`, `chowIsoEquiv` and its forward/inverse class-map formulas in `Cycles/ChowIsomorphism.lean` | Direct specialization of the proved closed pushforward to both directions of an actual scheme isomorphism | The forward map is the same closed quotient pushforward. Its inverse on representatives is the existing geometric open restriction along the isomorphism. Both directions preserve the actual relation submodules, which proves the quotient equivalence. This does not claim injectivity for arbitrary closed immersions. General-open relation preservation and integral/rational quotient restriction are supplied subsequently by SP61–SP62. | FORMAL / DIRECT PROOF |

### Carrier dimension, finite bounds and a constructed low-dimensional grading (A11z / SP41)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Actual carrier dimension is point height | `integralSubschemePointOrderIso`, `ambientGenericPoint_height_eq_supportDim`, `point_height_eq_supportDim`, `point_height_toNat_eq`, `point_height_toNat_strictMono` in `Cycles/SupportDimension.lean` | Direct proof from the actual closed inclusion and the point/irreducible-closed order equivalence; scheme dimension convention [Stacks, Section 28.10, Tag 04MS](https://stacks.math.columbia.edu/tag/04MS) | On any scheme, the points of an actual integral closed carrier are order-isomorphic to the specializations of its ambient generic point. Its topological dimension is therefore that point's height, not its ambient coheight. Finite ambient dimension gives finite integer closure heights and strict decrease under proper specialization. No Noetherianity, integrality of the ambient scheme or catenarity is assumed; no unit-step law follows from finiteness alone. | FORMAL / DIRECT PROOF; SOURCE CONVENTION VERIFIED |
| Finite dimension from an actual polynomial presentation | `polynomialDimensionBound`, `ringKrullDim_le_bound_of_surjective`, `ringKrullDim_lt_top_of_finiteType`, `finiteRingKrullDim_of_finiteType`, `spec_topologicalKrullDim_lt_top_of_finiteType`, `quotientSpec_topologicalKrullDim_lt_top_of_finiteType` in `Cycles/FiniteTypeDimension.lean` | Direct proof using Mathlib's proved one-variable inequality and actual polynomial presentations; the stronger classical polynomial calculation is [Stacks, Lemma 10.114.1, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP) | Over any field, iteration of dim R[T] ≤ 2 dim R + 1 gives a finite recursive bound for a finite polynomial algebra. Surjectivity transfers it to any finite-type algebra and its actual affine quotient spectra. The strict bound below infinity includes the zero algebra and empty spectrum; only the nonempty `FiniteRingKrullDim` package requires a nontrivial algebra. This SP41 bound does not itself assert sharp polynomial dimension or equality with transcendence degree; SP42 below subsequently proves those algebraic comparisons. | FORMAL / DIRECT PROOF; STRONGER SOURCE CONTEXT VERIFIED |
| Finite dimension from an actual structural morphism | `point_coheight_eq_of_isOpenImmersion`, `topologicalKrullDim_lt_top_of_finite_openCover`, `affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType`, `topologicalKrullDim_lt_top_of_finiteType` in `Cycles/FiniteTypeSchemeDimension.lean` | Direct proof using the preceding affine bound, actual stalk isomorphisms and a finite affine subcover; compare the stronger field dimension theory in [Stacks, Lemma 33.20.3, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | An actual structural morphism X → Spec(k), locally of finite type and quasi-compact, supplies the finite-type algebra on each actual affine chart. Open stalk isomorphisms preserve point coheight; a finite affine subcover therefore bounds the global dimension. The theorem includes empty and reducible schemes and assumes neither integrality nor a separate algebra or dimension bound on global sections. This proves finite dimension, not a general dimension-function instance. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| A dimension function constructed from dimension at most one | `DimensionFunction.ofKrullDimLEOne`, `supportDegree_ofKrullDimLEOne_eq_iff`, `fundamentalCycle_mem_ofKrullDimLEOne_iff`, and its evaluation, range and strict-specialization laws in `Cycles/LowDimensionalDimensionFunction.lean` | Direct order proof of both conditions in [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9) | The function is the integer-valued actual point height, which the carrier theorem identifies with dimension of the reduced point closure. A strict pair must have heights zero and one, proving both strict decrease and the immediate-specialization unit step. Only the actual bound dim X ≤ 1 is supplied, not either grading law. The actual carrier degree equals its topological dimension; for natural n and nontrivial coefficients, fundamental-cycle membership in the existing degree-n piece is exactly that dimension test. There are no integrality, Noetherianity or nonemptiness assumptions. | FORMAL / DIRECT PROOF; SOURCE DEFINITION VERIFIED |
| Actual affine-line instance | `Examples.affineLine`, `affineLine_dimension`, `affineLineDimensionFunction`, `affineLineOrigin`, `affineLineDimensionFunction_genericPoint`, `affineLineDimensionFunction_origin` in `Cycles/Examples/DimensionFunction.lean` | Direct polynomial-PID and actual maximal-kernel proofs; compare the one-variable case of [Stacks, Lemma 10.114.1, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP) | For every field k the scheme is literally Spec(k[T]); its exact dimension is one. The preceding constructed dimension function gives value one at the actual generic point and zero at the actual origin defined by the constant-coefficient kernel. This provides a positive-dimensional instance, not merely a supplied-grading example or an affine-line Chow-group computation. | FORMAL / DIRECT PROOF; SOURCE SUBCASE VERIFIED |
| General field-based grading and the target degree convention | SP52–SP55 construct field-based grading, identify actual carrier dimensions, prove the integral codimension/degree comparison and reindex the existing principal relations | [Stacks, Lemma 29.53.3, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW), specialized by [Example 42.7.2, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM); closure dimension [Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO); field-specific laws [Lemma 33.20.3(6), (7), (9c), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | The general source uses a locally Noetherian universally catenary base with a dimension function and a locally finite type morphism. Over Spec(k) with base value zero it gives δ(x) = trdeg_k κ(x) = dim closure{x}; locally finite type is enough, without ambient integrality or separatedness. Quasi-compactness is additionally needed by the current finite-cycle Noetherian quotient. SP42 below proves the affine transcendence-degree comparison, and SP47 proves the affine prime-spectrum unit step. SP48 constructs the actual affine dimension functions using the existing order comparison and the structural morphism. SP49 supplies the structural scheme-residue actions and actual affine/open algebra comparisons. SP50 identifies arbitrary structural affine values with actual residue degrees and proves affine-open agreement. SP51 supplies the nonaffine pointwise finiteness and chart-value agreement. SP52 proves the common-chart order/cover laws and constructs the global field-based dimension function; the construction is not inferred merely from finite dimension. SP53 identifies its actual finite point heights and point-closure/carrier dimensions. SP54 identifies actual codimension n with complementary degree d−n on integral schemes. SP55 reindexes the existing relations and proves top-degree vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FIELD GRADING, DIMENSION, INTEGRAL CODIMENSION AND RELATION REINDEXING FORMAL IN SP52–SP55 / BROADER TARGETS OPEN |

### Transcendence degree and actual affine dimensions (A11aa / SP42)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Dimension invariance under an actual integral injection | `integral_specComap_strictMono`, `exists_primeSeries_lift_of_injective_integral`, `ringKrullDim_eq_of_injective_integral` in `Cycles/IntegralDimension.lean` | [Stacks, Lemma 10.112.4, Tag 00OK](https://stacks.math.columbia.edu/tag/00OK) | For commutative rings with an actual integral algebra map, incomparability proves strictness of contraction; injectivity supplies lying over and actual length-preserving prime-chain lifts. Their extended Krull dimensions are equal. No domain, Noetherianity, nontriviality or finite-dimensionality assumption is imposed. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Strict transcendence-degree drop for domain quotients | `trdeg_lt_of_surjective_of_not_injective`, `primeQuotient_trdeg_strictAnti`, `primeQuotient_trdeg_toNat_strictAnti` in `Cycles/TranscendenceDegreeDrop.lean` | The finite-type prime-quotient consequence is [Stacks, Lemma 10.116.2, Tag 06RP](https://stacks.math.columbia.edu/tag/06RP) | The generic theorem requires domains, an actual surjective noninjective algebra map over a field, and finite source transcendence degree, not finite generation. The prime-quotient specialization requires a finite-type ambient algebra but not an ambient domain. The source uses the affine dimension formula; the Lean proof instead lifts a transcendence basis and uses algebraicity to contradict a nonzero kernel, so its subsequent use in the dimension upper bound is noncircular. | FORMAL / DIRECT PROOF; SOURCE SUBCASE VERIFIED |
| Actual normalization and the dimension lower bound | `trdeg_eq_normalization_size`, `normalization_size_le_ringKrullDim`, `trdeg_toNat_le_ringKrullDim_of_finiteType` in `Cycles/NormalizationDimension.lean` | [Stacks, Lemma 10.115.4, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY); actual normalization existence already proved by Mathlib's `exists_integral_inj_algHom_of_fg` | The actual finite-variable polynomial injection is integral, rather than an abstract dimension witness. Algebraic-extension transcendence-degree invariance identifies its number of variables for a domain. The proved polynomial lower bound and integral dimension invariance then give the lower bound for every finite-type domain. The dimension comparison for a supplied normalization map itself does not require the target to be a domain. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Finite-type domain dimension and the actual fraction field | `trdeg_eq_of_isFractionRing`, `trdeg_eq_fractionRing`, `ringKrullDim_le_trdeg_toNat_of_finiteType`, `ringKrullDim_eq_trdeg_toNat_of_finiteType`, `ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType`, `spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType` in `Cycles/AffineDimension.lean` | Global-dimension conclusion of [Stacks, Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) | Actual fraction-field algebra maps and their compatible scalar tower preserve transcendence degree without a finite-type assumption. Finite type gives a finite invariant; actual prime chains give the upper dimension bound, while normalization gives the lower bound for a domain. The exact equality also concerns the topology of the actual affine spectrum. This SP42 row records the global conclusion; SP44 below subsequently proves the source's additional equality with every maximal-local dimension. | FORMAL / DIRECT PROOF; SOURCE CONCLUSION MATCHED |
| Sharp finite-variable polynomial dimension | `mvPolynomial_ringKrullDim_eq_card` in `Cycles/AffineDimension.lean` | Polynomial-dimension conclusion of [Stacks, Lemma 10.114.1, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP) | For every field and every natural n, the actual n-variable polynomial algebra has dimension n. This follows from the proved domain dimension formula and its actual polynomial transcendence degree. It does not use a `proof_wanted` declaration or assert the stronger regular-local conclusions of the source. | FORMAL / DIRECT PROOF; SOURCE SUBCASE VERIFIED |
| Actual affine point closures and residue-field values | `prime_coheight_eq_quotientDim`, `spec_point_height_eq_prime_coheight`, `spec_pointSupport_dimension_eq_quotientDim`, `primeQuotient_trdeg_eq_residueField`, `spec_pointSupport_dimension_eq_residueField_trdeg`, `spec_point_height_toNat_eq_residueField_trdeg`, `prime_residueField_trdeg_toNat_strictAnti` in `Cycles/AffineSupportDimension.lean` | Affine specialization of [Stacks, Lemma 33.20.3(6), (9c), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), using [Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) on actual prime quotients | For any commutative ring, the actual reduced point-closure carrier has the dimension of its prime quotient. For a finite-type algebra over a field, including reducible algebras, this equals the finite transcendence degree of the actual prime-localization residue field `p.asIdeal.ResidueField`. Its actual fraction-field structure over the prime quotient and compatible scalar tower prove the comparison. This is not a newly constructed comparison with a separate `Scheme.residueField` object. SP47 below subsequently proves the affine prime-spectrum unit-step law. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Subsequent affine unit step and remaining target grading | No general higher-dimensional `DimensionFunction` constructor is supplied by SP42 | [Stacks, Lemma 33.20.3(4), (7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21); the stronger uniform-chain input is [Lemma 10.114.4, Tag 00OS](https://stacks.math.columbia.edu/tag/00OS) | The affine global dimension and strict-drop theorems alone do not identify every immediate drop as one; SP47 below proves that affine law by the actual prime quotient and SP46 dimension formula. SP48 supplies the actual affine scheme-point adapter. SP49 supplies structural field actions and actual affine/open residue comparisons. SP50 identifies the height-defined values on arbitrary structural affine schemes with their scheme-residue degrees and proves affine-open agreement. SP51 supplies pointwise finiteness and chart-value agreement over a nonaffine ambient scheme. SP52 proves both common-chart laws and constructs the global field-based dimension function. SP53 supplies global point-height and closure/carrier dimension identification. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. SP43 and SP44 below add polynomial and finite-type-domain maximal-local equality. A uniform-chain theorem or catenarity theorem is not inferred from the global or maximal-local equality. | SOURCE IDENTIFIED / OPEN |

### Polynomial maximal heights and actual closed-point stalks (A11ab / SP43)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Actual prime extension and a strict extra height step | `polynomial_comap_map_C`, `polynomialPrimeExtension`, `polynomialPrimeExtension_height_le`, `polynomial_map_C_not_isMaximal`, `polynomial_map_comap_C_lt`, `polynomial_primeHeight_comap_add_one_le` in `Cycles/PolynomialPrimeHeight.lean` | Direct proof from actual ideal extension/contraction, the polynomial quotient isomorphism and prime-chain height | For every commutative ring R, extension along the constant-polynomial map is an order embedding on primes. No extended ideal is maximal, since its actual quotient is a polynomial ring and hence is not a field. The extension of a polynomial maximal ideal's contraction is strictly smaller, so the contraction height plus one is at most the maximal height. No Jacobson, domain, Noetherian or finiteness assumption is imposed. | FORMAL / DIRECT PROOF |
| Heights and actual maximal localizations of polynomial algebras | `mvPolynomial_primeHeight_eq_card_of_isMaximal`, `mvPolynomial_height_eq_card_of_isMaximal`, `mvPolynomial_localization_dimension_of_isMaximal` in `Cycles/PolynomialMaximalHeight.lean` | Local-dimension conclusion of [Stacks, Lemma 10.114.1, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP); maximal contraction is the polynomial specialization of [Proposition 10.35.19(2), Tag 00GB](https://stacks.math.columbia.edu/tag/00GB) | For any field and every natural n, every maximal ideal of the actual n-variable polynomial algebra has height n, and its actual prime localization has dimension n. The lower bound is proved by Jacobson maximal contraction and the preceding generic height step; SP42 supplies the sharp upper bound. This includes zero variables and non-rational maximal ideals. The source's additional generator count and regular-locality conclusions are not claimed. | FORMAL / DIRECT PROOF; SOURCE CONCLUSION MATCHED |
| Actual closed-point structure-sheaf stalks and coheight | `mvPolynomial_stalk_dimension_of_isMaximal`, `mvPolynomial_stalk_dimension_of_isClosed`, `mvPolynomial_closedPoint_coheight` in `Cycles/PolynomialClosedPointDimension.lean` | Direct use of the actual affine stalk's localization structure and SP36's proved scheme-point coheight/local-dimension comparison; preceding [Stacks, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP) | Closedness supplies maximality of the actual affine prime. Its structure-sheaf stalk has dimension n, and the same point has coheight n in the scheme's closure-inclusion order. No independent stalk proxy or residue-field-degree-one input is introduced. Scheme-point coheight here is not the point height measuring its closed-carrier dimension. | FORMAL / DIRECT PROOF |
| Further maximal-local and grading comparisons | SP43 gives the polynomial case; SP44 below supplies finite-type-domain maximal-local equality | The stronger domain conclusion is [Stacks, Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0); uniform prime-chain lengths are [Lemma 10.114.3, Tag 00OR](https://stacks.math.columbia.edu/tag/00OR); immediate-specialization grading is [Lemma 33.20.3(7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | SP44 below proves the required normal-base going-down and normalization height comparison, extending the polynomial result to finite-type domains. Polynomial maximal heights alone do not prove regularity, uniform lengths of saturated chains or a unit-step law between arbitrary consecutive primes. SP52 supplies the global field-based dimension function. SP49 supplies the structural residue-field action and actual affine/open algebra comparisons; SP53 identifies global point-height and closure/carrier dimensions. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | SOURCE IDENTIFIED / OPEN |

### Normal-base going down and affine maximal local dimensions (A11ac / SP44)

| Statement | Active Lean objects | Source | Exact scope | Status |
| --- | --- | --- | --- | --- |
| Actual ideal-sensitive monic annihilators | `exists_monic_annihilator_coeff_mem_pow_of_mem_map`, `exists_monic_annihilator_of_mem_map` in `CommutativeAlgebra/IntegralIdealPolynomial.lean` | [Stacks, Lemma 10.38.4, Tag 00H5](https://stacks.math.columbia.edu/tag/00H5), with the ideal-power convention of [Definition 10.38.1, Tag 00H2](https://stacks.math.columbia.edu/tag/00H2) | For any integral algebra of commutative rings and y in the actual extension of an ideal I, a finite membership witness generates a finite integral subalgebra. The ideal-sensitive Cayley--Hamilton theorem gives a monic annihilator F with coefficient i in I^(natDegree F−i); in particular every lower coefficient lies in I. The whole algebra need not be finite, a domain, normal or Noetherian. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Monic prime-coefficient comparison, including scaling | `monic_map_eq_X_pow_of_lower_coeff_zero`, `coeff_mem_prime_of_monic_dvd_scaled`, `coeff_mem_prime_of_monic_dvd` in `CommutativeAlgebra/MonicPrimeCoefficients.lean` | Prime-ideal version of the monic-divisor coefficient comparison in [Stacks, Lemma 10.38.5, Tag 00H6](https://stacks.math.columbia.edu/tag/00H6), proved directly | For a prime p of any commutative ring, a monic divisor g of F(aX), with F monic, its lower coefficients in p and a outside p, also has its lower coefficients in p. The actual prime quotient and its fraction field reduce the assertion to monic divisors of a power of X. The unscaled result takes a=1. Unlike the source's ambient subring-of-a-field presentation, this direct prime-quotient proof does not require the original coefficient ring to be a domain. | FORMAL / DIRECT PROOF; SOURCE COMPARISON VERIFIED |
| Constructed normal-base going down | `mem_prime_of_mul_mem_map_of_isIntegrallyClosed`, `hasGoingDown_of_isIntegrallyClosed` in `CommutativeAlgebra/NormalGoingDown.lean` | [Stacks, Proposition 10.38.7, Tag 00H8](https://stacks.math.columbia.edu/tag/00H8); normal-base minimal polynomial comparison [Lemma 10.38.6, Tag 00H7](https://stacks.math.columbia.edu/tag/00H7) | An injective integral map of domains with integrally closed base satisfies going down. Normal-base minimal-polynomial divisibility and the preceding scaled coefficient theorem prove scalar cancellation; a prime disjoint from the constructed multiplicative set gives an actual prime below the selected terminal prime and with the required contraction. No finiteness, Noetherianity, separability, normality of the target or separate going-down input is used. The theorem is existence, not uniqueness of prime lifts. | FORMAL / DIRECT PROOF; SOURCE SCOPE VERIFIED |
| Prime heights and actual polynomial normalizations | `primeHeight_eq_under_of_isIntegral_of_hasGoingDown`, `normalization_primeHeight_eq_size` in `Cycles/NormalizationLocalDimension.lean`; reused `NormalizationInertia.primeHeight_under_le_of_hasGoingDown` | Direct chain comparison using integral incomparability and going down; normalization [Stacks, Lemma 10.115.4, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY), polynomial maximal heights [Lemma 10.114.1, Tag 00OP](https://stacks.math.columbia.edu/tag/00OP) | The generic height comparison uses integrality and going down on commutative rings, without domain, injectivity or finite-dimensionality assumptions. For an actual injective integral map from an s-variable polynomial algebra over a field into a domain, the newly proved normal-base theorem supplies going down and every maximal ideal upstairs has height s. This specialization does not require the upper domain to be finite type or normal. No integrality of a map between two selected prime localizations is assumed. | FORMAL / DIRECT PROOF; SOURCE INPUTS MATCHED |
| Every maximal localization of a finite-type domain has full dimension | `primeHeight_eq_trdeg_toNat_of_isMaximal`, `height_eq_trdeg_toNat_of_isMaximal`, `localization_dimension_eq_of_isMaximal` in `Cycles/NormalizationLocalDimension.lean` | Maximal-local conclusion of [Stacks, Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0), together with SP42's global/fraction-field equality | Over any field, a finite-type domain has maximal height and actual maximal-local dimension equal to its global dimension and finite fraction-field transcendence degree. The proof uses actual Noether normalization and the preceding height comparison. There is no normality, separability or rational-maximal-point assumption on the domain. The proof does not invoke the uniform-chain theorem used by the cited source's proof. | FORMAL / DIRECT PROOF; FULL SOURCE CONCLUSION MATCHED |
| Actual affine closed-point stalks and coheight | `affine_stalk_dimension_of_isMaximal`, `affine_stalk_dimension_of_isClosed`, `affine_closedPoint_coheight_eq_trdeg` in `Cycles/AffineClosedPointDimension.lean` | Direct actual stalk-localization and SP36 point-coheight transport of the preceding maximal-local result | On the actual spectrum of any finite-type domain over a field, every closed point has structure-sheaf stalk dimension equal to the global ring dimension. Its scheme-point coheight equals the finite transcendence degree of the ambient domain, not the dimension of the point's closed carrier. Closedness supplies maximality; no replacement stalk or degree-one residue extension is introduced. | FORMAL / DIRECT PROOF |
| Subsequent consecutive-prime law and remaining target grading | No uniform-chain or general higher-dimensional dimension-function constructor is supplied by SP44 | [Stacks, Lemma 10.114.3, Tag 00OR](https://stacks.math.columbia.edu/tag/00OR); [Lemma 33.20.3(7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | SP47 below combines the subsequent affine prime formula with the actual quotient-prime cover to establish the affine unit drop. SP48 supplies the actual affine scheme-point dimension functions. SP52 supplies the common-chart laws and global field-based dimension function. SP53 identifies global point-height and closure/carrier dimensions. SP54 proves the integral chain-codimension/degree formula. SP55 supplies relation reindexing and top-degree vanishing. SP56 supplies general rational coefficient extension. Uniform interval-chain results and reducible/componentwise targets remain separate. No regular-local or general intersection theorem is inferred from the maximal-local dimension result. | SOURCE IDENTIFIED / OPEN |

### Lifted quotient normalization and actual generic localization (A11ad / SP45)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Lift an actual prime-quotient normalization | `quotientPolynomialLift`, `quotient_comp_quotientPolynomialLift`, `quotientPolynomialLift_injective`, `polynomial_map_nonZeroDivisors_disjoint`, `exists_lifted_residue_normalization` in `Cycles/ResidueNormalizationLift.lean` | Noether normalization [Stacks, Lemma 10.115.4, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY), applied to the actual domain B/q; the polynomial lift is proved directly | A finite-type algebra B need not be a domain: its actual prime quotient is. Choose representatives of the normalization variables and evaluate them in B. The quotient composite is exactly the original normalization, so the lifted map is injective and its nonzero polynomial images avoid q. Integrality concerns the quotient composite, not the lifted map into B. The lifting helpers themselves allow an arbitrary quotient; the normalization-existence endpoint requires a field, finite type and a prime ideal. | FORMAL / DIRECT PROOF; SOURCE INPUT MATCHED |
| The actual generic-fiber algebra and finite type | `genericFiberAlgebra`, `genericFiberAlgebra_algebraMap_eq`, `genericFiberAlgebra_isScalarTower`, `genericFiber_finiteType`, `genericFiber_isDomain`, `genericFiber_localization_injective`, `genericFiber_baseField_injective`, `genericFiber_isScalarTower_base` in `CommutativeAlgebra/GenericFiberAlgebra.lean` | Direct use of Mathlib's `localizationAlgebra`, `Algebra.isPushout_of_isLocalization` and finite type under actual pushout | The carrier is any actual localization of an R-algebra S at the image of R's non-zero-divisors; the integrated theorem uses the literal `Localization` carrier. Its fraction-ring algebra is the existing localization map, installed explicitly, and the scalar towers are proved. The tensor-product equivalence proves the pushout's finite-type property without replacing that carrier. Finite type requires no domain assumption; domain and injectivity endpoints use an injective base map and domain S. No global algebra instance or abstract substitute fiber is introduced. | FORMAL / DIRECT PROOF |
| Maximality through the actual localized quotient | `residueLocalization_map_isMaximal` in `CommutativeAlgebra/ResidueLocalization.lean` | Localization and quotient [Stacks, Proposition 10.9.14, Tag 00CT](https://stacks.math.columbia.edu/tag/00CT); localization preserves integrality, the forward direction of [Lemma 10.36.11, Tag 0307](https://stacks.math.columbia.edu/tag/0307); a domain integral over a field is a field, [Lemma 10.36.19(2), Tag 00GS](https://stacks.math.columbia.edu/tag/00GS) | For a domain R and an actual injective integral map R→S/q, localize at the images of nonzero R-elements. The actual localization of S/q is a domain integral over Frac(R), hence a field. The constructed surjection from the localization of S has exactly the extended q as kernel. No domain, finite-type, Noetherian, normality or separability assumption on S is needed. This uses only the localization-preserves-integrality consequence of 0307, not a newly proved full integral-closure comparison. | FORMAL / DIRECT PROOF; SOURCE CONCLUSIONS MATCHED |
| Exact contraction, primality and prime height | `residueLocalization_comap_map`, `residueLocalization_map_isPrime`, `residueLocalization_primeHeight_map` in `CommutativeAlgebra/ResidueLocalization.lean` | Direct actual localization prime correspondence; Mathlib `IsLocalization.comap_map_of_isPrime_disjoint`, `IsLocalization.isPrime_of_isPrime_disjoint`, and `IsLocalization.primeHeight_comap` | Only the injection R→S/q is needed beyond domain R and prime q: it proves denominator disjointness. Integrality is not required for these three endpoints. The correspondence restricts to an order isomorphism of the complete lower prime intervals, so full height is preserved, not merely bounded. Reducible or nonreduced S is allowed. | FORMAL / DIRECT PROOF |
| Constructed localization of every finite-type prime quotient | `residueNormalization_localization`, `exists_residueNormalization_localization`, `primeHeight_eq_residueNormalization_trdeg` in `Cycles/ResidueNormalizationLocalization.lean` | The preceding constructed maps and [Stacks, Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0), whose maximal-height conclusion was proved in SP44 | For any finite-type k-algebra B and prime q, the actual lifted normalization P→B gives B′ finite type over K=Frac(P), with q′ maximal, exact contraction and preserved height. Only the last endpoint adds domain B, obtains domain B′, and applies the previously proved maximal-height theorem over K to conclude ht(q)=trdeg_K(B′). It does not apply that theorem over k or assume K finite type over k. | FORMAL / DIRECT PROOF; SOURCE APPLICATION MATCHED |
| Original-field comparison and remaining grading scope | SP46 below supplies the transcendence-degree localization and tower assembly left by SP45 | The local formula is [Stacks, Lemma 10.116.3, Tag 00P1](https://stacks.math.columbia.edu/tag/00P1); the intended scheme dimension function is [Lemma 33.20.3(7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | SP46 proves ht(q)+trdeg_k(B/q)=trdeg_k(B) for finite-type domains, deriving finite trdeg(K/k) from the polynomial variable count rather than a finite-type assumption on K. For possibly reducible B, 00P1 instead uses the local topological dimension dim_x(Spec B), not the global dimension of B; that broader comparison is not asserted. SP47 below proves the affine consecutive-prime unit-step consequence. SP48 supplies the actual affine dimension functions. SP49 supplies the structural scheme-residue actions and actual affine/open comparisons. SP52 supplies the common-chart laws and global field-based dimension function. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | DOMAIN CASE FORMAL IN SP46 / FURTHER COMPARISONS OPEN |

### Localization transcendence degree and the affine prime formula (A11ae / SP46)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Cardinal transcendence degree of an actual localization | `lift_trdeg_eq_of_isLocalization`, `trdeg_eq_of_isLocalization`, `trdeg_toNat_eq_of_isLocalization` in `Cycles/LocalizationTranscendenceDegree.lean` | Tower additivity [Stacks, Lemma 9.26.5, Tag 030H](https://stacks.math.columbia.edu/tag/030H), via Mathlib's explicitly tagged faithful domain-algebra generalization `lift_trdeg_add_eq`; actual localization algebraicity and injectivity | For a domain B over a field k and an actual localization B′ at a submonoid of non-zero-divisors, the compatible k→B→B′ tower preserves the full transcendence-degree cardinal. The localization's domain and injectivity properties are proved from the denominator condition. The comparison allows different carrier universes; the same-universe and `toNat` formulas are corollaries. No finite-type or finite-transcendence-degree premise is needed, and the `toNat` corollary is not a finiteness assertion. The source itself states field towers; the pinned library proves the domain-algebra version actually used here. | FORMAL / DIRECT PROOF; SOURCE GENERALIZATION IDENTIFIED |
| The original-field sum on a literal polynomial generic fiber | `polynomial_genericFiber_trdeg_toNat_add` in `Cycles/AffinePrimeDimension.lean` | Tower additivity [Stacks, Lemma 9.26.5, Tag 030H](https://stacks.math.columbia.edu/tag/030H); the previously proved actual polynomial fraction-field comparison | For a finite-type domain B over a field k and any injective polynomial k-algebra map P→B, the actual generic localization B′ and K=Frac(P) give n+trdeg_K(B′)=trdeg_k(B). The actual k→P→K→B′ scalar towers commute. The polynomial variable count proves trdeg_k(K)=n, while finite type over K proves the other summand finite; only then is cardinal addition passed to natural numbers. Neither the map P→B nor a quotient composite is assumed integral in this helper. K is not assumed finite type over k. | FORMAL / DIRECT PROOF; SOURCE APPLICATION MATCHED |
| Every prime of a finite-type domain: original-field dimension formula | `primeHeight_add_quotient_trdeg_eq`, `height_add_quotient_trdeg_eq`, `primeHeight_add_residueField_trdeg_eq` in `Cycles/AffinePrimeDimension.lean` | Domain specialization of [Stacks, Lemma 10.116.3, Tag 00P1](https://stacks.math.columbia.edu/tag/00P1); residue-quotient equality already proved in SP42 | The actual quotient normalization identifies n with trdeg_k(B/q), and SP45 identifies ht(q) with trdeg_K(B′). The preceding tower sum therefore proves ht(q)+trdeg_k(B/q)=trdeg_k(B), including the equivalent actual prime-localization residue-field formula. There is no normality, maximality, separability, rational-point or separately assumed finite-height premise. The source's proof uses uniform chains; this Lean proof instead assembles the actual localization and already proved maximal-height comparison. The source allows reducible algebras and then uses dim_x(Spec B), not global dim B; only its domain specialization is matched here. | FORMAL / DIRECT PROOF; SOURCE DOMAIN CASE MATCHED |
| Actual quotient and prime-localization dimensions | `height_add_quotient_dimension_eq`, `localization_dimension_add_quotient_dimension_eq` in `Cycles/AffinePrimeDimension.lean` | [Stacks, Lemma 10.116.3, Tag 00P1](https://stacks.math.columbia.edu/tag/00P1), domain case, with the proved global dimension/transcendence-degree equality [Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) | The constructed formula is translated to the actual quotient ring and actual `Localization.AtPrime q`: dim(B_q)+dim(B/q)=dim(B). No chosen replacement local ring is introduced. The residue-field endpoint uses `Ideal.ResidueField`, not a newly asserted comparison with a separate scheme residue-field object. SP47 below supplies the affine consecutive-prime unit step. SP48 supplies the actual affine scheme-point grading. SP49 supplies the structural field action and actual affine/open scheme-residue comparisons. SP52 proves the common-chart laws and constructs the global field-based dimension function. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FORMAL / DIRECT PROOF; SOURCE DOMAIN CASE MATCHED |

### Consecutive affine primes and the unit drop (A11af / SP47)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| The actual quotient of a consecutive prime pair | `primeQuotient_map_isPrime`, `primeQuotient_bot_covBy_map`, `primeQuotient_primeHeight_eq_one_of_covBy` in `CommutativeAlgebra/PrimeQuotientCover.lean` | Direct proof using Mathlib's actual `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` and prime-chain height | For primes p and q of any commutative ring, p≤q makes the actual image of q in B/p prime. A cover p⋖q in `PrimeSpectrum B` becomes a cover of zero in the actual domain quotient; its upper prime therefore has height one. The cover concerns prime ideals, not all ideals. No field, ambient domain, Noetherianity, finite type, catenarity or supplied height-one hypothesis is needed. | FORMAL / DIRECT PROOF |
| Exact unit drop for prime quotients and their residue fields | `primeQuotient_trdeg_toNat_add_one_of_covBy`, `prime_residueField_trdeg_toNat_add_one_of_covBy` in `Cycles/ConsecutivePrimeDimension.lean` | Affine algebraic form of [Stacks, Lemma 33.20.3(7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21); SP46's domain prime formula and Mathlib's actual `DoubleQuot.quotQuotEquivQuotOfLEₐ` | Over any field, a finite-type ambient algebra may be reducible or nonreduced. The actual lower-prime quotient is a finite-type domain, so SP46 applies to its actual height-one upper prime. The double-quotient k-algebra equivalence identifies the remaining quotient with B/q and gives trdeg_k(B/q)+1=trdeg_k(B/p). The actual `Ideal.ResidueField` comparison supplies the same unit drop for residue degrees. Only finite values are converted to natural numbers; no scheme residue-field replacement or chart transport is asserted. The source allows all locally algebraic schemes, without irreducibility or equidimensionality in part (7). | FORMAL / DIRECT PROOF; SOURCE AFFINE CASE MATCHED |
| Quotient dimensions and the remaining scheme comparison | `primeQuotient_dimension_add_one_of_covBy` in `Cycles/ConsecutivePrimeDimension.lean`; SP52 subsequently constructs the global dimension function over a field | [Stacks, Lemma 33.20.3(6), (7), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) and the domain dimension comparison [Lemma 10.116.1, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) | The actual quotient rings satisfy dim(B/q)+1=dim(B/p). This is not a claim that ambient stalk dimensions rise by one for arbitrary reducible B: the source's separate part (11) requires irreducibility or equidimensionality. SP48 transports the prime-spectrum law into the actual affine scheme-point order and constructs the affine dimension functions. SP49 constructs the structural k-algebra on actual scheme-stalk residue fields, the compatible affine algebra equivalence and general open-immersion residue-degree invariance. SP50 identifies the height-defined value on arbitrary structural affine schemes with this actual residue degree and proves affine-open agreement. SP51 supplies nonaffine pointwise finiteness and chart-value agreement. SP52 proves both common-chart laws and constructs the global field-based dimension function. SP53 subsequently proves global point-height and closure/carrier dimension identification. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. No general uniform-chain, catenarity or regular-local theorem is asserted by this checkpoint. | FORMAL / DIRECT PROOF; SOURCE AFFINE CASE MATCHED |

### Constructed dimension functions on actual affine schemes (A11ag / SP48)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Reused actual affine point-order reversal | `specPointOrderIso` in `Cycles/AffineSupportDimension.lean`, now public | Direct actual scheme/prime specialization comparison, reused from SP42 | The existing identity-on-points order isomorphism identifies the scheme's closure-inclusion order with the dual of prime-ideal inclusion. It applies to every commutative ring. Exposing the existing definition introduces neither a duplicate order comparison nor a new point carrier. | FORMAL / DIRECT PROOF |
| Residue-degree dimension function on a literal affine spectrum | `DimensionFunction.ofSpecFiniteType`, `DimensionFunction.ofSpecFiniteType_apply`, `DimensionFunction.ofSpecFiniteType_eq_pointHeight`, `DimensionFunction.ofSpecFiniteType_nonneg`, `supportDegree_ofSpecFiniteType_eq_iff`, `fundamentalCycle_mem_ofSpecFiniteType_iff` in `Cycles/AffineDimensionFunction.lean` | Both defining conditions of [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9); affine value, strictness and unit-step conclusions of [Lemma 33.20.3(6), (7), (9c), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | For a finite-type algebra A over any field k, the actual `Spec A` function is the integer cast of the finite transcendence degree of `Ideal.ResidueField`. SP42 strict anti-monotonicity and SP47's cover law prove both axioms after the actual order reversal. The function equals finite integer scheme-point height and is nonnegative. Actual carrier degree equals its topological dimension; for n∈ℕ, the exact existing-fundamental-cycle membership iff additionally requires nontrivial semiring coefficients. Ambient integrality, reducedness, normality and a dimension-at-most-one bound are not required. | FORMAL / DIRECT PROOF; SOURCE AFFINE CASE MATCHED |
| Structural affine scheme and its actual carrier grading | `DimensionFunction.ofAffineLocallyOfFiniteType`, `DimensionFunction.ofAffineLocallyOfFiniteType_apply`, `DimensionFunction.ofAffineLocallyOfFiniteType_nonneg`, `supportDegree_ofAffineLocallyOfFiniteType_eq_iff`, `fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff` in `Cycles/AffineSchemeDimensionFunction.lean` | The affine case of [Stacks, Lemma 33.20.3, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), with actual formal transport of the preceding constructor | An actual affine X and structural p:X→Spec k locally of finite type supply the finite-type k-algebra on global sections. The proof uses X.isoSpec and existing dimension-function restriction along that isomorphism, then identifies the transported function with actual integer point height. Its value is the definition, while both dimension-function laws are proved by this geometric transport. No independently supplied sections algebra, dimension function or grading law is assumed; the empty affine scheme is allowed. Actual carrier-degree and fundamental-cycle iff statements use n∈ℕ and nontrivial coefficients for the latter. SP49 supplies the compatible k-action and actual affine/open scheme-residue algebra comparisons. SP50 identifies this height-defined value for arbitrary structural affine X with its actual scheme-residue degree and proves affine-open agreement. SP51 compares chart values and proves pointwise finiteness in a nonaffine ambient scheme. SP52 proves both common-chart laws and constructs the global field-based dimension function. SP53 proves its global point-height and closure/carrier dimension comparison, including qualified open-height invariance over the structural field. No unrestricted open-immersion preservation of absolute point height is asserted. | FORMAL / DIRECT PROOF; SOURCE AFFINE CASE MATCHED |

### Structural actions and actual affine residue-field comparisons (A11ah / SP49)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Structural action on the existing scheme residue field | `residueFieldBaseMap`, `residueFieldBaseAlgebra`, `residueFieldBaseAlgebra_algebraMap` in `Cycles/StructuralResidueField.lean` | Residue-field and local-morphism definitions in [Stacks, Definition 26.2.1, Tag 01HB](https://stacks.math.columbia.edu/tag/01HB); actual spectrum global sections in [Lemma 26.5.4(1), Tag 01HV](https://stacks.math.columbia.edu/tag/01HV) | For a scheme X with actual p:X→Spec k, pull back canonical global constants and evaluate in the existing residue field of the actual structure-sheaf stalk. This independently constructs the k-algebra; it is an ordinary definition installed locally, never a global instance or a transferred action from a replacement carrier. The base k is any commutative ring. No affine-source, finite-type, domain, reducedness or normality hypothesis is needed. | FORMAL / DIRECT PROOF; SOURCE DEFINITIONS MATCHED |
| Naturality and open-immersion base-algebra equivalence | `residueFieldBaseMap_comp`, `residueFieldBaseAlgHom`, `residueFieldBaseAlgHom_apply`, `residueFieldBaseAlgEquivOfIsOpenImmersion`, `residueFieldBaseAlgEquivOfIsOpenImmersion_apply` in `Cycles/StructuralResidueField.lean` | Direct proofs from Mathlib's actual `Scheme.Γevaluation_naturality` and the open-immersion residue-field isomorphism; local maps as in [Stacks, Definition 26.2.1, Tag 01HB](https://stacks.math.columbia.edu/tag/01HB) | For f:X→Y and p:Y→Spec k, the actual residue map κ_Y(fx)→κ_X(x) commutes with the structural actions for p and f≫p. The resulting algebra homomorphism keeps this underlying map. An open immersion gives a k-algebra equivalence by its actual stalk/residue-field isomorphism, with scalar compatibility proved. No independently supplied compatibility equation or global chart-gluing theorem is used. | FORMAL / DIRECT PROOF |
| Actual affine residue carrier and compatibility with constants | `specResidueFieldEquiv`, `specResidueFieldEquiv_evaluation`, `specResidueFieldAlgEquiv`, `specResidueFieldAlgEquiv_apply` in `Cycles/AffineResidueField.lean` | Canonical affine stalk and global-section identifications in [Stacks, Lemma 26.5.4(1), (6), Tag 01HV](https://stacks.math.columbia.edu/tag/01HV), followed by the actual residue quotient of [Definition 26.2.1, Tag 01HB](https://stacks.math.columbia.edu/tag/01HB) | The ring equivalence is the actual `IsLocalRing.ResidueField.mapEquiv` of `StructureSheaf.stalkIso`, between `(Spec A).residueField x` and the separate `x.asIdeal.ResidueField`. The equality on every A-constant proves that this equivalence commutes with the independent structural k-action for Spec(algebraMap k A), hence is a k-algebra equivalence. Both k and A may be arbitrary commutative rings, with an actual k-algebra structure on A. The two residue carriers are compared, not declared definitionally identical. | FORMAL / DIRECT PROOF; SOURCE COMPARISON MATCHED |
| Actual structural residue degree and the existing affine grading | `spec_schemeResidueField_trdeg_eq`, `spec_schemeResidueField_trdeg_lt_aleph0`, `DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg`, `residueFieldBase_trdeg_eq_of_isOpenImmersion` in `Cycles/AffineResidueFieldDimension.lean` | Affine value in [Stacks, Lemma 33.20.3(6), (9c), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21); direct invariance of transcendence degree under the proved k-algebra equivalences | Over any field, the actual affine spectrum comparison and any open-immersion comparison preserve the full transcendence-degree cardinal, with no finite-type premise. For a finite-type affine algebra, the actual prime quotient proves the scheme residue degree finite before conversion to a natural number or integer. Its integer value equals the existing literal-spectrum dimension function; neither that function nor the residue-field action is redefined. SP50 identifies the height-defined dimension function on arbitrary structural affine X with this actual scheme-residue degree and proves affine-open agreement. SP51 supplies nonaffine pointwise finiteness and chart-value agreement. SP52 proves both common-chart laws and constructs the global function. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FORMAL / DIRECT PROOF; SOURCE AFFINE VALUE MATCHED |

### Arbitrary structural affine values and open-immersion agreement (A11ai / SP50)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Reused actual point-height isomorphism comparison | `point_height_iso` in `Cycles/AffineSchemeDimensionFunction.lean`, now public | Direct actual scheme-carrier isomorphism proof, reused from SP48 | An actual scheme isomorphism preserves point height by its induced isomorphism on the existing reduced point-closure carriers. No field, affine, finite-dimensionality or finite-type premise is needed. Exposing the existing theorem adds no duplicate order, height or carrier object. | FORMAL / DIRECT PROOF |
| Structural residue degree on an arbitrary affine scheme | `affine_schemeResidueField_trdeg_lt_aleph0`, `DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg` in `Cycles/AffineSchemeResidueDegree.lean` | Affine form of [Stacks, Lemma 33.20.3(6), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), applied to actual reduced point closures; canonical affine sections/stalks in [Lemma 26.5.4(1), (6), Tag 01HV](https://stacks.math.columbia.edu/tag/01HV) | For affine X with actual p:X→Spec k locally of finite type, X.isoSpec and the transported structural map supply the actual finite-type sections algebra. Equality of that map with its spectrum presentation makes SP49's residue comparison compatible with the independently defined structural action on X. The actual residue transcendence degree is finite before numeric conversion, and equals the existing height-defined affine dimension function. No separately supplied sections algebra, base compatibility, domain, reducedness, normality or nonemptiness premise is used. This is not a finite-type-algebra claim for the residue field or a redefinition of the dimension function. | FORMAL / DIRECT PROOF; SOURCE AFFINE VALUE MATCHED |
| Agreement under an actual open immersion between affine schemes | `DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion` in `Cycles/AffineSchemeResidueDegree.lean` | Direct consequence of the preceding value formula and SP49's proved structural residue-field algebra equivalence | For affine X and Y, an open immersion f:X→Y and a locally finite-type p:Y→Spec k, the existing dimension functions for f≫p and p agree at x and f(x). Both affine value formulas are evaluated using their actual structural actions. SP51 supplies chart-value agreement and pointwise residue-degree finiteness in a nonaffine ambient scheme. SP52 proves both common-chart laws and constructs the global function. SP53 proves the global height and carrier-dimension comparison and qualified open-height invariance over the structural field. SP54 supplies actual integral chain codimension and complementary degree. No unrestricted open-height invariance on arbitrary schemes is asserted. | FORMAL / DIRECT PROOF |

### Pointwise residue finiteness and affine-chart agreement (A11aj / SP51)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Finite actual structural residue degree at every point | `schemeResidueField_trdeg_lt_aleph0` in `Cycles/ChartResidueDegree.lean` | Pointwise affine reduction in [Stacks, Lemma 33.20.3, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21); the actual affine residue comparison proved in SP49--SP50 | For actual p:X→Spec k locally of finite type over a field, the existing affine cover supplies one chart through each selected point. Its finite residue degree transfers through the actual open-immersion k-algebra comparison. There is no affine-X, quasi-compactness, finite-subcover, global-dimension-bound, integrality or reducedness premise. Only transcendence degree is proved finite; the residue field is not asserted finite type as a k-algebra. This uses the source's local setup, not its stronger catenarity, uniform-chain or stalk-dimension statements. | FORMAL / DIRECT PROOF; SOURCE LOCAL SCOPE MATCHED |
| Existing affine-chart values equal the ambient residue-degree value | `affineChart_dimension_eq_schemeResidueField_trdeg` in `Cycles/ChartResidueDegree.lean` | Direct consequence of SP50's affine value formula and SP49's actual open-immersion residue-degree invariance | For any actual affine open immersion i:U→X, use the structural map i≫p on U and p on X. The already constructed affine dimension function at u is the integer value of the actual structural residue degree at i(u). The ambient X need not be affine. Pointwise finiteness is independently proved before numeric conversion; no new global dimension function is defined. | FORMAL / DIRECT PROOF |
| Equal ambient images give equal chart values | `affineChart_dimension_eq_of_eq_image` in `Cycles/ChartResidueDegree.lean` | Direct equality transport of the preceding ambient-value comparison | For two actual affine open immersions into the same locally finite-type X, equality of their point images gives equality of their existing affine dimension values. A local expression transports the dependent actual residue field and its structural action together. No identification of unrelated field carriers, affine-intersection premise, prescribed overlap equation or gluing package is assumed. SP52 subsequently proves both common-chart laws and constructs the global dimension function. SP53 proves the global point-height and closure/carrier dimension comparisons. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FORMAL / DIRECT PROOF |

### Constructed global dimension function over a field (A11ak / SP52)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| An actual common affine chart for a specialization pair | `exists_isAffineOpen_mem_of_le` in `Cycles/FieldDimensionFunction.lean` | Direct use of the scheme affine-open basis and stability of open sets under generalization | For any actual scheme and two points related in the closure-inclusion order, an affine neighbourhood of the specialized point also contains the generalization. No base field, finite-type, quasi-compactness, irreducibility or finite-dimensionality assumption is used by this helper. | FORMAL / DIRECT PROOF |
| The global structural residue-degree dimension function | `DimensionFunction.ofLocallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_apply`, `DimensionFunction.ofLocallyOfFiniteType_nonneg` in `Cycles/FieldDimensionFunction.lean` | Both conditions of [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9); residue-degree strictness and unit step in [Lemma 33.20.3(7), (9c), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21) | For actual p:X→Spec k locally of finite type, the existing structural residue degree gives nonnegative integer values, with pointwise finiteness supplied by SP51. A common affine chart and the actual specialization and cover comparisons transfer both laws from the already constructed affine function. SP51's chart-value equality transfers both laws back, constructing the existing DimensionFunction structure without an external law or gluing package. X need not be affine, quasi-compact, integral, reduced, normal or globally finite-dimensional. The source's catenarity, uniform-chain and ambient-stalk dimension statements are not used or claimed here. | FORMAL / DIRECT PROOF; SOURCE DIMENSION-FUNCTION LAWS MATCHED |
| Affine object equality and unrestricted open-source value compatibility | `DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion` in `Cycles/FieldDimensionFunction.lean` | Direct use of SP50's structural affine value formula and SP49's actual open-immersion residue-field algebra equivalence | On affine X the entire dimension-function object equals the previous affine construction, not just a selected value. For any open immersion f:X→Y over the structural field, values agree for f≫p and p without affineness of X or Y. This is invariance of the proved structural grading, not an unrestricted claim about absolute point height on arbitrary schemes. SP53 identifies the global grading with actual finite point heights and point-closure/carrier dimensions. SP54 proves actual chain codimension versus complementary degree on integral schemes. SP55 reindexes the existing principal relations by codimension and proves top-degree relation vanishing. SP56 supplies general rational coefficient extension and the scalar-extension quotient comparison. SP57 supplies representative-preserving rational naturality for closed immersions and isomorphisms. SP61–SP62 supply actual open relation preservation and integral/rational quotient restriction with coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity. Closed-complement localization, geometric target identification and broader operation laws remain separate. | FORMAL / DIRECT PROOF |

### Global point heights and geometric carrier degrees (A11al / SP53)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Actual finite point height and reduced closure dimension | `point_height_eq_ofLocallyOfFiniteType`, `point_height_ne_top_of_locallyOfFiniteType`, `DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight`, `pointSupport_dimension_eq_ofLocallyOfFiniteType` in `Cycles/FieldSupportDimension.lean` | Point-closure form of [Stacks, Lemma 33.20.3(6), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21); direct comparison with the existing actual point-support geometry | For any actual p:X→Spec k locally of finite type, nonnegative strictness bounds actual point height by the constructed residue degree. One actual affine chart supplies the reverse inequality through its finite height, affine normalization and strict point map. Heights are finite, and the existing global function equals literal integer point height. The already proved actual reduced-closure comparison gives equality in the full extended dimension type, not an equality obtained by discarding an infinite value. No affine-X, quasi-compactness, finite-subcover, global-dimension-bound or ambient integral/reduced/normal assumption is used. | FORMAL / DIRECT PROOF; SOURCE POINT-CLOSURE VALUE MATCHED |
| Existing carrier degree and fundamental-cycle homogeneity | `supportDegree_ofLocallyOfFiniteType_eq_iff`, `fundamentalCycle_mem_ofLocallyOfFiniteType_iff` in `Cycles/FieldSupportDimension.lean` | Equality of clauses (1) and (2) of [Stacks, Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO), for the point base with value zero in [Example 42.7.2, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM) | Every actual integral closed carrier is its generic point's existing reduced closure, so its constructed support degree equals its finite actual dimension. The exact exported degree iff uses n∈ℕ; the coefficient-one cycle iff additionally requires nontrivial semiring coefficients. The cycle module and homogeneous submodule are unchanged. This is the field-base degree/dimension comparison, not the source's arbitrary Jacobson-base generality or its additional closed-point stalk-dimension clause. There is no uniform global dimension bound on X. | FORMAL / DIRECT PROOF; SOURCE FIELD-BASE CARRIER COMPARISON MATCHED |
| Qualified actual point-height invariance under open immersion | `point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType` in `Cycles/FieldSupportDimension.lean` | Direct consequence of the preceding global height formula and SP52's structural open-value invariance | For p:Y→Spec k locally of finite type and any actual open immersion f:X→Y, actual point heights at x and f(x) agree, with f≫p supplying the source structure. Neither scheme must be affine or quasi-compact. This does not assert open-height invariance on arbitrary schemes. SP54 proves actual chain codimension plus degree and the complementary-degree criterion on integral targets. SP55 supplies relation reindexing and top-degree vanishing. Reducible/componentwise targets remain separate; mixed-dimensional components do not receive an assumed uniform shift. General rational Chow identification and operations are not consequences of these numerical comparisons. | FORMAL / DIRECT PROOF |

### Integral chain codimension and complementary degree (A11am / SP54)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Finite integral dimension and actual point coheight | `integral_topologicalKrullDim_eq_ofLocallyOfFiniteType`, `point_coheight_ne_top_of_integral_locallyOfFiniteType` in `Cycles/IntegralCodimension.lean` | Integral specialization of [Stacks, Lemma 33.20.3(6), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), with direct order-theoretic bounds | On integral X locally of finite type over a field, SP53's finite height at the actual generic point gives finite full ambient dimension and hence finite point coheight. No affine ambient, quasi-compactness, separate Noetherian or global-dimension-bound premise is supplied. This strengthens the arbitrary-X pointwise statement only under integrality; it does not bound a general non-quasi-compact union of components. | FORMAL / DIRECT PROOF; SOURCE INTEGRAL SCOPE MATCHED |
| Actual chain codimension plus geometric carrier degree | `point_coheight_add_dimension_of_integral_locallyOfFiniteType`, `supportCodimension_ne_top_of_integral_locallyOfFiniteType`, `supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType`, `supportCodimension_add_dimension_of_integral_locallyOfFiniteType` in `Cycles/IntegralCodimension.lean` | Selected integral consequences of [Stacks, Lemma 33.20.3(3), (6), (7), (10), Tag 0A21](https://stacks.math.columbia.edu/tag/0A21), with actual chain codimension as in [Lemma 28.10.3, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ) | The existing codimension is the coheight of the actual irreducible closed support. Finite-coheight induction uses the already proved unit-step law to obtain codimension plus degree equal to the generic degree. SP53 converts degree to actual carrier dimension, also yielding the full extended-dimension equality. Neither subtraction as a new codimension definition nor a uniform-chain/catenarity hypothesis is used. Only the integral numerical comparison is claimed, not every result in the cited source. | FORMAL / DIRECT PROOF; SOURCE INTEGRAL CODIMENSION FORMULA MATCHED |
| Existing homogeneous cycles in complementary degree | `supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType`, `fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType`, `mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType` in `Cycles/IntegralCodimension.lean` | Direct algebraic consequence of the preceding formula and the existing homogeneous-cycle criterion; geometric degree convention [Stacks, Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO), specialized to the field base | For every n∈ℕ, integer degree d−n is equivalent to actual chain codimension n. The coefficient-one cycle iff uses nontrivial semiring coefficients; n≤d is not assumed, and n>d gives an impossible negative-degree support. For any semiring, the whole existing homogeneous submodule is exactly the finite cycles whose nonzero coefficients have actual codimension n. The existing cycle module, carriers and grading remain unchanged. SP55 supplies codimension reindexing of actual principal-relation data and proves top-degree relation vanishing. The data equivalence and generic-degree emptiness do not require Noetherianity; the relation map and span retain the existing Noetherian premise. SP56 subsequently supplies general rational coefficient extension. Reducible/componentwise targets are not supplied by the integral formula. | FORMAL / DIRECT PROOF |

### Codimension-indexed principal relations and the top degree (A11an / SP55)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Actual carrier/function reindexing by codimension | `principalRelationDataEquivCodimension` and its `apply_carrier`, `apply_function`, `symm_apply_carrier`, `symm_apply_function` theorems in `Cycles/PrincipalRelationCodimension.lean` | The degree convention in [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), with the field-base carrier normalization in [Lemma 42.7.5, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO) and the proved SP54 integral codimension formula | For integral X locally of finite type over a field, a relation in cycle degree d−(n+1) has carrier degree d−n, equivalent to actual chain codimension n. The dependent equivalence changes only the proof of that condition; both the actual carrier and the unit in its own function field are literally retained in both directions. No Noetherian or quasi-compactness hypothesis is required for the data equivalence. This is the integral field-base reindexing, not a uniform shift on mixed-dimensional components. | FORMAL / DIRECT PROOF; SOURCE INDEX CONVENTION MATCHED |
| The reindexed generator is the same ambient divisor | `principalRelation_equivCodimension_symm_coe` in `Cycles/PrincipalRelationCodimension.lean` | Actual ambient principal-divisor prescription of [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW); principal-divisor degree in [Definition 42.17.1, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO) | With the existing Noetherian-X premise for finite principal cycles and the relation map, inverse reindexing gives definitionally the unchanged ambient principal divisor. SP54's existing homogeneous-cycle criterion identifies its nonzero coefficients with codimension n+1. The existing span therefore has exactly these codimension-indexed generators; no new relation map, subgroup, cycle module or quotient is introduced. | FORMAL / DIRECT PROOF; SOURCE GENERATOR MATCHED |
| Generic-degree data are empty and rational equivalence is equality | `isEmpty_principalRelationData_genericDegree`, `principalRelations_genericDegree_eq_bot`, `rationallyEquivalent_genericDegree_iff_eq` in `Cycles/PrincipalRelations.lean` | Direct consequence of the dimension-function monotonicity in [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9) and the degree-(m+1) carrier index in [Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW) | For arbitrary integral X and an arbitrary supplied δ, generic-point specialization bounds every actual support degree by δ(η). The generic-degree relation index would require degree δ(η)+1 and is empty, without field, finite-type or Noetherian assumptions. Noetherianity is retained only for the already defined relation span and rational equivalence; the span is zero and the difference criterion reduces to equality. SP56 rationalizes the existing homogeneous cycles and quotient without assuming injectivity of the quotient rationalization map: torsion is possible. SP57 proves representative-preserving rational naturality for the existing graded closed-pushforward and scheme-isomorphism maps. SP58 proves integral-open function-field/stalk compatibility and local-order transport. SP59 proves actual open-support restriction, its finite-cycle coefficient formula and integral principal-divisor restriction under the target finiteness hypotheses. SP60 supplies graded open restriction and the actual open/closed finite-cycle square. SP61 proves the nonempty/empty ambient principal-divisor cases, graded generator transport and integer relation-span/rational-equivalence preservation. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General rational target comparison and reducible/componentwise conventions remain separate. | FORMAL / DIRECT PROOF; SOURCE DEGREE CONSEQUENCE MATCHED |

### Rational coefficient extension and the actual Chow quotient (A11ao / SP56)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Coefficientwise extension on the existing homogeneous cycles | `cyclesOfDegreeRationalize`, `_apply`, `_injective`, `_single`; `cyclesOfDegreeRationalizationEquiv`, `_tmul`, `_one_tmul` in `Cycles/CoefficientExtension.lean` | Direct proof using Mathlib's `Finsupp.supportedEquivFinsupp`, `TensorProduct.finsuppScalarRight` and linear scalar extension | For arbitrary X and supplied δ, integer coefficients cast on the same actual integral closed supports. The supported-degree module is identified with its actual carrier basis, giving ℚ⊗Z_ℤ≃Z_ℚ and the formula q⊗z↦q·z_ℚ. Empty and infinite degree-support index types are allowed; individual cycles remain finitely supported. Injectivity is proved for this coefficient map before taking a quotient. No geometric finiteness, integrality or Noetherian assumption is needed. | FORMAL / DIRECT PROOF |
| Scalar extension of a generated relation quotient | `scalarExtensionQuotientEquiv`, `scalarExtensionQuotientEquiv_tmul_mk` in `Cycles/ScalarExtensionQuotient.lean` | Direct proof from quotient and tensor universal properties | For commutative R and S with an R-algebra structure, a compatible linear scalar-extension model carries the quotient by the R-span of a generator family to the quotient by the S-span of the same images. The two explicit quotient/tensor maps are inverse, with s⊗[m]↦[s·f(m)]. The statement requires neither flatness of S nor injectivity of M→N or of the induced quotient map. | FORMAL / DIRECT PROOF |
| Rational actual principal relations, quotient and representative comparison | `rationalPrincipalRelations`, `RationalChowGroup`, `rationalClassMap`, `rationalClassMap_eq_zero_iff`, `rationalClassMap_surjective`, `rationalClassMap_principalRelation`, `chowRationalizationEquiv`, `chowRationalizationEquiv_tmul_classMap`, `chowRationalize`, `chowRationalize_classMap` in `Cycles/RationalChow.lean` | Principal-generator convention of [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), with the direct scalar-extension quotient theorem above; the target convention uses tensor rational coefficients in [Section 45.3, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ) | Noetherian X is retained for the existing actual principal divisors and relation map. Their coefficient casts generate the rational relation submodule; no arbitrary subgroup or replacement cycle carrier is supplied. The quotient class map is surjective with exactly that kernel and kills each generator. The tensor comparison preserves actual representatives q⊗[z]↦[q·z_ℚ], and its tensor-1 specialization commutes with both class maps. No integral-Chow-to-rational-Chow injectivity is inferred: torsion may be killed. The 0FFZ citation records the rational coefficient convention in its smooth-projective setting, not a construction here of its correspondence product or geometric target comparison. | FORMAL / DIRECT PROOF; SOURCE COEFFICIENT CONVENTION VERIFIED |
| Generic-degree rational relations vanish | `rationalPrincipalRelations_genericDegree_eq_bot` in `Cycles/RationalChow.lean` | Direct consequence of SP55's actual empty principal-relation index and the rational span definition | Integral Noetherian X and any supplied δ suffice; no field-base hypothesis is required. The rational span of the empty actual generator family is zero. SP57 proves representative-preserving rational naturality for the existing graded closed-pushforward and scheme-isomorphism maps. SP58 proves integral-open function-field/stalk compatibility and local-order transport. SP59 proves actual open-support restriction, its finite-cycle coefficient formula and integral principal-divisor restriction under the target finiteness hypotheses. SP60 supplies graded open restriction and the actual open/closed finite-cycle square. SP61 proves the nonempty/empty ambient principal-divisor cases, graded generator transport and integer relation-span/rational-equivalence preservation. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General proper/flat/Gysin relation laws, geometric target identification and reducible/componentwise target conventions remain separate. | FORMAL / DIRECT PROOF |

### Rational closed pushforward and scheme-isomorphism naturality (A11ap / SP57)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Coefficient-parametric homogeneous pushforward and actual coefficient compatibility | `gradedClosedImmersionPushforwardWithCoefficients`, `_val`, `_id`, `_comp` in `Cycles/GradedPushforward.lean`; `closedImmersionPushforward_rationalize`, `gradedClosedImmersionPushforward_rationalize`, `openRestriction_iso_mem_cyclesOfDegree` in `Cycles/CoefficientPushforward.lean` | Direct extension of the already constructed closed-image cycle map, checked on the same actual carrier basis | The cycle layer accepts any semiring, a closed immersion and equality of source/image support degrees. The original four integer APIs remain unchanged specializations. Raw and graded coefficient casts commute with actual pushforward. Existing open restriction along a scheme isomorphism preserves the canonical restricted degree over every semiring. No Noetherian, integral, field-base or finite-type premise is imposed at this layer. | FORMAL / DIRECT PROOF |
| Actual rational principal-relation preservation and quotient descent | `rationalPrincipalRelations_le_comap_closedImmersionPushforward`; `rationalChowClosedImmersionPushforward`, `_classMap`, `_restricted_classMap`, `_id`, `_comp` in `Cycles/RationalChowPushforward.lean` | Closed-immersion case of [Stacks, Lemma 42.20.3, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2), proved directly from existing actual carrier-image principal-divisor transport and coefficient compatibility | Source and target are Noetherian, as required by the existing relation quotients; dimension functions agree on actual source/image support degrees. The geometric principal-generator identity proves rational-span preservation rather than assuming it. The quotient map sends each actual representative to the class of its existing pushforward, and inherits identity/composition. Canonical restriction of the target dimension function supplies the numerical premise. The cited source has its broader proper-morphism/base-dimension setup; this checkpoint proves the intrinsic closed-immersion case, not general proper or flat relation descent. | FORMAL / DIRECT PROOF; SOURCE CLOSED CASE VERIFIED |
| Closed pushforward commutes with both rationalization comparisons | `rationalChowClosedImmersionPushforward_chowRationalize`, `rationalChowClosedImmersionPushforward_chowRationalizationEquiv` in `Cycles/RationalChowPushforward.lean` | Direct representative and tensor-induction proofs using SP56's coefficient and quotient comparisons | The integral-to-rational map commutes with actual closed pushforward on all integral classes. The full ℚ⊗CH comparison intertwines scalar extension of the integral pushforward with the actual rational quotient map. This proves both squares, not only equality on a freely selected cohomological model. No rationalization-injectivity assumption is used. | FORMAL / DIRECT PROOF |
| Rational scheme isomorphism and its actual inverse representatives | `rationalChowIsoEquiv`, `_chowRationalizationEquiv`, `_toLinearMap`, `_classMap`, `_symm_classMap`, `_chowRationalize` in `Cycles/RationalChowIsomorphism.lean` | Direct scalar extension of the existing integral Chow isomorphism and the already proved equality of inverse closed pushforward with actual open restriction | For Noetherian schemes, an actual isomorphism and the canonically restricted dimension function, the scalar-extended integral equivalence is proved equal to actual rational closed pushforward. Its inverse class formula uses the existing openRestriction ℚ on the literal rational-cycle representative, with homogeneity proved by the coefficient-parametric cycle lemma. No second graded-isomorphism carrier is introduced. SP58 proves actual integral-open function-field/stalk compatibility and divisor-point/local-order transport. SP59 proves actual open-support restriction, its finite-cycle coefficient formula and integral principal-divisor restriction under the target finiteness hypotheses. SP60 supplies graded open restriction and the actual open/closed finite-cycle square. SP61 proves ambient principal-divisor restriction, including the empty-carrier branch, graded generator transport and integer relation-span/rational-equivalence preservation. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. Localization, general proper/flat/Gysin laws and geometric target identification remain separate. The isomorphism specialization does not assert injectivity for a general closed Chow pushforward. | FORMAL / DIRECT PROOF |

### Open-immersion function fields, divisor points and local orders (A11aq / SP58)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Actual contravariant generic-stalk field map and local compatibility | `functionFieldIsoOfOpenImmersion`, `functionFieldEquivOfOpenImmersion`, `functionFieldIsoOfOpenImmersion_stalkSpecializes`, `functionFieldEquivOfOpenImmersion_algebraMap` in `Cycles/FunctionFieldTransport.lean` | Direct proof from Mathlib's `genericPoint_eq_of_isOpenImmersion`, the actual open-immersion stalk isomorphism and `Scheme.stalkSpecializes_stalkMap` | An open immersion of integral schemes sends the actual generic point to the actual generic point. The resulting stalk isomorphism is the contravariant function-field map, and stalk-specialization naturality proves the local-algebra square. No Noetherian, compactness, finite-type, affine, normality or field-base premise is required. The four existing scheme-isomorphism APIs specialize this same construction, rather than introducing parallel fields or maps. | FORMAL / DIRECT PROOF |
| Actual divisor-point embedding and its precise image | `stalkDimension_openImmersion`, `divisorPointEmbedding`, `divisorPointEmbedding_val`, `mem_range_divisorPointEmbedding_iff`, `divisorPointEmbedding_iso` in `Cycles/SchemeLocalOrder.lean` | Direct Krull-dimension invariance under the actual stalk ring isomorphism, followed by the injective open point map | For arbitrary schemes, the existing one-dimensional-stalk point index embeds into the target index. A target divisor point has a source preimage exactly when its underlying point lies in the actual open image. No integrality or Noetherian hypothesis is needed, and no bijection with all target divisor points is asserted. For a scheme isomorphism the embedding agrees with the retained point equivalence. | FORMAL / DIRECT PROOF |
| Signed local-order preservation with target-only local Noetherianity | `divisorOrder_openImmersion` in `Cycles/SchemeLocalOrder.lean` | Local length-order convention of [Stacks, Definition 10.121.2, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD), and its prime-divisor use in [Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ); direct isomorphism transport of that coefficient | Source and target are integral and the target is locally Noetherian; local Noetherianity of the source is derived. The actual generic-stalk field map and local stalk isomorphism satisfy the scalar square used by the already proved fraction-order transport, giving ord_x(j* f)=ord_j(x)(f). This requires neither compactness/global Noetherianity nor normality/DVR structure. The old isomorphism order theorem specializes the same proof. SP59 proves actual open-support restriction and its reduced-closure inverse, the finite-cycle coefficient formula and principal-divisor restriction for integral schemes with locally Noetherian, quasi-compact target. SP60 supplies graded open restriction and the actual open/closed finite-cycle square. SP61 proves ambient principal-divisor restriction with its nonempty and empty carrier cases, graded generator transport and integer relation-span/rational-equivalence preservation. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. General open restriction is not modeled by a closed-image map, and no general flat Chow descent or localization sequence is inferred from this pointwise result. | FORMAL / DIRECT PROOF; SOURCE LOCAL-ORDER SCOPE VERIFIED |

### Actual open supports and finite principal-divisor restriction (A11ar / SP59)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Actual reduced closure, inverse ideal-comap restriction and codimension | `openClosureSubscheme`, `openClosureSubscheme_ambientGenericPoint`, `ambientGenericPoint_openRestrictionSubscheme`, `nonempty_openRestrictionSubscheme_iff`, `openClosureSubscheme_comap`, `openClosureSubscheme_openRestrictionSubscheme`, `supportCodimension_openClosureSubscheme`, `supportCodimension_openRestrictionSubscheme`, `openClosureSubscheme_divisorPoint` in `Cycles/OpenSupport.lean` | Reduced-closure description for open restriction in [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA); direct use of the existing actual point/support equivalence and open stalk isomorphism | The closure is the literal reduced point closure of j(ξ_W). Its actual ideal-sheaf comap recovers W. Nonempty restriction is equivalent to the ambient generic point lying in the open image, and reduced closure recovers the original ambient support in that case. Existing chain codimension is preserved through actual generic-point local rings. These support results hold for arbitrary schemes without integrality or finiteness assumptions. The source's graded/base-induced setup is not substituted for this ungraded support construction. | FORMAL / DIRECT PROOF; SOURCE OPEN-SUPPORT DESCRIPTION MATCHED |
| Coefficient formula for the existing finite-cycle restriction | `openRestriction_apply` in `Cycles/OpenSupport.lean` | Generator restriction in the open-immersion discussion of [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA), with direct finite linear extension | For every semiring and actual finite cycle, the coefficient at W is exactly the original coefficient at its ambient reduced closure. The proof uses the already defined ideal-comap generator restriction, treats empty inverse images as zero, and uses the inverse support identities for uniqueness. Neither a new restriction map nor a finite ambient support index is introduced. This is the ungraded finite-cycle formula, not a proof of the source's full graded localization sequence or arbitrary flat pullback. | FORMAL / DIRECT PROOF |
| Signed order on an actual prime support and its reduced closure | `primeDivisorOrder_openImmersion` in `Cycles/PrincipalDivisorTransport.lean` | Prime-divisor coefficient convention [Stacks, Definition 31.27.3, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ), with SP58's proved local-order transport | Integral source/target and locally Noetherian target suffice; source local Noetherianity is derived. The closure codimension theorem makes the actual ambient closure a prime divisor, and its generic point is the existing divisor-point image. Pullback uses the actual generic-stalk function-field map. No quasi-compactness, normality, DVR or field-base assumption is needed for this coefficient theorem. | FORMAL / DIRECT PROOF; SOURCE COEFFICIENT MATCHED |
| Open restriction of the existing finite principal-divisor cycle | `openRestriction_principalDivisor_of_isOpenImmersion` in `Cycles/PrincipalDivisorTransport.lean` | Actual principal-divisor coefficients in [Stacks, Definition 31.27.5, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3), combined directly with the preceding open-support and order comparisons | For integral source/target, locally Noetherian and quasi-compact target, the source's local Noetherianity and quasi-compactness are derived. Both principal divisors are therefore the existing finite sums. Equality follows coefficientwise: prime supports use the signed-order comparison, and all other coefficients vanish on both sides. The existing isomorphism endpoint specializes the new proof without changing its signature. The source definition permits locally finite Weil sums; target quasi-compactness is retained here for the project's existing finite-cycle carrier. SP60 supplies actual δ∘j grading and the open/closed finite-cycle square. SP61 uses that square to prove both ambient principal-divisor branches, graded generator transport and integer relation-span/rational-equivalence preservation. SP62 supplies integral/rational quotient descent and coefficient naturality. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity; closed-complement localization remains separate. | FORMAL / DIRECT PROOF; SOURCE FINITE-CYCLE SCOPE MATCHED |

### Actual open grading and closed-carrier base change (A11as / SP60)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Literal open restriction of the supplied dimension function | `openImmersion_covBy`, `DimensionFunction.comapOpenImmersion`, `_apply`, `_id`, `_comp`, `_eq_comapClosedImmersion` in `Cycles/OpenGrading.lean` | Both conditions of [Stacks, Definition 5.20.1, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9); direct actual specialization-order proof | An open immersion reflects specialization and has order-convex point image. Its point map preserves covers, so the literal composite δ∘j satisfies both dimension-function laws. Identity/composition and equality with the existing closed restriction for a map that is also closed are proved. The ambient schemes are arbitrary; neither Noetherianity nor an existence theorem for dimension functions is assumed. | FORMAL / DIRECT PROOF; SOURCE DEFINITION VERIFIED |
| Actual support degrees and homogeneous finite-cycle restriction | `supportDegree_openClosureSubscheme`, `supportDegree_openRestrictionSubscheme`, `openRestriction_mem_cyclesOfDegree`, `gradedOpenRestriction`, `_val`, `_id`, `_comp` in `Cycles/OpenGrading.lean` | Open-restriction prescription and its graded functoriality in [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA); direct proof for the existing finite-cycle modules and supplied δ | Actual generic-point identities identify the source support degree with the ambient reduced-closure degree and preserve the degree of a nonempty restricted carrier. The previous coefficient formula restricts the existing cycle map to the existing homogeneous submodules over every semiring, including trivial coefficients and empty schemes. The underlying representative and contravariant identity/composition laws are retained. This is the open-immersion finite-cycle specialization; SP61–SP62 subsequently prove actual open relation preservation and quotient restriction. Arbitrary flat pullback is not supplied by this construction. | FORMAL / DIRECT PROOF; SOURCE OPEN-CYCLE SCOPE MATCHED |
| Actual carrier square and open/closed finite-cycle compatibility | `openRestrictionSubschemeMap_subschemeι` in `Cycles/OpenSupport.lean`; `openRestriction_closedImmersionPushforward_subscheme` in `Cycles/OpenClosedBaseChange.lean` | Scheme-theoretic inverse image as the fiber product and ideal pullback in the opening of [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA); the cycle square is proved directly on actual integral generators | The actual ideal-comap carrier map commutes with its two closed inclusions even for an arbitrary scheme map. For open j, an actual integral closed ambient carrier and any semiring, existing open restriction commutes with actual closed pushforward around this Cartesian square. No nonempty inverse-image premise is imposed. The proof matches nonemptiness of both generator inverse images, identifies their actual generic points in the nonempty case and gives zero on both sides in the empty case. No ambient integral, Noetherian or compactness premise is needed. SP61 uses this cycle square for both ambient principal-divisor branches and proves graded generator, integer relation-span and rational-equivalence preservation. SP62 proves integral and rational open quotient restriction, representative formulas, contravariant functoriality and both rationalization squares. SP63 proves actual raw/graded cycle surjectivity via reduced closure and integral/rational Chow restriction surjectivity; closed-complement kernel/image and localization exactness remain separate. | FORMAL / DIRECT PROOF; SOURCE FIBER-PRODUCT DESCRIPTION MATCHED |

### Actual open restriction of ambient principal relations (A11at / SP61)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Ambient principal-divisor restriction, nonempty and empty branches | `openRestriction_ambientPrincipalDivisor_of_nonempty`, `openRestriction_ambientPrincipalDivisor_of_isEmpty` in `Cycles/PrincipalDivisorRestriction.lean` | Principal-divisor convention [Stacks, Definition 31.27.5, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3), combined directly with the proved SP59 open divisor comparison and SP60 actual carrier square | The original integral closed carrier alone is locally Noetherian and quasi-compact. For its actual nonempty ideal-comap carrier, the inherited finiteness and generic-stalk field pullback give equality of the existing ambient principal cycles. An empty carrier gives zero via its actual zero finite-cycle module. No ambient integrality, Noetherianity, compactness or grading premise is required for these two identities. The finite-cycle convention retains carrier quasi-compactness; the cited Weil divisor definition itself permits locally finite sums. | FORMAL / DIRECT PROOF; SOURCE COEFFICIENT CONVENTION MATCHED |
| Nonempty restriction of the actual principal-relation data | `PrincipalRelationData.openRestriction`, `_carrier`, `_function` in `Cycles/PrincipalRelationRestriction.lean` | Actual carrier/function indexing in [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), with the proved supplied-dimension open restriction | For arbitrary schemes, a supplied δ and an actual degree-(m+1) relation carrier with nonempty open inverse image, the restricted datum uses exactly that ideal-comap carrier and the actual contravariant function-field pullback. The carrier degree is preserved. This index construction needs no Noetherianity, compactness or field-base assumption. It does not assign data to the empty branch. | FORMAL / DIRECT PROOF; SOURCE GENERATOR INDEX MATCHED |
| Graded generator, relation-span and rational-equivalence preservation | `openImmersion_isNoetherian`, `gradedOpenRestriction_principalRelation_of_nonempty`, `_of_isEmpty`, `principalRelations_le_comap_openRestriction`, `rationallyEquivalent_openRestriction` in `Cycles/PrincipalRelationRestriction.lean` | Open-immersion specialization of [Stacks, Lemma 42.20.2, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1), proved directly for the existing intrinsic Noetherian cycle model | Target Noetherianity is assumed and source Noetherianity is derived. The same graded cycle map sends each actual principal generator to the nonempty restricted generator or zero; span preservation and the difference criterion then prove preservation of actual rational equivalence. The source treats arbitrary flat maps with relative dimension in Situation 42.7.1; this proof covers open immersions and finite cycles with the supplied dimension function. This generator checkpoint supplies the open relation law; SP62 constructs the integral/rational quotient maps and their rationalization comparisons. SP63 proves actual raw/graded-cycle and integral/rational Chow restriction surjectivity; the closed-complement kernel/image comparison and localization sequence of 02RX remain separate. | FORMAL / DIRECT PROOF; SOURCE OPEN SPECIALIZATION MATCHED |

### Integral and rational Chow open restriction (A11au / SP62)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Integral Chow quotient restriction and contravariant functoriality | `chowOpenRestriction`, `_classMap`, `_id`, `_comp` in `Cycles/ChowOpenRestriction.lean` | Quotient definition [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW), with the open specialization of relation preservation in [Lemma 42.20.2, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1) | The already proved SP61 span inclusion descends the existing graded cycle map by the quotient universal property. Target Noetherianity alone is assumed; open source and intermediate schemes inherit it. The supplied δ restricts by the actual point maps. Class representatives are unchanged except for actual cycle restriction, and identity/composition follow on those representatives. The source's full flat/base-induced framework is not assumed as a new project input. | FORMAL / DIRECT PROOF; SOURCE OPEN-QUOTIENT SPECIALIZATION MATCHED |
| Coefficient compatibility on raw and homogeneous finite cycles | `openRestriction_rationalize`, `gradedOpenRestriction_rationalize` in `Cycles/CoefficientRestriction.lean` | Direct coefficientwise proof using SP59's actual reduced-closure coefficient formula | For any open immersion, integer-to-rational coefficient cast commutes with the existing finite-cycle restriction. A supplied dimension function gives the same identity on its homogeneous submodules and the canonical restricted grading. No Noetherianity, integrality, compactness or field-base premise is needed, and no quotient injectivity is used. | FORMAL / DIRECT PROOF |
| Rational relation descent, representative formulas and both scalar-extension squares | `rationalPrincipalRelations_le_comap_openRestriction`, `rationalChowOpenRestriction`, `_classMap`, `_id`, `_comp`, `_chowRationalize`, `_chowRationalizationEquiv` in `Cycles/RationalChowOpenRestriction.lean` | Direct rational span and quotient argument from the same actual generators, followed by SP56's representative-preserving tensor comparison; geometric relation prescription as in [Stacks, Definition 42.19.1, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW) | Target Noetherianity and supplied δ suffice. Coefficient compatibility transfers the nonempty/empty integral generator formulas into preservation of the rational span; the quotient map therefore retains actual rational-cycle representatives and identity/composition. The integral rationalization square holds on every integral class, and the full tensor square on every tensor element. Neither injectivity of Chow rationalization nor a new rational quotient model is used. SP63 proves raw/graded cycle and integral/rational Chow restriction surjectivity via reduced closure. Closed-complement kernel/image and localization exactness remain separate, as do general proper/flat/Gysin laws and geometric target identification. | FORMAL / DIRECT PROOF; DIRECT SCALAR-EXTENSION COMPARISON |

### Surjectivity of actual open cycle and Chow restriction (A11av / SP63)

| Source-matched step | Lean interface | Exact source | Scope and matching decision | Status |
| --- | --- | --- | --- | --- |
| Reduced-closure lifts of raw and homogeneous finite cycles | `openRestriction_surjective`, `gradedOpenRestriction_surjective` in `Cycles/OpenRestrictionSurjectivity.lean` | Open-cycle surjectivity argument preceding Lemma 42.14.2 in [Stacks, Section 42.14, Tag 02RA](https://stacks.math.columbia.edu/tag/02RA) | The actual reduced ambient closure of every integral support restricts to that support. Finite linear combinations lift with unchanged coefficients; the proved degree comparison retains homogeneity for the supplied restricted dimension function. These intrinsic finite-cycle results hold for arbitrary schemes and any semiring, without Noetherianity, compactness or a field base. The source uses its base-induced dimension and locally finite cycle setup; only its reduced-closure lifting argument is matched here. | FORMAL / DIRECT PROOF; SOURCE LIFTING SCOPE VERIFIED |
| Surjectivity of the existing integral and rational Chow restrictions | `chowOpenRestriction_surjective` in `Cycles/ChowOpenRestriction.lean`; `rationalChowOpenRestriction_surjective` in `Cycles/RationalChowOpenRestriction.lean` | Surjectivity portion of the sequence in [Stacks, Lemma 42.19.3, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX), proved here from actual cycle lifts and quotient representative formulas | Target Noetherianity alone is assumed and open-source Noetherianity is derived. Choose a homogeneous integral or rational cycle representative, lift it by reduced support closure and take its existing ambient class. The proof uses no Chow-level closure operation or relation-preserving section. The actual closed-complement kernel/image identification and the full localization exactness assertion remain separate, as do general proper/flat/Gysin laws and geometric target identification. | FORMAL / DIRECT PROOF; SOURCE SURJECTIVITY CONSEQUENCE MATCHED |

The actual split-scheme span idempotence and the obstruction to unital maps
`M₂(ℚ) → C` for nontrivial commutative `C` are proved directly in Lean; no
external theorem or source axiom is used for either.

The split-span coefficient realization is also now proved directly: intrinsic
scheme points give isomorphism invariance; disjoint open point charts prove
the actual fiber-product comparison; the actual scheme coproduct comparison
proves geometric additivity. Counting matching pairs then supplies the
matrix algebra homomorphism. No Stacks citation is being used as an axiom for
this bridge. The exact additive quotient is also proved directly: the
actual finite indexed scheme-coproduct comparison gives the geometric
decomposition, and point-pair normal form with matrix-unit independence
identifies the generated ideal with the full kernel. The actual zero-cycle
and rational-equivalence construction now supplies the additive Chow groups.
Actual image, product, and inverse-image comparisons now supply the point
geometry for proper pushforward and flat pullback. Stalk-length and
residue-field degree computations supply their multiplicities. The resulting
cycle operations descend to the Chow quotient, and geometric correspondence
composition is proved to be the matrix law. Its endomorphism algebra is
identified with the additive span quotient, preserving point generators,
and its actual Chow action satisfies the matrix-vector formula. The actual
complex-point topology, singular degree-zero cocycles, and normalized cycle
class now provide the Betti action comparison. The independent effective
degree-zero Hodge structure and the actual point-plus-scheme Chow block
now instantiate graph construction, lower-left detection, and the target
equivalences. The split marked-sheet checkpoint now constructs the regular
torsor, multiplicative residual Chow map, and fixed-action comparison using
an actual Chow shear. Its generated class is the negative fundamental class;
multiplicative rigidity prevents arbitrary coverage by surjective
multiplicative maps alone. Class-dependent geometric generation, general
Hodge models, and nontrivial cover-compactification comparisons remain separate.

## Citation acceptance test

For each proposed source, record:

1. the stable URL and exact tag/theorem number;
2. a verbatim mathematical statement in private notes (do not copy long
   passages into a public draft);
3. a symbol-by-symbol mapping to the Lean declaration;
4. every extra source hypothesis absent from the current interface; and
5. whether the source proves the implication used or only a nearby result.

## Galois coefficient descent and harmonic transport source copies

The local `galois-obstruction-theory` workspace supplies three source snapshots.
It is not a Git checkout, so the copied file headers identify the exact source
bytes by SHA-256. The Jacobian tensor-invariant proof is generalized to arbitrary
vector spaces in `LinearAlgebra/GaloisDescent.lean`; its complete MIT notice is
retained inline. The two Homotopical sources become `LinearAlgebra/Harmonic/`
`Morphism.lean` and `HarmonicCohomology.lean`, retaining the original MIT notice
in that directory's `LICENSE`. The quotient bridge and rational witness
transport are local additions. These files use the existing Lean/Mathlib pin;
no new package dependency is introduced.

The scalar inclusion acts on coefficient tensors of the existing Chow module.
The native harmonic quotient is over ℝ, and raw endomorphism naturality requires
symmetry. The aggregate additionally requires the transported witness to be
injective. [0061](working/0061-galois-harmonic-coverage.md) records source paths,
hashes, gates and the actual P¹ instance; the manuscript preserves these scopes.

## Actual split geometric cover comparison (2026-11-26)

The geometric rank, ordinary Chow bridge, native transfer comparison and
aggregate adapter in [0062](working/0062-geometric-cover-coverage.md) are local
proofs using existing project APIs and pinned Mathlib. No external source copy,
new license input, package dependency or source-theorem axiom is introduced.
The rank proof uses the actual scheme product and finite-flat rank base change.
The ordinary Chow comparison retains identical cycle representatives and the
original finite maps; the native comparison uses actual point fibers and the
canonical complex-point homeomorphism. General upstairs generation is an input
to the adapter, proved here only for the displayed zero-dimensional example.

## Split projective-line cover and native cochain transfer (2026-11-26)

The six modules in [0063](working/0063-projective-line-split-double-cover.md)
are local proofs using existing project APIs and pinned Mathlib. No external
source copy, package dependency, license input or theorem axiom is added.
The geometric rank is calculated from the actual affine product-ring model.
Canonical analytic points are compared using original open immersions.
Connectedness of the standard simplex proves the original cochain split;
native categorical homology transports the resulting maps to cohomology.
The ordinary Chow comparison retains the original principal relations and
quotient maps. The P¹ instance uses the existing independently constructed
Hodge target and component cycle maps; general Gysin compatibility remains
outside this checkpoint.

## Connected square-map comparison (2026-11-26)

The eight modules in [0064](working/0064-projective-line-square-cover.md)
are local proofs using existing project APIs and pinned Mathlib. No external
source copy, package dependency, license input or theorem axiom is added.
The coordinate proof uses even/odd coefficients of the actual square ring
map, and the original glued scheme charts identify its finite flat rank.
Original weighted fiber degree and residue degrees compute branch
multiplicities. Native circle-square pullback uses literal angular singular
triangles; a morphism of the original short exact cochain sequences proves
Mayer–Vietoris naturality. The supported trace uses the actual fixed
singleton map and the existing oriented zero-point Gysin isomorphism.
Original Chow quotients, maps and the independent Hodge target are retained.
General branched trace and arbitrary point-Gysin naturality remain separate.

## Original relative Thom and ramification comparison (2026-11-26)

The five modules in [0065](working/0065-projective-line-ramification-comparison.md)
are local proofs using original project cochain, relative-boundary, normal-chart,
excision, Gysin and ordinary cycle APIs plus pinned Mathlib. The actual complex
algebraic-closedness instance is imported explicitly for the Chow adapter.
No external source copy, new dependency, license input or theorem axiom is
added. The native local result uses the existing angular circle-square proof
and the original relative connecting map; the global result uses literal
cochain precomposition and original excision. The ordinary zero-cycle result
uses actual finite-fiber coefficients with original local multiplicity.
Dependency audits distinguish this local proof route from the prior global
P¹ square calculation and prior square-cover fixture. This does not supply
general point transport, coordinate independence or general proper trace.

## Finite-point Gysin and affine coordinates (2026-11-26)

The seven modules in [0066](working/0066-projective-line-finite-point-gysin.md)
are local proofs using pinned Mathlib and original project point/cochain/chart,
relative excision, Gysin and ordinary cycle APIs. No external source copy,
package pin, license input or theorem axiom is added. The compact-parameter
one-point extension uses compact inverse images; the affine homotopy uses a
fixed-unit complex exponential/logarithm path. Actual scheme normal charts
use the original polynomial algebra equivalence X ↦ uX+a. Original native
relative restriction and support forgetting connect these actual charts to
positive Gysin normalization and coordinate independence. The original support
scheme image and ordinary reduced cycle are retained in the certificate family.
The global native affine map is not presented as a proved global scheme
morphism, and general analytic-coordinate or proper-trace conclusions are
not inferred from this finite-point affine case.

## Infinity Gysin and complete point coverage (2026-11-27)

The seven modules in [0067](working/0067-projective-line-infinity-gysin.md)
use local proofs and the same pinned Mathlib inputs. The cover pair is swapped
on the original cochain complexes; its negative intersection map gives the
original boundary sign. Actual circle component evaluation computes inverse
H¹, and actual reciprocal-chart naturality proves native H² positivity. The
local Thom class passes through original actual Y-chart pullback, relative
excision and forgetting. Both chart cases retain their original singleton
source and ordinary reduced cycle of the same actual scheme image.

No new source axiom, external copied module, dependency pin or license input
is introduced. The full model and original finite maps are unchanged; global
rank two and the earlier zero-supported push are explicitly retained.
Nonlinear transition naturality and general proper trace remain separate.
