.DEFAULT_GOAL := help
.NOTPARALLEL:

.PHONY: build-p1-double-cover check-p1-double-cover
.PHONY: build-geometric-cover-coverage check-geometric-cover-coverage
.PHONY: build-galois-harmonic-coverage check-galois-harmonic-coverage
.PHONY: build-finite-coverage check-finite-coverage build-harmonic-witness check-harmonic-witness build-cover-harmonic-comparison check-cover-harmonic-comparison

LAKE ?= lake
PYTHON ?= python3

.PHONY: help build build-transfer build-derham-core build-derham-components build-chow build-betti \
        build-comparison check check-layers check-derham-core check-chow \
        check-derham-components check-comparison check-integration \
        build-affine-line-comparison check-affine-line-comparison \
        build-graph-chow check-graph-chow \
        build-positive-degree check-positive-degree \
        build-scheme-comparison check-scheme-comparison \
        build-projective-line-betti check-projective-line-betti \
        build-projective-line-periods check-projective-line-periods \
        build-small-chains check-small-chains \
        build-open-cover-small-chains check-open-cover-small-chains \
        build-sheafification-kernel check-sheafification-kernel \
        build-global-singular-sheaves check-global-singular-sheaves \
        build-open-singular-sheaves check-open-singular-sheaves \
        build-flasque-derived check-flasque-derived \
        build-singular-derived-comparison check-singular-derived-comparison \
        build-singular-constant-comparison check-singular-constant-comparison \
        build-analytic-betti-comparison check-analytic-betti-comparison \
        build-singular-coefficient-change check-singular-coefficient-change \
        build-complex-singular-comparison check-complex-singular-comparison \
        build-singular-cohomology check-singular-cohomology \
        build-circle-cohomology check-circle-cohomology \
        build-projective-line-cohomology check-projective-line-cohomology \
        build-projective-line-product check-projective-line-product \
        build-projective-line-product-fibers check-projective-line-product-fibers \
        build-projective-line-product-chow-realization check-projective-line-product-chow-realization \
        build-circle-orientation check-circle-orientation \
        build-projective-line-period-comparison check-projective-line-period-comparison \
        build-hodge-filtration check-hodge-filtration \
        build-projective-line-hodge check-projective-line-hodge \
        build-filtered-hodge-target check-filtered-hodge-target \
        build-filtered-projector-defect check-filtered-projector-defect \
        build-tate-hodge-bridge check-tate-hodge-bridge \
        build-scheme-betti check-scheme-betti \
        build-holomorphic-derham check-holomorphic-derham \
        build-analytic-charts check-analytic-charts \
        build-holomorphic-descent check-holomorphic-descent \
        build-intrinsic-poincare check-intrinsic-poincare \
        build-singular-sheaves check-singular-sheaves \
        build-relative-cohomology check-relative-cohomology \
        build-projective-line-point-gysin check-projective-line-point-gysin \
        build-fixed-inertia check-fixed-inertia \
        build-palomar check-palomar-proofs check-palomar

help:
	@echo "build-transfer       Generic linear degree transfer"
	@echo "build-derham-core    Affine de Rham complex and algebra trace"
	@echo "build-derham-components  Polynomial closed functions and component basis"
	@echo "build-affine-line-comparison  Actual affine-line degree-zero Betti comparison"
	@echo "build-chow           Finite flat cycle/Chow transfer"
	@echo "build-graph-chow     Actual graph Chow convolution and absolute-product comparison"
	@echo "build-positive-degree  Positive-degree forms and ordinary projective-line cycle classes"
	@echo "build-scheme-comparison  Projective-line scheme de Rham comparison and cycle classes"
	@echo "build-projective-line-betti  Actual P1 complex topology and all-degree singular cochains"
	@echo "build-projective-line-periods  Actual analytic Laurent and scheme periods"
	@echo "build-small-chains    Rational singular subdivision and small-chain comparison"
	@echo "build-open-cover-small-chains  Arbitrary-cover chain/cochain comparison and acyclic vanishing kernel"
	@echo "build-sheafification-kernel  Actual global unit kernel, local vanishing and native acyclicity"
	@echo "build-global-singular-sheaves  Original global unit surjectivity and cohomology comparison"
	@echo "build-open-singular-sheaves  Native open restriction, actual section lifts and flasqueness"
	@echo "build-flasque-derived  Higher derived sections of actual flasque module sheaves"
	@echo "build-singular-derived-comparison  Original whole-complex derived comparison for flasque sheaves"
	@echo "build-singular-constant-comparison  Original rational singular groups and derived constant-sheaf cohomology"
	@echo "build-analytic-betti-comparison  Complex coefficients and the actual holomorphic derived target"
	@echo "build-singular-coefficient-change  Finite-cohomology coefficient change on actual singular cochains"
	@echo "build-complex-singular-comparison  Complex singular/holomorphic comparison and canonical P1 case"
	@echo "build-singular-cohomology  Exact rational duals and full singular Mayer-Vietoris"
	@echo "build-circle-cohomology  Actual circle singular H1 and cover generator"
	@echo "build-projective-line-cohomology  Actual P1 rational singular H2 and cover generator"
	@echo "build-projective-line-product  Actual P1 square geometry, fiber supports and Betti classes"
	@echo "build-projective-line-product-fibers  Actual P1 square Chow fibers and supported Betti classes"
	@echo "build-projective-line-product-chow-realization  Actual P1 square Chow-to-Betti map"
	@echo "build-circle-orientation  Actual positive cycle and generator pairing"
	@echo "build-projective-line-period-comparison  Actual boundary periods and ordinary cycle maps"
	@echo "build-hodge-filtration  Actual derived degree filtration and P1 H2 calculation"
	@echo "build-projective-line-hodge  Geometric type (1,1) and the fixed P1 Hodge-cycle model"
	@echo "build-filtered-hodge-target  General rational target from tensor conjugation and filtration"
	@echo "build-filtered-projector-defect  Cyclic filtered detector of the existing closure defect"
	@echo "build-tate-hodge-bridge  Proved Tate/Hodge compatibility and the existing target equivalence"
	@echo "build-scheme-betti    Canonical scheme complex points, Betti functor and P1 comparison"
	@echo "build-holomorphic-derham  Holomorphic complex, radial primitives and all-degree Poincare comparison"
	@echo "build-intrinsic-poincare  Intrinsic chart identifications and constant-sheaf quasi-isomorphism"
	@echo "build-singular-sheaves  Original singular cochains and rational constant-sheaf resolution"
	@echo "build-holomorphic-descent  Atlas forms sheaf, descended differential and all-degree algebraic map"
	@echo "build-analytic-charts  Canonical analytic atlas, regular functions and scheme maps"
	@echo "build-relative-cohomology  Actual relative cochains, excision and connecting signs"
	@echo "build-projective-line-point-gysin  Oriented zero-point Gysin and ordinary cycle comparison"
	@echo "build-fixed-inertia  Adapted DVR fixed-inertia étaleness and local bridge"
	@echo "build-betti          Existing singular Betti realization"
	@echo "build-comparison     De Rham, geometry and Chow/Betti squares"
	@echo "check-layers         Enforce project import boundaries"
	@echo "check-derham-core    Core build, examples and axiom audits"
	@echo "check-derham-components  Polynomial/component regressions and axiom audits"
	@echo "check-affine-line-comparison  Topology, cocycles, tensors and pullback checks"
	@echo "check-chow           Chow build, rank and quotient regressions"
	@echo "check-graph-chow     Graph actions, quotient projectors and axiom audits"
	@echo "check-positive-degree  Cocycles, trivializations, nonzero H2 and axiom audits"
	@echo "check-scheme-comparison  Actual sheaves, derived sections and ordinary cycle compatibility"
	@echo "check-projective-line-betti  Atlas topology, actual cochains, H0 bridge and axiom audits"
	@echo "check-projective-line-periods  Analytic integrals, quotient descent and cycle normalization"
	@echo "check-small-chains    Subdivision, shrinking, actual inclusion and axiom audits"
	@echo "check-open-cover-small-chains  Infinite-cover shrinking, nonzero vanishing cochains and axiom audits"
	@echo "check-sheafification-kernel  Nonzero native kernel terms, actual primitives and scheme controls"
	@echo "check-global-singular-sheaves  Global unit on noncompact, empty, affine and projective-line spaces"
	@echo "check-open-singular-sheaves  All-degree open restrictions and a noncompact projective-line chart"
	@echo "check-flasque-derived  Native derived vanishing, skyscrapers and preserved projective-line H2"
	@echo "check-singular-derived-comparison  Whole-complex comparison, original maps and all-degree controls"
	@echo "check-singular-constant-comparison  Original composite, canonical scheme targets and nonzero derived P1 class"
	@echo "check-analytic-betti-comparison  Coefficient maps, rational detection and nonzero holomorphic P1 class"
	@echo "check-singular-coefficient-change  Infinite chain terms, actual coefficient map and P1 isomorphism"
	@echo "check-complex-singular-comparison  Original coefficient squares, derived comparison and P1 isomorphism"
	@echo "check-singular-cohomology  Duality, original restriction maps and full cover sequence"
	@echo "check-circle-cohomology  Homotopy, contractible charts and the actual H1 boundary quotient"
	@echo "check-projective-line-cohomology  Original affine charts, radial pullback and actual H2"
	@echo "check-projective-line-product  Focused P1 square build and axiom audit"
	@echo "check-projective-line-product-fibers  Focused fiber Chow/Betti build and axiom audit"
	@echo "check-projective-line-product-chow-realization  Focused product Chow-to-Betti map and axiom audit"
	@echo "check-circle-orientation  Native connecting representatives and positive-loop pairing"
	@echo "check-projective-line-period-comparison  Tensor extension, actual periods and ordinary Chow square"
	@echo "check-hodge-filtration  Brutal truncation, actual derived images and characteristic-two checks"
	@echo "check-projective-line-hodge  Independent Betti decomposition, geometric comparison and model witnesses"
	@echo "check-filtered-hodge-target  Proper-subspace control, scheme adapter and axiom audit"
	@echo "check-filtered-projector-defect  Exact detection, nonzero boundary control and axiom audit"
	@echo "check-tate-hodge-bridge  Tate-cutoff, proper-subspace and actual P1 compatibility checks"
	@echo "check-scheme-betti    Base and affine controls, original P1 periods and axiom audit"
	@echo "check-holomorphic-derham  Nonclosed-form controls, radial primitives, Kahler maps and axiom audit"
	@echo "check-intrinsic-poincare  Nonzero forms on actual schemes, local primitives and axiom audit"
	@echo "check-singular-sheaves  Actual cochain controls, canonical scheme resolution and axiom audit"
	@echo "check-holomorphic-descent  Nonzero forms, coordinate Jacobians, scheme maps and axiom audit"
	@echo "check-analytic-charts  Actual smooth schemes, chart evaluations and axiom audit"
	@echo "check-relative-cohomology  Kernel pairs, actual excision and positive boundary checks"
	@echo "check-projective-line-point-gysin  Local Thom orientation, original chart and zero-cycle checks"
	@echo "build-p1-double-cover  Positive-dimensional split P1 cover and native H2 aggregate"
	@echo "check-p1-double-cover  Ordinary Chow/native cochain comparison and rejection controls"
	@echo "build-geometric-cover-coverage  Original Chow/native Betti geometric cover aggregate"
	@echo "check-geometric-cover-coverage  Normalization, full coverage and axiom controls"
	@echo "build-galois-harmonic-coverage  Galois coefficient descent and quotient harmonic transport"
	@echo "check-galois-harmonic-coverage  Descent, faithful transport, rejection and axiom checks"
	@echo "build-finite-coverage  Exact modular rank and fixed-target aggregate coverage"
	@echo "check-finite-coverage  Gate rejection controls, execution and axiom audits"
	@echo "build-cover-harmonic-comparison  Actual circle/P1 cover, Chow and Hodge comparison"
	@echo "check-cover-harmonic-comparison  Nonzero differential controls and axiom audits"
	@echo "build-harmonic-witness  Finite harmonic certificates, descent and product coordinates"
	@echo "check-harmonic-witness  Focused controls and standard-three axiom audits"
	@echo "check-fixed-inertia  Focused statement and axiom checks for the DVR theorem"
	@echo "check-comparison     Comparison build, examples and axiom audits"
	@echo "check-integration    Full build and root-import inventory"
	@echo "check                All checks above"
	@echo "build-palomar        Existing fixed-ring Challenge and Solution only"
	@echo "check-palomar-proofs Local statement/axiom checks; independent replay is separate"
	@echo "check-palomar        Static submission preflight; reports preparation blockers"

build:
	$(LAKE) build

build-transfer:
	$(LAKE) build HodgeConjecture.Realization.Transfer

build-derham-core:
	$(LAKE) build HodgeConjecture.Realization.DeRham.Core

build-derham-components:
	$(LAKE) build HodgeConjecture.Realization.DeRham.AffineComponents

build-affine-line-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham.AffineLineComparison

build-chow:
	$(LAKE) build HodgeConjecture.Realization.Chow.FiniteFlatTransfer

build-graph-chow:
	$(LAKE) build HodgeConjecture.Correspondence.GraphChowBaseComparison

build-positive-degree:
	$(LAKE) build HodgeConjecture.Realization.DeRham.PositiveDegree HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass

build-scheme-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass

build-projective-line-betti:
	$(LAKE) build HodgeConjecture.Realization.Betti.ProjectiveLine

build-projective-line-periods:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods

build-small-chains:
	$(LAKE) build HodgeConjecture.Realization.Betti.SmallChains

build-open-cover-small-chains:
	$(LAKE) build HodgeConjecture.Realization.Betti.SmallChains

build-sheafification-kernel:
	$(LAKE) build HodgeConjecture.Realization.Betti.SchemeSingularSheaves HodgeConjecture.Realization.Betti.AffineSingularRealization

build-global-singular-sheaves:
	$(LAKE) build HodgeConjecture.Realization.Betti.SchemeSingularSheaves HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints

build-open-singular-sheaves: build-global-singular-sheaves

build-flasque-derived:
	$(LAKE) build HodgeConjecture.Realization.Betti.SchemeSingularSheaves HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints HodgeConjecture.Realization.Betti.ProjectiveLineCohomology HodgeConjecture.Realization.DeRham.AffineSheafAcyclicity

build-singular-derived-comparison: build-flasque-derived
	$(LAKE) build HodgeConjecture.Realization.DeRham.SheafHypercohomology

build-singular-constant-comparison: build-singular-derived-comparison
	$(LAKE) build HodgeConjecture.Geometry.ProjectiveLineSmooth

build-analytic-betti-comparison: build-singular-constant-comparison
	$(LAKE) build HodgeConjecture.Realization.DeRham.AnalyticBettiComparison HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison

build-singular-coefficient-change: build-analytic-betti-comparison
	$(LAKE) build HodgeConjecture.Realization.Betti.CoefficientChange HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure

build-complex-singular-comparison: build-singular-coefficient-change
	$(LAKE) build HodgeConjecture.Realization.Betti.SingularCoefficientTensorBridge HodgeConjecture.Realization.Betti.SingularCoefficientDerivedSquare HodgeConjecture.Realization.DeRham.AnalyticComplexSingularComparison HodgeConjecture.Realization.DeRham.ProjectiveLineHolomorphicComparisonIso

build-singular-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps

build-circle-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.Circle

build-projective-line-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.ProjectiveLineCohomology \
	  HodgeConjecture.Realization.Betti.ProjectiveLineDegreeOne

build-projective-line-product:
	$(LAKE) build HodgeConjecture.Geometry.AffineComplexPointsProduct \
	  HodgeConjecture.Geometry.ProjectiveLineProductComplexPoints \
	  HodgeConjecture.Geometry.ProjectiveLineProductTopology \
	  HodgeConjecture.Geometry.ProjectiveLineProductAffinePrime \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriers \
	  HodgeConjecture.Realization.Betti.ProductContractibleFactor \
	  HodgeConjecture.Realization.Betti.ProductSecondFactorCover \
	  HodgeConjecture.Realization.Betti.ProductSecondFactorH1Local \
	  HodgeConjecture.Realization.Betti.ProductSecondFactorH1Criterion \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductOverlapH1 \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductOverlapH1Spanning \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineChartH2 \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineOverlapH2 \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineOverlapTopology \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductAlmostSpanning \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanning \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanningCriterion \
	  HodgeConjecture.Realization.Betti.ProjectiveLineDegreeOne

build-projective-line-product-fibers:
	$(LAKE) build HodgeConjecture.Cycles.ProjectiveLineProductChowClasses \
	  HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberClassInputs \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberSupportedClass \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberChowBettiData \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberPairedWitness

build-projective-line-product-chow-realization:
	$(LAKE) build HodgeConjecture.Cycles.PrincipalRelationOfDivisor \
	  HodgeConjecture.Cycles.TopDegreePrincipalRelations \
	  HodgeConjecture.Cycles.RationalTopDegreeRelations \
	  HodgeConjecture.Cycles.UFDHeightOneLocalOrder \
	  HodgeConjecture.Cycles.UFDPrincipalDivisor \
	  HodgeConjecture.Cycles.UFDChowVanishing \
	  HodgeConjecture.Cycles.UFDZeroDivisorUnit \
	  HodgeConjecture.Cycles.SpecUFDZeroDivisorUnit \
	  HodgeConjecture.Cycles.GlobalUnitPrincipalDivisor \
	  HodgeConjecture.Cycles.BaseFieldScalarPrincipalDivisor \
	  HodgeConjecture.Cycles.BaseFieldScalarOpenTransport \
	  HodgeConjecture.Cycles.AffineProductScalarUnits \
	  HodgeConjecture.Cycles.ProjectiveLineProductAffineChowLocalization \
	  HodgeConjecture.Cycles.ProjectiveLineProductAffineChowVanishing \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroAffineChowLocalization \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroBoundaryGenerators \
	  HodgeConjecture.Geometry.ProjectiveLineProductIntegral \
	  HodgeConjecture.Cycles.ProjectiveLineProductGenericDegree \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroFiberRestriction \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroChartComplex \
	  HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriersDistinct \
	  HodgeConjecture.Cycles.ProjectiveLineProductFiberChowIndependence \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductChowFiberRealization

build-circle-orientation:
	$(LAKE) build HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing

build-projective-line-period-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison

build-hodge-filtration:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration

build-projective-line-hodge:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass

build-filtered-hodge-target:
	$(LAKE) build HodgeConjecture.Realization.FilteredHodgeTarget HodgeConjecture.Realization.DeRham.BettiHodgeTarget

build-filtered-projector-defect:
	$(LAKE) build HodgeConjecture.Inputs.ChowLocalization

build-tate-hodge-bridge:
	$(LAKE) build HodgeConjecture.Realization.HodgeTarget HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass

build-scheme-betti:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison

build-holomorphic-derham:
	$(LAKE) build HodgeConjecture.Realization.DeRham.HolomorphicPoincare HodgeConjecture.Realization.DeRham.HolomorphicKaehler

build-intrinsic-poincare:
	$(LAKE) build HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms HodgeConjecture.Realization.DeRham.HolomorphicPoincare

build-singular-sheaves:
	$(LAKE) build HodgeConjecture.Realization.Betti.SchemeSingularSheaves HodgeConjecture.Geometry.ProjectiveLineSmooth

build-holomorphic-descent:
	$(LAKE) build HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms

build-analytic-charts:
	$(LAKE) build HodgeConjecture.Geometry.Holomorphic.SchemeEvaluation HodgeConjecture.Geometry.ProjectiveLineSmooth

build-relative-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.RelativeMayerVietoris

build-projective-line-point-gysin:
	$(LAKE) build HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass

build-p1-double-cover:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineDoubleCoverCoverage

build-geometric-cover-coverage:
	$(LAKE) build HodgeConjecture.Realization.Betti.Examples.SplitGeometricCoverage

build-galois-harmonic-coverage:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineGaloisCoverage

build-finite-coverage:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

build-cover-harmonic-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineCoverHodgeComparison

build-harmonic-witness:
	$(LAKE) build HodgeConjecture.Realization.Chow.HarmonicWitness \
	  HodgeConjecture.Realization.Betti.ProjectiveLineProductHarmonicWitness

build-fixed-inertia:
	$(LAKE) build \
	  HodgeConjecture.Boundary.Normalization.PrimeInertia \
	  HodgeConjecture.Boundary.Normalization.DvrInertiaFixedRing \
	  HodgeConjecture.Boundary.Normalization.FixedInertiaEtaleBridge \
	  HodgeConjecture.Boundary.Normalization.LocalizationInertia \
	  HodgeConjecture.Boundary.Normalization.FixedRingLocalizationComparison \
	  HodgeConjecture.Boundary.Normalization.FixedRingAtPrimeComparison \
	  HodgeConjecture.Boundary.Normalization.FixedRingPrimeLocalization \
	  HodgeConjecture.Boundary.Normalization.HeightOneDvrBase \
	  HodgeConjecture.Boundary.Normalization.HeightOneDvrBaseChange \
	  HodgeConjecture.Boundary.Normalization.NormalizationFixedRingLocalization \
	  HodgeConjecture.Boundary.Normalization.NormalizationFixedRingPrimeComparison \
	  HodgeConjecture.Boundary.Normalization.FixedPointsBaseComparison \
	  HodgeConjecture.Boundary.Normalization.HeightOneDvrInertiaEtale \
	  HodgeConjecture.Boundary.Normalization.HeightOneInertiaGroupComparison \
	  HodgeConjecture.Boundary.Normalization.NormalizationActionComparison \
	  HodgeConjecture.Boundary.Normalization.NormalizationActionInertiaComparison \
	  HodgeConjecture.Boundary.Normalization.NormalizationActionFixedPointsComparison \
	  HodgeConjecture.Boundary.Normalization.NormalizationActionEtaleComparison \
	  HodgeConjecture.Boundary.Normalization.FixedPointsAtPrimeTower \
	  HodgeConjecture.Boundary.Normalization.FullInvariantBaseProperties \
	  HodgeConjecture.Boundary.Normalization.LocalizedEtaleTransport

build-betti:
	$(LAKE) build HodgeConjecture.Realization.Betti

build-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham

check-layers:
	$(PYTHON) scripts/check_layers.py

check-derham-core: check-layers build-derham-core
	$(LAKE) env lean research/DeRhamCoreVerification.lean

check-derham-components: check-layers build-derham-components
	$(LAKE) env lean research/DeRhamComponentsVerification.lean

check-affine-line-comparison: check-layers build-affine-line-comparison
	$(LAKE) env lean research/AffineLineComparisonVerification.lean

check-chow: build-chow
	$(LAKE) env lean research/FiniteFlatRankVerification.lean
	$(LAKE) env lean research/FiniteFlatChowVerification.lean

check-graph-chow: check-layers build-graph-chow
	$(LAKE) env lean research/GraphChowVerification.lean

check-positive-degree: check-layers build-positive-degree
	$(LAKE) env lean research/HigherDegreeVerification.lean

check-scheme-comparison: check-layers build-scheme-comparison
	$(LAKE) env lean research/SchemeComparisonVerification.lean

check-projective-line-betti: check-layers build-projective-line-betti
	$(LAKE) env lean research/SingularCochainsVerification.lean
	$(LAKE) env lean research/ProjectiveLineTopologyVerification.lean

check-projective-line-periods: check-layers build-projective-line-periods
	$(LAKE) env lean research/ProjectiveLinePeriodVerification.lean

check-small-chains: check-layers build-small-chains
	$(LAKE) build HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
	$(LAKE) env lean research/SingularSubcomplexVerification.lean
	$(LAKE) env lean research/SubcomplexCochainsVerification.lean
	$(LAKE) env lean research/SubcomplexChainVerification.lean
	$(LAKE) env lean research/AffineSingularVerification.lean
	$(LAKE) env lean research/SubdivisionGeometryVerification.lean
	$(LAKE) env lean research/NativeSimplexGeometryVerification.lean
	$(LAKE) env lean research/VertexSubdivisionVerification.lean
	$(LAKE) env lean research/BarycentricMeshVerification.lean
	$(LAKE) env lean research/SingularSubdivisionVerification.lean
	$(LAKE) env lean research/SingularSubdivisionSmallnessVerification.lean
	$(LAKE) env lean research/SmallSingularComparisonVerification.lean

check-singular-cohomology: check-layers build-singular-cohomology
	$(LAKE) build HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
	$(LAKE) env lean research/RationalDualVerification.lean
	$(LAKE) env lean research/CochainDualComparisonVerification.lean
	$(LAKE) env lean research/SingularMayerVietorisVerification.lean
	$(LAKE) env lean research/SingularMayerVietorisMapsVerification.lean

check-circle-cohomology: check-layers build-circle-cohomology
	$(LAKE) env lean research/SingularHomotopyVerification.lean
	$(LAKE) env lean research/CircleTopologyVerification.lean
	$(LAKE) env lean research/CircleCohomologyVerification.lean

check-projective-line-cohomology: check-layers build-projective-line-cohomology
	$(LAKE) env lean research/ProjectiveLineAnalyticCoverVerification.lean
	$(LAKE) env lean research/ProjectiveLineSingularCohomologyVerification.lean
	$(LAKE) env lean research/ProjectiveLineCohomologyVerification.lean

check-projective-line-product: check-layers build-projective-line-product
	$(LAKE) env lean research/ProjectiveLineProductVerification.lean

check-projective-line-product-fibers: check-layers build-projective-line-product-fibers
	$(LAKE) env lean research/ProjectiveLineProductFibersVerification.lean

check-projective-line-product-chow-realization: check-layers build-projective-line-product-chow-realization
	$(LAKE) env lean research/ProjectiveLineProductChowRealizationVerification.lean

check-circle-orientation: check-layers build-circle-orientation
	$(LAKE) env lean research/ConnectingRepresentativeVerification.lean
	$(LAKE) env lean research/SingularCyclePairingVerification.lean
	$(LAKE) env lean research/CircleOrientedCycleVerification.lean
	$(LAKE) env lean research/CircleOrientationVerification.lean

check-projective-line-period-comparison: check-layers build-projective-line-period-comparison
	$(LAKE) env lean research/ProjectiveLineBettiCycleClassVerification.lean
	$(LAKE) env lean research/LaurentOrientedArcsVerification.lean
	$(LAKE) env lean research/ProjectiveLinePeriodComparisonVerification.lean

check-hodge-filtration: check-layers build-hodge-filtration
	$(LAKE) build Mathlib.Algebra.Field.ZMod Mathlib.Data.Complex.Basic
	$(LAKE) env lean research/DegreeFiltrationVerification.lean
	$(LAKE) env lean research/ProjectiveLineHodgeFiltrationVerification.lean

check-projective-line-hodge: check-layers build-projective-line-hodge
	$(LAKE) env lean research/ProjectiveLineHodgeStructureVerification.lean
	$(LAKE) env lean research/ProjectiveLineHodgeComparisonVerification.lean

check-filtered-hodge-target: check-layers build-filtered-hodge-target
	$(LAKE) env lean research/FilteredHodgeTargetVerification.lean

check-filtered-projector-defect: check-layers build-filtered-projector-defect
	$(LAKE) env lean research/FilteredProjectorDefectVerification.lean

check-tate-hodge-bridge: check-layers build-tate-hodge-bridge
	$(LAKE) env lean research/TateHodgeGraphVerification.lean

check-scheme-betti: check-layers build-scheme-betti
	$(LAKE) env lean research/SchemeBettiVerification.lean

check-holomorphic-derham: check-layers build-holomorphic-derham
	$(LAKE) env lean research/HolomorphicDeRhamVerification.lean

check-intrinsic-poincare: check-layers build-intrinsic-poincare
	$(LAKE) env lean research/IntrinsicPoincareVerification.lean

check-singular-sheaves: check-layers build-singular-sheaves
	$(LAKE) env lean research/SingularSheavesVerification.lean

check-open-cover-small-chains: check-layers build-open-cover-small-chains
	$(LAKE) build HodgeConjecture.Realization.Betti.SingularSheafGlobalSections
	$(LAKE) env lean research/OpenCoverSmallChainsVerification.lean

check-sheafification-kernel: check-layers build-sheafification-kernel check-open-cover-small-chains
	$(LAKE) env lean research/SheafificationKernelVerification.lean

check-global-singular-sheaves: check-layers build-global-singular-sheaves check-sheafification-kernel
	$(LAKE) env lean research/GlobalSingularSheafVerification.lean

check-open-singular-sheaves: check-layers build-open-singular-sheaves check-global-singular-sheaves
	$(LAKE) env lean research/OpenSingularSheafVerification.lean

check-flasque-derived: check-layers build-flasque-derived check-open-singular-sheaves
	$(LAKE) env lean research/FlasqueDerivedVerification.lean

check-singular-derived-comparison: check-layers build-singular-derived-comparison check-flasque-derived
	$(LAKE) env lean research/SingularDerivedComparisonVerification.lean

check-singular-constant-comparison: check-layers build-singular-constant-comparison check-singular-derived-comparison
	$(LAKE) env lean research/SingularConstantSheafVerification.lean

check-analytic-betti-comparison: check-layers build-analytic-betti-comparison check-singular-constant-comparison
	$(LAKE) env lean research/AnalyticBettiComparisonVerification.lean

check-singular-coefficient-change: check-layers build-singular-coefficient-change check-analytic-betti-comparison
	$(LAKE) env lean research/SingularCoefficientChangeVerification.lean

check-complex-singular-comparison: check-layers build-complex-singular-comparison check-singular-coefficient-change
	$(LAKE) env lean research/SingularCoefficientGlobalUnitVerification.lean
	$(LAKE) env lean research/SingularCoefficientDerivedSquareVerification.lean
	$(LAKE) env lean research/ComplexSingularOpenRestrictionVerification.lean
	$(LAKE) env lean research/ComplexSingularConstantSheafVerification.lean
	$(LAKE) env lean research/AnalyticComplexSingularComparisonVerification.lean
	$(LAKE) env lean research/ProjectiveLineHolomorphicComparisonIsoVerification.lean
	$(LAKE) env lean research/DerivedScalarRestrictionNaturalityVerification.lean

check-holomorphic-descent: check-layers build-holomorphic-descent
	$(LAKE) env lean research/HolomorphicDescentVerification.lean

check-analytic-charts: check-layers build-analytic-charts
	$(LAKE) env lean research/AnalyticChartsVerification.lean

check-relative-cohomology: check-layers build-relative-cohomology
	$(LAKE) build HodgeConjecture.Realization.Betti.Circle
	$(LAKE) env lean research/RelativeCochainsVerification.lean
	$(LAKE) env lean research/RelativeExcisionVerification.lean

check-projective-line-point-gysin: check-layers build-projective-line-point-gysin
	$(LAKE) env lean research/ComplexPointThomVerification.lean
	$(LAKE) env lean research/ProjectiveLineNormalChartVerification.lean
	$(LAKE) env lean research/ProjectiveLinePointGysinVerification.lean

check-p1-double-cover: check-layers build-p1-double-cover
	$(LAKE) env lean research/ProjectiveLineDoubleCoverVerification.lean

check-geometric-cover-coverage: check-layers build-geometric-cover-coverage
	$(LAKE) env lean research/GeometricCoverCoverageVerification.lean

check-galois-harmonic-coverage: check-finite-coverage build-galois-harmonic-coverage
	$(LAKE) env lean research/GaloisHarmonicCoverageVerification.lean

check-finite-coverage: check-layers build-finite-coverage
	$(LAKE) env lean research/FiniteCoverageCertificateVerification.lean

check-cover-harmonic-comparison: check-layers build-cover-harmonic-comparison
	$(LAKE) env lean research/CoverHarmonicComparisonVerification.lean

check-harmonic-witness: check-layers build-harmonic-witness
	$(LAKE) env lean research/HarmonicWitnessVerification.lean

check-fixed-inertia: build-fixed-inertia
	$(LAKE) env lean research/FixedInertiaVerification.lean

check-comparison: build-comparison
	$(LAKE) env lean research/DeRhamVerification.lean

check-integration: build
	$(LAKE) env lean research/Verification.lean

build-palomar:
	$(LAKE) build Challenge Solution

check-palomar-proofs: build-palomar
	$(LAKE) env lean research/PalomarVerification.lean

check-palomar:
	$(PYTHON) scripts/check_palomar.py

check: check-derham-core check-derham-components check-affine-line-comparison check-positive-degree check-scheme-comparison check-projective-line-betti check-projective-line-periods check-small-chains check-open-cover-small-chains check-sheafification-kernel check-global-singular-sheaves check-open-singular-sheaves check-flasque-derived check-singular-derived-comparison check-singular-constant-comparison check-analytic-betti-comparison check-singular-coefficient-change check-complex-singular-comparison check-singular-cohomology check-circle-cohomology check-projective-line-cohomology check-circle-orientation check-projective-line-period-comparison check-hodge-filtration check-projective-line-hodge check-filtered-hodge-target check-filtered-projector-defect check-tate-hodge-bridge check-scheme-betti check-holomorphic-derham check-analytic-charts check-holomorphic-descent check-intrinsic-poincare check-singular-sheaves check-relative-cohomology check-projective-line-point-gysin check-chow check-graph-chow check-comparison check-integration check-projective-line-product check-projective-line-product-fibers check-projective-line-product-chow-realization check-harmonic-witness check-cover-harmonic-comparison check-finite-coverage check-galois-harmonic-coverage check-geometric-cover-coverage check-p1-double-cover
