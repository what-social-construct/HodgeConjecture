.DEFAULT_GOAL := help
.NOTPARALLEL:

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
        build-singular-cohomology check-singular-cohomology \
        build-circle-cohomology check-circle-cohomology \
        build-projective-line-cohomology check-projective-line-cohomology \
        build-circle-orientation check-circle-orientation \
        build-projective-line-period-comparison check-projective-line-period-comparison \
        build-hodge-filtration check-hodge-filtration \
        build-projective-line-hodge check-projective-line-hodge \
        build-relative-cohomology check-relative-cohomology \
        build-projective-line-point-gysin check-projective-line-point-gysin \
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
	@echo "build-singular-cohomology  Exact rational duals and full singular Mayer-Vietoris"
	@echo "build-circle-cohomology  Actual circle singular H1 and cover generator"
	@echo "build-projective-line-cohomology  Actual P1 rational singular H2 and cover generator"
	@echo "build-circle-orientation  Actual positive cycle and generator pairing"
	@echo "build-projective-line-period-comparison  Actual boundary periods and ordinary cycle maps"
	@echo "build-hodge-filtration  Actual derived degree filtration and P1 H2 calculation"
	@echo "build-projective-line-hodge  Geometric type (1,1) and the fixed P1 Hodge-cycle model"
	@echo "build-relative-cohomology  Actual relative cochains, excision and connecting signs"
	@echo "build-projective-line-point-gysin  Oriented zero-point Gysin and ordinary cycle comparison"
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
	@echo "check-singular-cohomology  Duality, original restriction maps and full cover sequence"
	@echo "check-circle-cohomology  Homotopy, contractible charts and the actual H1 boundary quotient"
	@echo "check-projective-line-cohomology  Original affine charts, radial pullback and actual H2"
	@echo "check-circle-orientation  Native connecting representatives and positive-loop pairing"
	@echo "check-projective-line-period-comparison  Tensor extension, actual periods and ordinary Chow square"
	@echo "check-hodge-filtration  Brutal truncation, actual derived images and characteristic-two checks"
	@echo "check-projective-line-hodge  Independent Betti decomposition, geometric comparison and model witnesses"
	@echo "check-relative-cohomology  Kernel pairs, actual excision and positive boundary checks"
	@echo "check-projective-line-point-gysin  Local Thom orientation, original chart and zero-cycle checks"
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

build-singular-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps

build-circle-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.Circle

build-projective-line-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.ProjectiveLineCohomology

build-circle-orientation:
	$(LAKE) build HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing

build-projective-line-period-comparison:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison

build-hodge-filtration:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration

build-projective-line-hodge:
	$(LAKE) build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass

build-relative-cohomology:
	$(LAKE) build HodgeConjecture.Realization.Betti.RelativeMayerVietoris

build-projective-line-point-gysin:
	$(LAKE) build HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass

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

check-relative-cohomology: check-layers build-relative-cohomology
	$(LAKE) build HodgeConjecture.Realization.Betti.Circle
	$(LAKE) env lean research/RelativeCochainsVerification.lean
	$(LAKE) env lean research/RelativeExcisionVerification.lean

check-projective-line-point-gysin: check-layers build-projective-line-point-gysin
	$(LAKE) env lean research/ComplexPointThomVerification.lean
	$(LAKE) env lean research/ProjectiveLineNormalChartVerification.lean
	$(LAKE) env lean research/ProjectiveLinePointGysinVerification.lean

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

check: check-derham-core check-derham-components check-affine-line-comparison check-positive-degree check-scheme-comparison check-projective-line-betti check-projective-line-periods check-small-chains check-singular-cohomology check-circle-cohomology check-projective-line-cohomology check-circle-orientation check-projective-line-period-comparison check-hodge-filtration check-projective-line-hodge check-relative-cohomology check-projective-line-point-gysin check-chow check-graph-chow check-comparison check-integration
