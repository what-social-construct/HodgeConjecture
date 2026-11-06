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

check: check-derham-core check-derham-components check-affine-line-comparison check-positive-degree check-scheme-comparison check-chow check-graph-chow check-comparison check-integration
