"""Keep standalone build layers independent of their downstream consumers."""

from collections import deque
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
RULES = {
    "HodgeConjecture.LinearAlgebra.Harmonic.Cohomology": (
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Correspondence",
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Geometry",
        "HodgeConjecture.Realization",
        "HodgeConjecture.Inputs",
        "HodgeConjecture.SheafCohomology",
    ),
    "HodgeConjecture.Correspondence.FilteredProjectorDefect": (
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Geometry",
        "HodgeConjecture.Realization",
        "HodgeConjecture.Inputs",
        "HodgeConjecture.SheafCohomology",
    ),
    "HodgeConjecture.Boundary.FilteredProjectorDefect": (
        "HodgeConjecture.Realization",
        "HodgeConjecture.Inputs.ChowLocalization",
    ),
    "HodgeConjecture.Realization.DeRham.Core": (
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Correspondence",
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Realization.Chow",
        "HodgeConjecture.Realization.Betti",
        "HodgeConjecture.Realization.DeRham.AffineGeometricDegree",
        "HodgeConjecture.Realization.DeRham.SplitComparison",
        "HodgeConjecture.Realization.DeRham.AffineLineComparison",
    ),
    "HodgeConjecture.Realization.Chow.FiniteFlatTransfer": (
        "HodgeConjecture.Realization.Betti",
        "HodgeConjecture.Realization.DeRham",
    ),
    "HodgeConjecture.Realization.Betti": (
        "HodgeConjecture.Realization.DeRham",
    ),
    "HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses": (
        "HodgeConjecture.Realization.DeRham",
    ),
}
RULES["HodgeConjecture.Realization.DeRham.AffineComponents"] = RULES[
    "HodgeConjecture.Realization.DeRham.Core"
]
RULES["HodgeConjecture.Realization.DeRham.AffineLineComparison"] = (
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham.AffineGeometricDegree",
    "HodgeConjecture.Realization.DeRham.SplitComparison",
)
RULES["HodgeConjecture.Correspondence.GraphChowBaseComparison"] = (
    "HodgeConjecture.Collision",
    "HodgeConjecture.Realization",
)
RULES["HodgeConjecture.Realization.DeRham.PositiveDegree"] = (
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.DeRham.AffineGeometricDegree",
    "HodgeConjecture.Realization.DeRham.AffineLineComparison",
    "HodgeConjecture.Realization.DeRham.SplitComparison",
)
RULES["HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass"] = (
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence.GraphChowAlgebra",
    "HodgeConjecture.Correspondence.GraphChowBaseComparison",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.DeRham.AffineGeometricDegree",
    "HodgeConjecture.Realization.DeRham.AffineLineComparison",
    "HodgeConjecture.Realization.DeRham.SplitComparison",
)
RULES["HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison"] = (
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti",
)
RULES["HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass"] = RULES[
    "HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass"
]
RULES["HodgeConjecture.Realization.Betti.SingularCochains"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.SheafCohomology",
)
RULES["HodgeConjecture.Realization.Betti.SimplicialCochains"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
] + (
    "HodgeConjecture.Realization.Betti.SingularDegreeZero",
    "HodgeConjecture.Realization.Betti.SingularCochains",
    "HodgeConjecture.Realization.Betti.SubcomplexCochains",
)
RULES["HodgeConjecture.Realization.Betti.SmallChains"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
for entry in (
    "HodgeConjecture.Realization.Betti.SubcomplexOperators",
    "HodgeConjecture.Realization.Betti.SingularSupportedChains",
    "HodgeConjecture.Realization.Betti.SingularSubdivisionIteration",
    "HodgeConjecture.Realization.Betti.CoverSingular",
    "HodgeConjecture.Realization.Betti.CoverSubdivisionSmallness",
    "HodgeConjecture.Realization.Betti.CoverSubdivisionHomotopy",
    "HodgeConjecture.Realization.Betti.CoverSmallChains",
    "HodgeConjecture.Realization.Betti.CoverSmallCochains",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.Betti.SingularCochains"]
RULES["HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
RULES["HodgeConjecture.Realization.Betti.Examples.CircleCohomology"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
RULES["HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology"] = (
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.SheafCohomology",
)
RULES["HodgeConjecture.Realization.Betti.ProjectiveLineCohomology"] = RULES[
    "HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology"
]
RULES["HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
for entry in (
    "HodgeConjecture.Realization.Betti.ProjectiveLineOrientation",
    "HodgeConjecture.Realization.Betti.ProjectiveLineComplexification",
):
    RULES[entry] = RULES[
        "HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology"
    ]
RULES["HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass"] = (
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence.GraphChowAlgebra",
    "HodgeConjecture.Correspondence.GraphChowBaseComparison",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.SheafCohomology",
)
RULES["HodgeConjecture.Realization.DeRham.LaurentPeriods"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.SheafCohomology",
)
RULES["HodgeConjecture.Realization.DeRham.LaurentOrientedArcs"] = RULES[
    "HodgeConjecture.Realization.DeRham.LaurentPeriods"
]
for entry in (
    "HodgeConjecture.Realization.DeRham.Core",
    "HodgeConjecture.Realization.DeRham.AffineComponents",
    "HodgeConjecture.Realization.DeRham.AffineLineComparison",
    "HodgeConjecture.Realization.DeRham.PositiveDegree",
    "HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass",
):
    RULES[entry] += ("HodgeConjecture.SheafCohomology",)

for entry in (
    "HodgeConjecture.Realization.DeRham.Core",
    "HodgeConjecture.Realization.DeRham.AffineComponents",
    "HodgeConjecture.Realization.DeRham.PositiveDegree",
    "HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass",
    "HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison",
    "HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass",
):
    RULES[entry] += (
        "HodgeConjecture.Realization.DeRham.LaurentPeriods",
        "HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods",
    )

RULES["HodgeConjecture.Realization.DeRham.DegreeFiltration"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.SheafCohomology",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Transfer",
    "HodgeConjecture.Realization.FiberSum",
    "HodgeConjecture.Realization.HodgeClasses",
    "HodgeConjecture.Realization.HodgeTarget",
    "HodgeConjecture.Realization.DeRham.SheafComplex",
    "HodgeConjecture.Realization.DeRham.SheafHypercohomology",
    "HodgeConjecture.Realization.DeRham.TwoTermHypercohomology",
    "HodgeConjecture.Realization.DeRham.TwoTermDegreeFiltration",
    "HodgeConjecture.Realization.DeRham.HypercohomologyFiltration",
    "HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration",
    "HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration",
)
RULES["HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Collision",
)
RULES["HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration"] = RULES[
    "HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison"
]
RULES["HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure"] = RULES[
    "HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology"
] + ("HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass",)

RULES["HodgeConjecture.Realization.HodgeFiltration"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.SheafCohomology",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.HodgeClasses",
    "HodgeConjecture.Realization.HodgeTarget",
)
RULES["HodgeConjecture.Realization.FilteredHodgeTarget"] = tuple(
    forbidden for forbidden in RULES["HodgeConjecture.Realization.HodgeFiltration"]
    if forbidden != "HodgeConjecture.Realization.HodgeClasses"
)
RULES["HodgeConjecture.Realization.TateHodgeStructure"] = RULES[
    "HodgeConjecture.Realization.HodgeFiltration"
]
RULES["HodgeConjecture.Realization.HodgeTransport"] = RULES[
    "HodgeConjecture.Realization.HodgeFiltration"
]
for entry in (
    "HodgeConjecture.Geometry.ComplexPoints",
    "HodgeConjecture.Geometry.ComplexPointsFunctoriality",
    "HodgeConjecture.Geometry.AffineComplexPoints",
    "HodgeConjecture.Geometry.PolynomialComplexPoints",
    "HodgeConjecture.Geometry.EtaleAnalyticCoordinates",
    "HodgeConjecture.Geometry.SmoothComplexManifold",
    "HodgeConjecture.Geometry.LocallyContractible",
    "HodgeConjecture.Geometry.ProjectiveLineSmooth",
    "HodgeConjecture.Geometry.Holomorphic.SchemeEvaluation",
    "HodgeConjecture.Geometry.SectionAlgebra",
    "HodgeConjecture.Geometry.Holomorphic.FunctionAlgebra",
    "HodgeConjecture.Geometry.Holomorphic.Pullback",
    "HodgeConjecture.Geometry.Holomorphic.Wedge",
    "HodgeConjecture.Geometry.Holomorphic.Atlas",
    "HodgeConjecture.Geometry.Holomorphic.AtlasCoordinates",
    "HodgeConjecture.Geometry.Holomorphic.AtlasPoincare",
):
    RULES[entry] = (
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Correspondence",
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Inputs",
        "HodgeConjecture.Realization",
        "HodgeConjecture.SheafCohomology",
    )
RULES["HodgeConjecture.Realization.Betti.Scheme"] = (
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.Realization.Betti.Examples",
)
for entry in (
    "HodgeConjecture.Realization.Betti.SingularPresheaf",
    "HodgeConjecture.Realization.Betti.SchemeSingularSheaves",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.Betti.Scheme"]
for entry in (
    "HodgeConjecture.Realization.Betti.SingularLocallyZero",
    "HodgeConjecture.Realization.Betti.SingularLocalExactness",
    "HodgeConjecture.Realization.Betti.SingularSheafResolution",
    "HodgeConjecture.Realization.Betti.SingularSheafificationKernel",
    "HodgeConjecture.Realization.Betti.SingularCochainPatching",
    "HodgeConjecture.Realization.Betti.SingularSheafGlobalSections",
    "HodgeConjecture.Realization.Betti.SingularOpenRestriction",
    "HodgeConjecture.Realization.Betti.SingularSheafAcyclicity",
    "HodgeConjecture.Realization.Betti.SingularSheafHypercohomology",
    "HodgeConjecture.Realization.Betti.SingularConstantSheafCohomology",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.Betti.Scheme"] + (
        "HodgeConjecture.Geometry",
    )
for entry in (
    "HodgeConjecture.Geometry.Holomorphic.Forms",
    "HodgeConjecture.Geometry.Holomorphic.LowDegree",
    "HodgeConjecture.Geometry.Holomorphic.Poincare",
    "HodgeConjecture.Geometry.Holomorphic.Dimension",
    "HodgeConjecture.Geometry.Holomorphic.Contraction",
    "HodgeConjecture.Geometry.Holomorphic.ParameterIntegral",
    "HodgeConjecture.Geometry.Holomorphic.RadialHomotopy",
    "HodgeConjecture.SheafCohomology.LocalExactness",
    "HodgeConjecture.Realization.DeRham.HolomorphicComplex",
    "HodgeConjecture.Realization.DeRham.HolomorphicPoincare",
):
    RULES[entry] = (
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Correspondence",
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Inputs",
        "HodgeConjecture.Realization.Betti",
        "HodgeConjecture.Realization.Chow",
        "HodgeConjecture.CommutativeAlgebra",
        "HodgeConjecture.Realization.DeRham.PresheafComplex",
    )
RULES["HodgeConjecture.Realization.DeRham.HolomorphicAtlasPoincare"] = RULES[
    "HodgeConjecture.Realization.DeRham.HolomorphicPoincare"
]
RULES["HodgeConjecture.Realization.DeRham.HolomorphicHypercohomology"] = RULES[
    "HodgeConjecture.Realization.DeRham.HolomorphicPoincare"
]
RULES["HodgeConjecture.LinearAlgebra.HomCoefficients"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Realization",
    "HodgeConjecture.SheafCohomology",
    "HodgeConjecture.CommutativeAlgebra",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Inputs",
)
RULES["HodgeConjecture.Realization.Betti.CoefficientChange"] = (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.SheafCohomology",
    "HodgeConjecture.CommutativeAlgebra",
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.Realization.Betti.Examples",
    "HodgeConjecture.Realization.Betti.ProjectiveLine",
)
RULES["HodgeConjecture.Realization.DeRham.AnalyticBettiComparison"] = (
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.CommutativeAlgebra",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti.Examples",
    "HodgeConjecture.Realization.Betti.ProjectiveLine",
    "HodgeConjecture.Realization.DeRham.ProjectiveLine",
)
for entry in (
    "HodgeConjecture.SheafCohomology.ConstantLift",
    "HodgeConjecture.SheafCohomology.SheafifyKernel",
    "HodgeConjecture.SheafCohomology.SheafifyLocalLifts",
    "HodgeConjecture.SheafCohomology.SheafifyOpen",
    "HodgeConjecture.SheafCohomology.ComplexKernel",
    "HodgeConjecture.SheafCohomology.ComplexKernelComparison",
    "HodgeConjecture.SheafCohomology.DerivedPostcompose",
    "HodgeConjecture.SheafCohomology.FlasqueDerived",
    "HodgeConjecture.SheafCohomology.Hypercohomology",
    "HodgeConjecture.SheafCohomology.HypercohomologyComparison",
    "HodgeConjecture.SheafCohomology.ScalarRestriction",
    "HodgeConjecture.SheafCohomology.DerivedScalarRestriction",
    "HodgeConjecture.SheafCohomology.FlasqueComplex",
    "HodgeConjecture.SheafCohomology.FlasqueHypercohomology",
    "HodgeConjecture.SheafCohomology.LinearSheaves",
    "HodgeConjecture.SheafCohomology.AugmentedComplex",
):
    RULES[entry] = (
        "HodgeConjecture.Geometry",
        "HodgeConjecture.Realization",
        "HodgeConjecture.CommutativeAlgebra",
        "HodgeConjecture.Cycles",
        "HodgeConjecture.Correspondence",
        "HodgeConjecture.Boundary",
        "HodgeConjecture.Collision",
        "HodgeConjecture.Inputs",
    )
RULES["HodgeConjecture.Realization.DeRham.HolomorphicKaehler"] = tuple(
    forbidden for forbidden in RULES["HodgeConjecture.Realization.DeRham.HolomorphicComplex"]
    if forbidden not in (
        "HodgeConjecture.CommutativeAlgebra",
        "HodgeConjecture.Realization.DeRham.PresheafComplex",
    )
)
for entry in (
    "HodgeConjecture.Realization.DeRham.HolomorphicAtlasComplex",
    "HodgeConjecture.Realization.DeRham.HolomorphicFormsMap",
    "HodgeConjecture.Realization.DeRham.HolomorphicFormsNaturality",
    "HodgeConjecture.Realization.DeRham.HolomorphicFormsDifferential",
    "HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.DeRham.HolomorphicKaehler"]
for entry in (
    "HodgeConjecture.Geometry.Holomorphic.Forms",
    "HodgeConjecture.Geometry.Holomorphic.LowDegree",
    "HodgeConjecture.Geometry.Holomorphic.Poincare",
    "HodgeConjecture.Geometry.Holomorphic.Dimension",
    "HodgeConjecture.Geometry.Holomorphic.Contraction",
    "HodgeConjecture.Geometry.Holomorphic.ParameterIntegral",
    "HodgeConjecture.Geometry.Holomorphic.RadialHomotopy",
):
    RULES[entry] += (
        "HodgeConjecture.Realization",
        "HodgeConjecture.SheafCohomology",
    )
RULES["HodgeConjecture.SheafCohomology.LocalExactness"] += (
    "HodgeConjecture.Geometry",
    "HodgeConjecture.Realization",
)
RULES["HodgeConjecture.Realization.Chow.FilteredTateGraphProjector"] = (
    "HodgeConjecture.Realization.Betti",
    "HodgeConjecture.Realization.DeRham",
    "HodgeConjecture.Inputs",
)
RULES["HodgeConjecture.Realization.DeRham.BettiHodgeTarget"] = (
    "HodgeConjecture.Cycles",
    "HodgeConjecture.Boundary",
    "HodgeConjecture.Collision",
    "HodgeConjecture.Correspondence",
    "HodgeConjecture.Inputs",
    "HodgeConjecture.Realization.Chow",
    "HodgeConjecture.Realization.Betti.Examples",
    "HodgeConjecture.Realization.Betti.ProjectiveLine",
    "HodgeConjecture.Realization.HodgeClasses",
    "HodgeConjecture.Realization.HodgeTarget",
)

for entry in (
    "HodgeConjecture.Realization.Betti.RelativeCochains",
    "HodgeConjecture.Realization.Betti.ShortExactQuasiIso",
    "HodgeConjecture.Realization.Betti.RelativeUnion",
    "HodgeConjecture.Realization.Betti.RelativeExcision",
    "HodgeConjecture.Realization.Betti.RelativeMayerVietoris",
    "HodgeConjecture.Realization.Betti.Examples.ComplexPointThom",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.Betti.SingularCochains"]

for entry in (
    "HodgeConjecture.Realization.Betti.Examples.ProjectiveLinePointSupport",
    "HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChart",
    "HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChartBoundary",
):
    RULES[entry] = RULES["HodgeConjecture.Realization.Betti.ProjectiveLineCohomology"]

RULES["HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin"] = RULES[
    "HodgeConjecture.Realization.Betti.ProjectiveLineCohomology"
] + (
    "HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass",
    "HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass",
)
RULES["HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass"] = RULES[
    "HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass"
]


RULES["HodgeConjecture.Realization.Betti.CircleCoverHarmonicComparison"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
RULES["HodgeConjecture.Realization.Betti.ProjectiveLineCoverHarmonicComparison"] = (
    "HodgeConjecture.Realization.DeRham",
)


def without_comments(source):
    """Remove line comments and nested Lean block comments before reading imports."""
    result = []
    depth = 0
    index = 0
    while index < len(source):
        pair = source[index : index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            result.append(" ")
            index += 2
        elif not depth and pair == "--":
            index = source.find("\n", index)
            if index == -1:
                break
        else:
            if not depth or source[index] == "\n":
                result.append(source[index])
            index += 1
    return "".join(result)


def project_imports(module):
    path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    source = without_comments(path.read_text())
    imports = []
    for match in re.finditer(r"^(?:(?:public|private)\s+)?import\s+([^\n]+)", source, re.M):
        imports.extend(name for name in match[1].split() if name.startswith("HodgeConjecture"))
    return imports


def check_layers():
    failed = False
    for entry, forbidden in RULES.items():
        pending = deque([(entry, [entry])])
        seen = set()
        while pending:
            module, chain = pending.popleft()
            if module in seen:
                continue
            seen.add(module)
            # This extracted leaf only contains the original structure-map section algebras.
            # Scheme filtration may use it, while every analytic/concrete geometry module
            # remains forbidden. The leaf check below also prevents adding project inputs.
            shared_section_leaf = (
                entry == "HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration"
                and module == "HodgeConjecture.Geometry.SectionAlgebra"
            )
            if not shared_section_leaf and any(
                module == prefix or module.startswith(prefix + ".") for prefix in forbidden
            ):
                print("FAIL import boundary: " + " -> ".join(chain), file=sys.stderr)
                failed = True
                continue
            pending.extend((name, chain + [name]) for name in project_imports(module))
        if entry == "HodgeConjecture.Geometry.SectionAlgebra" and len(seen) != 1:
            print("FAIL shared section algebra must remain a project-independent leaf", file=sys.stderr)
            failed = True
        print(f"Checked {entry}: {len(seen)} project modules")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(check_layers())
