"""Keep standalone build layers independent of their downstream consumers."""

from collections import deque
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
RULES = {
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
RULES["HodgeConjecture.Realization.Betti.SmallChains"] = RULES[
    "HodgeConjecture.Realization.Betti.SingularCochains"
]
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
            if any(module == prefix or module.startswith(prefix + ".") for prefix in forbidden):
                print("FAIL import boundary: " + " -> ".join(chain), file=sys.stderr)
                failed = True
                continue
            pending.extend((name, chain + [name]) for name in project_imports(module))
        print(f"Checked {entry}: {len(seen)} project modules")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(check_layers())
