module

public import HodgeConjecture.Realization.DeRham.AffineCohomology
public import HodgeConjecture.Realization.DeRham.CohomologyProduct
public import HodgeConjecture.Realization.DeRham.Logarithmic
public import HodgeConjecture.Realization.DeRham.LaurentDifferentials
public import HodgeConjecture.Realization.DeRham.LaurentLogarithmicRegulator
public import HodgeConjecture.Realization.DeRham.MilnorRegulator
public import HodgeConjecture.Realization.DeRham.TorusResidue
public import HodgeConjecture.Realization.DeRham.ProjectiveLineChern

@[expose] public section

/-!
# Positive-degree algebraic realizations and the ordinary Čech first Chern class

The original Kähler de Rham complex supplies actual closed/exact quotients
in every degree, the H¹ × H¹ cup product, and logarithmic unit/symbol
regulators. Laurent residues prove nonvanishing. On the actual two-chart
projective line the ordinary first-Chern formula descends through changes
of trivialization into categorical total degree-two cohomology.

The main target remains the ordinary Chow-to-Hodge cycle map. The separate
ProjectiveLineCycleClass entry point constructs the ordinary Chow-source
map by the proved principal-divisor degree law. An identification of the
entire transition quotient with the ordinary Chow group and the Čech target
with scheme/singular cohomology remain separate comparisons. The auxiliary
Milnor-symbol realization does not replace them.
-/
