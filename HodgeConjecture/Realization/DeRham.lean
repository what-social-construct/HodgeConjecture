module

public import HodgeConjecture.Realization.DeRham.Core
public import HodgeConjecture.Realization.DeRham.AffineComponents
public import HodgeConjecture.Realization.DeRham.AffineLineComparison
public import HodgeConjecture.Realization.DeRham.PositiveDegree
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
public import HodgeConjecture.Realization.DeRham.AffineGeometricDegree
public import HodgeConjecture.Realization.DeRham.SplitComparison

@[expose] public section

/-!
# Constructed algebraic de Rham objects and bounded realizations

The affine de Rham complex is constructed for every commutative algebra.
Its degree-zero homology is identified with the actual universal-derivation
kernel. Formally unramified algebras carry an algebra-trace map on these
kernels, with the degree computed from a finite basis and identified with
the original affine scheme map's geometric rank and cycle-fiber degree.

For finite split complex schemes, the de Rham cycle-class map commutes with
the existing geometric Chow maps and compares to the genuine tensor
complexification of rational singular cohomology. Both pullback and trace
intertwine. Scheme hypercohomology, the general finite-syntomic trace, and
general positive-dimensional Betti/Hodge comparison remain separate constructions.
For the complex affine line, the degree-zero comparison with genuine
complexified rational singular cohomology is constructed and agrees with
point evaluation, multiplication and polynomial pullback.

Positive degrees now have actual closed/exact quotients identified with
categorical homology, an H¹ × H¹ cup product, and nonzero logarithmic
regulators. The actual projective-line cover carries an ordinary Čech
first-Chern map into total degree two, invariant under both local
trivializations and detected by Laurent residue. On the actual projective
line over an algebraically closed field, the principal-divisor degree law
now descends through the original integral/rational Chow quotients. Over
characteristic zero the resulting rational cycle map has the actual Čech
degree-two target and coefficient-one point normalization. General
singular-target comparison and prescribed-class coverage remain open.
For P¹ the original Čech target is now compared with actual scheme de Rham
hypercohomology. Its analytic Laurent unit-circle integral descends through
the original boundaries and this scheme comparison, with Chern period
`2πi` and normalized rational Chow period equal to rational degree.
-/
