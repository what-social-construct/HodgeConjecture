module

public import HodgeConjecture.Realization.DeRham.Core
public import HodgeConjecture.Realization.DeRham.AffineComponents
public import HodgeConjecture.Realization.DeRham.AffineLineComparison
public import HodgeConjecture.Realization.DeRham.PositiveDegree
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverHodgeComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate
public import HodgeConjecture.Realization.DeRham.ProjectiveLineGaloisCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineDoubleCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
public import HodgeConjecture.Realization.DeRham.HolomorphicPoincare
public import HodgeConjecture.Realization.DeRham.HolomorphicKaehler
public import HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms
public import HodgeConjecture.Realization.DeRham.AnalyticBettiComparison
public import HodgeConjecture.Realization.DeRham.AnalyticComplexSingularComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHolomorphicComparisonIso
public import HodgeConjecture.Geometry.Holomorphic.SchemeEvaluation
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import HodgeConjecture.Realization.DeRham.AffineGeometricDegree
public import HodgeConjecture.Realization.DeRham.SplitComparison

@[expose] public section

/-!
# Constructed de Rham complexes and bounded comparisons

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
The explicit positive circle cycle now fixes the original singular cover
generator's boundary-loop sign. The actual boundary period uniquely
specifies an equivalence to the genuine tensor complexification of P¹
singular H². The unnormalized Chern class retains its factor `2πi`;
normalizing the period gives the square for the independently constructed
ordinary Chow-to-singular map. This bounded period comparison does not
identify a separately constructed general analytic or Gysin comparison.
The actual degree filtration of the sheaf de Rham complex now computes
P¹'s H² filtration over every field: F¹ is all and F² is zero. The actual
derived inclusion fixes this calculation. Over ℂ its bounded period
comparison agrees with the independently specified type-(1,1) Betti
decomposition and rational conjugation. This gives a fixed-codimension
Hodge-cycle model with an explicit infinity-class witness for every
target class. General degeneration and analytic/Gysin identification
remain separate obligations.
The original P¹ point space is now identified with the canonical scheme
complex-point space. The actual homeomorphism pullbacks carry this same
period comparison, derived filtration, pure structure and ordinary Chow
square to the canonical singular Betti target.

On complex coordinate spaces, the actual holomorphic sheaf complex now
uses native complex-smooth alternating-form sections and exterior
derivatives. Restriction, d² = 0 and the constant-sheaf augmentation are
proved. The actual complex-smooth radial operator satisfies dK + Kd = id
in every positive degree, giving the full local sheaf quasi-isomorphism
in every coordinate dimension. Its degree-one specialization equals the
existing segment primitive. The existing Kähler universal property and
pullback give the actual analytic map in degree one, with polynomial
evaluation constructed. Canonical points of schemes smooth of fixed
relative dimension now carry a constructed native complex analytic atlas.
Regular functions and scheme morphisms are analytic, and original section
evaluations give actual holomorphic algebra maps on opens and charts.
Coordinate forms and their differential now descend through this atlas
as an intrinsic sheaf complex. The all-degree algebraic forms map uses
the same original section algebras and Kähler exterior powers, extends
the existing degree-one map, and commutes with d and original restrictions.
The intrinsic complex now has actual local chart identifications and
local primitives. Its native constant-sheaf augmentation is a full sheaf
quasi-isomorphism. This original resolution now identifies ordinary
derived sections of the native complex constant sheaf with intrinsic
holomorphic hypercohomology. Coefficient inclusion and the original
rational singular comparison construct a complex-linear map from the
existing tensor complexification to that actual analytic target. It
detects zero on the rational diagonal, including the nonzero original
P¹ generator. Invertibility of this coefficient comparison, proper
algebraic/analytic comparison, general periods and purity remain open.
The separately named cochain-induced composite through unrestricted complex
singular cohomology is invertible under finite rational cohomology and the
stated topology hypotheses; equality with the preceding map remains open.
The original preceding map is independently proved invertible for canonical
P¹ in degree two from its nonzero generator image and one-dimensional target.
-/
