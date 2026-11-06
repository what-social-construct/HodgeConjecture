module

public import HodgeConjecture.Realization.DeRham.Core
public import HodgeConjecture.Realization.DeRham.AffineComponents
public import HodgeConjecture.Realization.DeRham.AffineLineComparison
public import HodgeConjecture.Realization.DeRham.AffineGeometricDegree
public import HodgeConjecture.Realization.DeRham.SplitComparison

@[expose] public section

/-!
# Constructed affine de Rham objects and degree-zero comparison

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
-/
