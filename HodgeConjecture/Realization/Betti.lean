module

public import HodgeConjecture.Realization.Betti.Scheme
public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.CoefficientChange
public import HodgeConjecture.Realization.Betti.SingularCoefficientCohomology
public import HodgeConjecture.Realization.Betti.SingularCoefficientTensorBridge
public import HodgeConjecture.Realization.Betti.SingularCoefficientDerivedSquare
public import HodgeConjecture.Realization.Betti.ComplexSingularConstantSheafCohomology
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints

public import HodgeConjecture.Realization.Betti.Examples.SplitGaloisAction
public import HodgeConjecture.Realization.Betti.ZeroSimplexTransfer
public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import HodgeConjecture.Realization.Betti.Examples.AffineLineComplexPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLine
public import HodgeConjecture.Realization.Betti.SmallChains
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Realization.Betti.ProjectiveLineComplexification
public import HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass
public import HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
public import HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass

@[expose] public section

/-!
# Constructed Betti realization

The canonical complex point space is constructed for schemes over ℂ.
Its rational singular cohomology and scheme pullbacks reuse the shared
cochain functor in every degree. Affine and original P¹ point models are
identified by proved homeomorphisms. This supplies the geometric Betti
target; general de Rham comparison and purity remain open.
The original rational singular cochains now form presheaves on this
topology. Native sheafification gives a full constant-sheaf resolution
on the constructed smooth analytic manifolds. Global singular cochains
map to the same sheaf complex by the native unit. Its actual categorical
kernel is now identified with locally zero original cochains and proved
acyclic in every degree, with native primitives. On paracompact Hausdorff
spaces that same unit is now surjective in every degree and a
quasi-isomorphism to termwise global sections. Those topology hypotheses
are proved for canonical affine spaces and the original P¹. Open-subspace
lifting now gives native flasqueness of the existing cochain sheaves on
locally compact second-countable Hausdorff spaces, including these same
canonical spaces. Each such sheaf term now has zero positive derived
sections on every open, using the original module-valued functor.
The original whole-complex underived-to-derived comparison is now
invertible under the same flasqueness hypotheses. Composing it with
the original global unit and local constant-sheaf resolution now identifies
the original rational singular cohomology with actual right-derived
sections of the original rational constant sheaf. Scalar evaluation now
compares the original tensor complexification with unrestricted complex
functionals on the same native rational chains. This actual cochain map
induces an isomorphism in every degree where the original rational
cohomology is finite dimensional. The same unrestricted complex cochains
now compare isomorphically with derived sections of the native complex
constant sheaf under the stated topology hypotheses. The original
coefficient map commutes with sheafification and both constant-sheaf
resolutions. Its identification with the constructed holomorphic map,
general scheme topology and the general Betti–de Rham comparison remain open.

For path-connected spaces, actual paths and singular one-simplices prove
that degree-zero cocycles are constant. The complex affine line has the
topology of regular-function evaluations, proved homeomorphic to `ℂ`.
The actual projective-line complex points have the final affine-atlas
topology, proved homeomorphic to `OnePoint ℂ`. Singular cochains in every
degree use the original simplices and alternating faces; their H⁰ agrees
with the existing kernel construction.
The small-chain development constructs actual barycentric subdivision,
its local homotopy, and finite-chain shrinking for arbitrary indexed open covers.
The inclusion of the small singular subcomplex compares its rational
homology with the original singular complex. Original cochain restriction
is a surjective quasi-isomorphism for every indexed open cover, with an
acyclic original relative kernel and compatible refinement maps. The small cochain gluing
sequence has a constructed connecting map. Exact rational dualization
identifies actual full singular cochains with native dual chains and
proves the small restriction is a quasi-isomorphism. The resulting full
Mayer–Vietoris sequence uses the actual subtype cohomologies, with original
continuous restriction formulas and the first-minus-second difference.
Homotopy invariance and actual chart contractibility now compute the circle's
H¹ and the original projective line's H² as rational lines, with generators
given by the actual Mayer–Vietoris boundaries. The P¹ isomorphism uses the
original affine charts and actual radial overlap pullback. The explicit
counterclockwise two-arc cycle now proves positive pairing one with the
circle cover generator. The induced P¹ boundary pairing fixes its sign.
The genuine tensor complexification and ordinary Chow-to-singular map are
constructed independently of de Rham. A separate period layer compares
their actual boundary periods; general analytic/Gysin comparison remains open.
Actual relative cochains and open-cover excision now construct the oriented
zero-point Gysin map through local Thom class and forgetting support. Its
unit equals the positive P¹ generator and the zero-point ordinary cycle class;
the ordinary degree map factors through this distinguished-point Gysin.
Other points, chart independence and general Gysin comparison remain open.
An independently defined type-(1,1) decomposition on the genuine tensor
target has canonical rational conjugation, directness and an opposed
filtration. Its agreement with the actual scheme degree filtration is
proved separately in the de Rham comparison layer.

The finite split complex example uses actual complex-algebra points with
their evaluation topology, actual continuous singular simplices and faces,
and degree-zero cohomology defined by the singular coboundary kernel.
The normalized point cycle-class map is a proved linear equivalence.

Continuous pullback, singular cup product, and finite transfer construct
the cohomological action. The transfer formula is also identified with the
sum over actual lifts of each zero-simplex. Cycle classes intertwine this
action with geometric Chow pull--intersection--push, yielding an algebra
homomorphism into the actual cohomology endomorphism algebra.

The finite degree-zero Hodge structure is specified on the genuine tensor
complexification, independently of cycle classes, with directness and
conjugation compatibility proved. Adding a distinguished scheme point
constructs the Tate block. Actual Chow pushforward and lower-left pullback
instantiate the graph construction, detection, and Hodge compatibility,
and prove the corresponding finite degree-zero Palomar target.

For homogeneous sheets of a constructed split finite-group torsor, the
residual map is an actual point-cycle construction followed by cycle class.
An invertible Chow shear realizes the constant-marked coordinate change,
and the full sheet-algebra action comparison is proved. The marked
selector's universal target square follows for the resulting negative
fundamental class.
-/
