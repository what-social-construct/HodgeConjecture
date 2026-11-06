# Positive-degree realization toward the ordinary cycle map

Started: 2026-11-05. Validation completed: 2026-11-06. The selected target is the ordinary map
`CH^p(X)_ℚ → H^(2p)(X,ℚ)`. Saito's logarithmic and boundary constructions
are proof ideas for this task. No identification with Bloch higher Chow
groups or new Hodge-conjecture case is claimed.

## Pinned Axiom objects and selective reuse

The source audit retains AxiomMath/Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`. Its genuine sheaf-level
`DeRhamCohomologyFirstChernClass.lean` constructs a first Chern class in
degree-two relative de Rham cohomology. It is a substantial derived/sheaf
construction, with 1,181 upstream project modules in its source-import
closure. It is not merely an assumed Weil-theory field, but it is not
imported into this project.

The local rewrites instead use the actual exterior-power multiplication
and signed Leibniz proofs (`ExteriorPower/Wedge.lean`, `WedgeLeibniz.lean`
and the scalar formula in `PolynomialQuasiIso.lean`), the Euler/residue
calculation in `LaurentHomotopy.lean`, and the small actual projective-line
gluing construction. Attribution and the upstream license are retained.
All new objects use this project's original Kähler differential, complexes
and scheme library. There is no Axiom/Stacks Lake dependency.

## Actual positive-degree cohomology

`AffineCohomology.lean` constructs closed forms and the actual incoming
image in every degree. Their quotient is canonically isomorphic to
categorical homology of `deRhamComplex`. Degree zero recovers the existing
closed-function kernel. `CohomologyProduct.lean` constructs the genuine
`H¹ × H¹ → H²` cup product: explicit primitive formulas prove independence
of both representatives modulo exact forms. No cohomological product is
supplied as an input.

`Logarithmic.lean` proves closedness of `u⁻¹ du` for every actual unit,
along with multiplication, inversion, integral powers and Kähler pullback
compatibility. The resulting unit regulator lands in the actual `H¹`.
`LaurentResidue.lean` and `LaurentLogarithmicRegulator.lean` prove that the
coordinate class of the multiplicative line has residue one and is nonzero.
The universal Kähler lift of the Euler derivation also gives the actual
Laurent differential basis; exterior powers of degree at least two vanish.

The auxiliary `MilnorSymbols.lean` and `MilnorRegulator.lean` construct the
degree-two symbol presentation and the map `{u,v} ↦ [d log u ∧ d log v]`.
Both multiplicativity relations and Steinberg vanishing are proved on the
actual forms. `TorusResidue.lean` constructs a genuine two-form detector
on an iterated Laurent algebra, annihilating every actual degree-one
differential. These supporting constructions are not substituted for the
ordinary Chow source or a Bloch higher-Chow comparison.

## The actual projective-line cover

`Geometry/ProjectiveLine.lean` constructs the scheme by gluing two actual
`Spec k[X]` charts along `Spec k[T,T⁻¹]`, with coordinate inversion. Its
named chart maps are open immersions and jointly cover. The actual
overlap square is proved a pullback. `LaurentProjectiveCharts.lean` derives
the corresponding maps on Kähler forms from the original ring maps.
The images are closed and have residue zero, with no supplied comparison
or exactness premises.

`ProjectiveLineCech.lean` constructs the coordinate-ring Čech–de Rham
total complex. Its first terms are

```text
C⁰ = k[X] × k[Y]
C¹ = Ω¹(k[X]/k) × Ω¹(k[Y]/k) × k[T,T⁻¹]
C² = Ω¹(k[T,T⁻¹]/k).
```

The overlap tail retains the original exterior powers and their signed
differentials. Vanishing of higher polynomial chart forms is proved.
The actual restriction/differential formulas prove square zero. Its
explicit `CechH2` is canonically categorical homology in total degree two;
negation on the final short-complex term handles the outgoing sign.
This is a constructed Čech realization, not a declaration that a scalar
coordinate space is the desired cohomology.

## Ordinary Čech first Chern class

`ProjectiveLineChern.lean` maps a transition unit to the total class of
its actual logarithmic differential. Changing either chart trivialization
is an explicit incoming total boundary. The map therefore descends to
`TransitionPicard`, the quotient of overlap units by the actual chart
coboundaries. This is the Čech Picard group for the named two-chart cover.

The class of the coordinate transition has residue one, and so the
constructed first-Chern map and degree-two class are nonzero. Integral
tensor powers have the expected signed multiples. The residue retracts
the coefficient-linear span of the distinguished class.

The transition source has not been renamed to `CH¹`: an identification of
that entire group with geometric Picard or Chow classes remains separate.
The ordinary Chow-source map below is instead constructed directly from
the original principal-relation quotient. Comparison of the Čech target
with derived scheme de Rham and rational singular cohomology remains open.

## Ordinary divisor-source comparison

`TopDegreeRelations.lean` proves that an integral closed relation carrier
of the ambient generic degree is the whole reduced ambient scheme. Its
closed immersion is an actual isomorphism, and its ambient relation is
an actual ambient principal divisor with a constructed transported
rational function. This removes an arbitrary-carrier reduction from
the ordinary Chow descent problem.

The source work uses the actual two charts, proved integral and
Noetherian geometry, canonical field grading, and polynomial local orders.
The polynomial stalk/function-field dictionary preserves the original
scalar actions and signed length-based order. The actual divisor-point
set splits into the affine chart and infinity, and the affine points are
identified with monic irreducible polynomials. The gluing comparison
forces the two function-field readings to be related by coordinate
inversion. These are proved geometric maps, not supplied coordinates.

The degree-weighted finite orders sum to the rational function's degree;
the infinity order is its negative. Over an algebraically closed field, all irreducible
polynomial degrees are one. Consequently the actual coefficient sum of
every original projective-line principal divisor is zero. This theorem
discharges all original relation carriers through `TopDegreeRelations`.

`ProjectiveLineChow.lean` descends integral and rational degree to the
existing `ChowGroup` and `RationalChowGroup`, using their exact original
relation spans. `ProjectiveLineCycleClass.lean` then constructs the
ordinary map

```text
CH_0(P¹_k)_ℚ → RestrictScalars ℚ k (CechH2 k),
             z ↦ (degree z) · κ,     κ = c₁(T).
```

Here `k` is algebraically closed of characteristic zero for the rational
map; an integral additive map is also constructed without the
characteristic-zero restriction. Scalar restriction retains the original
Čech cohomology element. Every actual coefficient-one point cycle maps to
`κ`; the actual infinity cycle agrees with the coordinate first-Chern
transition. Principal relations vanish, integral/rational Chow
rationalization commutes, and the map is nonzero. Residue recovers the
actual degree. Field coefficients outside the rational scalar image
produce classes outside the rational cycle image, so complex coefficients
are not silently treated as rational classes.

This is an ordinary positive-codimension Chow-source map for the actual
projective-line scheme, with a constructed total degree-two de Rham target.
No identification of this source with the full transition Picard quotient
is needed as a premise. Injectivity of Chow degree, a classification of the
entire Chow group, and the general scheme/singular/Hodge comparison are
not asserted by this construction.

## Computing the degree-two target

`ProjectiveLineCohomology.lean` proves that every actual Laurent one-form
is represented by its constant Euler coefficient times `κ`. Positive
Laurent logarithmic monomials are actual zero-chart boundaries, and
negative monomials are actual infinity-chart boundaries. Consequently
`cechResidueEquiv : CechH2 k ≃ₗ[k] k` and
`cechCohomologyTwoCoordinates` compute categorical degree-two homology of
the constructed total complex. This holds over every commutative ring;
no division by integers or characteristic-zero hypothesis is needed.
Characteristic two and a nonfield coefficient ring are explicitly checked.

## Verification and limits

`make build-positive-degree` builds the algebraic and ordinary Chow-source entry points;
`make check-positive-degree` checks actual representatives, cup boundaries,
both local trivializations, residue normalization and nonzero categorical
degree-two cohomology, with enforced standard-three axiom audits.
The old algebraic core, polynomial/component and affine-line comparison
entry points retain their previous import boundaries.

The combined focused Make build passes 3,318 dependency jobs. The permanent
suite passes 34 meaningful examples and 48 enforced standard-three axiom
audits, including the original ordinary Chow source, all principal
relations, point normalization, rationalization, the rational-image bound,
characteristic-two chart boundaries and nonfield `ZMod 6` coefficients.

The full default build passes 4,215 jobs. Root verification passes 1,334
declaration checks, 574 examples and 1,226 axiom reports; every reported
axiom is within `propext`, `Classical.choice` and `Quot.sound` (one report
has no axioms). All 421 library modules plus the root pass the proof-token
and external-Stacks-import scan. The algebraic and ordinary Chow-source
entry points have 18 and 111 project modules respectively. All eight
import boundaries, three indirect-negative import checks, pinned
dependencies, local documentation links and whitespace checks pass.
Job counts include cached dependencies. Existing style/deprecation
warnings retain their previous scope; the new sources and focused suite
emit no warnings. The main README remains 69 lines.

The main remaining target is the ordinary Chow-to-Betti map and its
independently defined Hodge comparison beyond this algebraic Čech case.
These constructions do not prove coverage of prescribed Hodge classes.
Submission selection remains deferred.
