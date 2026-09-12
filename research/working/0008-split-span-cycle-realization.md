# Additive cycle-coefficient realization of actual split scheme spans

Checkpoint update: the exact finite point-decomposition kernel and additive
quotient identified as open below are now proved in
[0009-split-span-additive-quotient.md](0009-split-span-additive-quotient.md).
The historical construction and verification record below is preserved;
genuine Chow and Betti identifications remain separate open steps.

Status: SPLIT GEOMETRIC SOURCE-TO-MATRIX BRIDGE IMPLEMENTED; GENUINE
CHOW/BETTI IDENTIFICATION AND GENERAL HODGE COVERAGE REMAIN OPEN.

Date: 2026-09-11. This advances the dated checkpoint
[0007-split-point-realization.md](0007-split-point-realization.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.
Repository-wide release verification is recorded separately; this note is
the construction and scope record, not a final build certificate.

## Result and exact source

Fix an arbitrary field `k` and a finite label set `I`, and write
`Z_I = Spec(k^I)`. Let `S_sp(Z_I/k)` be the submonoid of the existing actual
finite-étale scheme-correspondence classes on `Z_I` consisting of classes
with a finite split presentation. Such a presentation has the form

```text
Z_I ← Z_A → Z_I,       A finite,
       l     r         l, r : A → I.
```

The legs are the scheme morphisms induced by pullback of coefficient
functions. The new construction gives a unital rational algebra map

```text
χ_sp : C_sp(Z_I/k) := Q[S_sp(Z_I/k)] → M_I(Q),
χ_sp([Z_I ← Z_A → Z_I]) = ∑ a∈A E_(r(a),l(a)).
```

Rows index outputs and columns index inputs. Thus the matrix entry `(j,i)`
counts carrier points with `l(a)=i` and `r(a)=j`. Its action on rational
coefficient vectors is the pull-push formula
`(χ_sp([A])v)(j) = ∑_{a : r(a)=j} v(l(a))`.

The map is independent of every choice of split presentation, respects
actual scheme pullback composition, sends actual disjoint union to sum,
and sends the empty carrier to zero. It is surjective. This is a constructed
map from geometric classes, not an assumed `FiniteEtaleAlgebraModel` and
not a redefinition of geometric composition to mean matrix multiplication.

There is also a distinct, injective algebra map

```text
j_sp : C_sp(Z_I/k) ↪ SchemeCorrespondence.FiniteEtaleFreeAlgebra (toBase k I),
```

which forgets the proof of split-presentability. Consequently the source
really embeds into the previously existing geometric free-span algebra.
Injectivity of `j_sp` must not be confused with surjectivity of `χ_sp`:
the matrix realization has relations in its kernel and is not asserted to
be injective.

## Geometry before linearization

`SplitPointGeometry.mapOfFunction k f` is `Spec` of the algebra map
`a ↦ a ∘ f`. Its identity, composition, base compatibility, and compatibility
with the point inclusions are proved. With finite source labels the map is
finite and étale. The finite proof uses restriction of scalars from `k`;
the étale proof uses the component coproduct presentation and open point
inclusions. Hence `SplitPointGeometry.span k l r` is an actual scheme span
with finite-étale legs.

For `I ← A → J` and `J ← B → L`, define the matching-pair set
`F = {(a,b) ∈ A × B : r_A(a)=l_B(b)}`. Lean constructs a canonical comparison

```text
Z_F → Z_A ×[Z_J] Z_B
```

and proves that it is an isomorphism. Each matching pair gives an open
point chart on the actual scheme pullback. The chart is obtained by mapping
the self-pullback of a point inclusion into the larger pullback. The source
self-pullback is the same point because the inclusion is a monomorphism.
The charts are pairwise disjoint and cover the pullback; both assertions
use the actual scheme-theoretic point labels. Their coproduct therefore
gives the required isomorphism.

This proves `span_comp_iso` with the convention
`[Q.comp P] = [Q] * [P]`. The comparison respects both external legs, not
only the abstract carrier. `span_identity_iso` identifies the diagonal
indexing span with the actual identity correspondence. `span_point_iso`
identifies a singleton diagonal span with the earlier `pointSpan`.

For disjoint union, `sumSchemeIso` identifies `Z_(A ⊕ B)` with the actual
scheme coproduct `Z_A ⨿ Z_B`; `span_sum_iso` proves compatibility with both
span legs. Its finite-étale proof is transported along that actual
isomorphism. No compactification or purity hypothesis is needed for this
finite proper split example.

## Descent from presentations to actual classes

`labelEquivScheme k A : A ≃ Z_A` identifies finite labels with the actual
points of `Spec(k^A)`. A scheme isomorphism `Z_A ≅ Z_B` therefore induces a
bijection `A ≃ B` through `labelEquivOfIso`. If the isomorphism respects the
span legs, `labelEquivOfIso_respects_map` proves that this bijection
respects `l` and `r`.

Combining this geometric fact with finite-sum reindexing proves
`SplitSpanRealization.matrix_eq_of_isom`. The theorem
`matrix_eq_of_class_eq` then descends to the existing quotient by actual
scheme-span isomorphisms.

`Presentation k I c` records a finite split presentation of an existing
`FiniteEtaleClass`, including an equality in that actual quotient.
`Presentation.matrix_eq` proves that any two presentations of `c` give
the same matrix. Thus the choice used by `classMatrix` to compute
coefficients has no effect on its result. We are not quotienting only by
chosen relabellings or assuming that all geometric isomorphisms have
already been encoded as relabellings.

The identity presentation and the geometric pullback theorem prove that
split-presentable classes form `classSubmonoid`. The arithmetic theorem
`FiniteSpanMatrix.matrix_pullback` proves that the matching-pair matrix is
the product of the two incidence matrices. Together these yield
`classMatrixHom : SplitClass k I →* Matrix I I Q`. Rational linearization
then gives the constructed algebra map `realization`.

## Additive relations: killed, not imposed

`C_sp(Z_I/k)` is still the monoid algebra on geometric span classes. Its formal
addition does not itself identify a disjoint-union basis vector with the
sum of its two component basis vectors. Nor is the empty-span basis vector
defined to be zero.

The realization proves the target equalities

```text
χ_sp([P ⨿ Q]) = χ_sp([P]) + χ_sp([Q]),
χ_sp([∅]) = 0.
```

`realization_sum`, combined with `span_sum_iso` and
`toFiniteEtaleFreeAlgebra_sum`, is a law about actual geometric coproduct
classes. `realization_empty` gives empty-carrier vanishing.
Equivalently, the corresponding additive-relation differences and the
empty basis vector are killed by the algebra map. No new quotient imposing
these relations has been defined here, and no theorem identifies their
generated two-sided ideal with the entire kernel of `χ_sp`.

In particular, distinct diagonal point projectors need not multiply to zero
inside the free-span source: their geometric composition has an empty
carrier, whose basis vector is still a source element. Their images are
orthogonal matrix projectors because that empty carrier realizes to zero.

`realization_surjective` writes every rational matrix as a rational linear
combination of matrix units. A singleton span with input label `i` and
output label `j` realizes to `E_(j,i)`, so every matrix coefficient has an
actual geometric representative. Surjectivity alone does not prove the
missing kernel/quotient identification.

## The earlier point projector now has one complete coefficient path

For `I = Fin 2`, `GeometricSplitPoints.Source k` is `C_sp(Z_I/k)`, and
`GeometricSplitPoints.projector k` is the singleton span over label `0`
on both sides, denoted `π₀^sp`. Its source embedding is exactly the earlier
geometric projector `π₀`, namely
`SplitPointGeometry.pointProjector k (Fin 2) 0`. This is the theorem
`projector_toFiniteEtaleFreeAlgebra`, not merely equality after passing to
matrices. Its source-side idempotence follows from that geometric identity
and the injectivity of the embedding.

The new and old constructions now compose as follows:

```text
actual singleton scheme-span projector π₀^sp
  -- χ_sp --> E₀₀
  -- C ↦ T C T⁻¹, T(a,b)=(a,b−a) --> P₋₁.
```

`matrixRealization_projector` proves the first arrow;
`coefficientRealization_projector` proves the composed action. The residual
map is still the explicit second-coordinate evaluation on the marked
augmentation ideal, with `θ(q−1)=−1`. It is not an arbitrary prescribed
Hodge class supplied as a new hypothesis.

`markedComparison` instantiates the canonical
`MarkedProjectorActionComparison` with this geometric-source projector.
`projectorLift` supplies the resulting projector lift, and
`palomarTargetSquare` proves the equality of unital algebra maps from
`Q × Q`:

```text
(ρ ∘ χ_sp) ∘ φ_(π₀^sp) = φ_(P₋₁).
```

No forbidden map from the full matrix algebra back to a commutative sheet
algebra is reintroduced. The canonical comparison uses the chosen
idempotent directly.

## Lean API and source files

All paths below are under `HodgeConjecture/`.

| File | Principal endpoints |
| --- | --- |
| `Correspondence/Examples/SplitPointMaps.lean` | `labelEquivScheme`, `labelEquivOfIso`, `labelEquivOfIso_respects_map` |
| `Correspondence/Examples/SplitSpanGeometry.lean` | `mapOfFunction`, `span`, `span_hasFiniteEtaleLegs`, `fiberComparison`, `fiberIso`, `span_comp_iso`, `span_identity_iso`, `span_point_iso` |
| `Correspondence/Examples/SplitSpanCoproduct.lean` | `sumSchemeIso`, `span_sum_iso` |
| `LinearAlgebra/FiniteSpanMatrix.lean` | `matrix_apply`, `matrix_mulVec`, `matrix_reindex`, `matrix_id`, `matrix_empty`, `matrix_sum`, `matrix_sigma`, `matrix_pullback` |
| `Realization/Chow/Examples/SplitSpanRealization.lean` | `matrix_eq_of_class_eq`, `Presentation.matrix_eq`, `classSubmonoid`, `classMatrixHom`, `realization`, `toFiniteEtaleFreeAlgebra_injective`, `realization_sum`, `realization_empty`, `realization_surjective` |
| `Realization/Chow/Examples/GeometricSplitPoints.lean` | `projector_toFiniteEtaleFreeAlgebra`, `projector_isIdempotent`, `matrixRealization_projector`, `coefficientRealization_projector`, `markedComparison`, `projectorLift`, `palomarTargetSquare` |

## Scope and the next remaining comparisons

The field `k` is arbitrary. The main span and matrix construction is
universe-polymorphic with finite label and carrier types; the two-point
endpoint is currently stated with `k : Type`. The source consists of
finite split-presentable classes, not all finite-étale correspondences
over `k`. A nonsplit finite-étale carrier is outside that source unless a
suitable split presentation is actually supplied and proved. Extending
to nonsplit carriers would require further degree or base-change/descent
work, not an automatic consequence of the current map.

The earlier additive realization arrow is now discharged in this precise
split scope. The remaining comparisons are distinct:

- Present the appropriate additive quotient and prove an exact kernel or
  universal-property theorem, if that quotient is to be identified with
  the coefficient matrix algebra. The current algebra map kills the
  expected relations but does not prove that they generate its full kernel.
- Identify the finite split point-cycle coefficient objects with actual
  scheme-theoretic Chow groups and their correspondence composition.
  The construction here is a cycle-coefficient realization, not a theorem
  that the existing source or target definition is a Chow group.
- Construct and identify the genuine Betti cycle-class map and Hodge
  subspace, with the needed action compatibility. The present coefficient
  module and the change of coordinates do not supply these comparisons.

Even completing these zero-dimensional identifications would not supply
class-dependent higher-dimensional geometry, a general compactification
and boundary-vanishing theorem, or coverage of arbitrary rational Hodge
classes. The result is a checked geometric realization bridge in the
finite split test case, not a new case or proof of the Hodge conjecture.

## Verification of this checkpoint

- Full `lake build` passed (2,809 jobs). The only warnings were the two
  pre-existing `sorry` declarations in unchanged `Challenge.lean`.
- `lake env lean research/Verification.lean` passed. The actual pullback
  comparison, constructed realization, surjectivity, and geometric-source
  Palomar square depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The project source directory `HodgeConjecture/` contains no `sorry`, `admit`,
  `axiom`, or `unsafe` declarations.
- The canonical `paper/main.pdf` rebuilt to 19 pages, without LaTeX warnings,
  undefined references, or over/underfull boxes.
- Independent mathematical and manuscript/Lean parity reviews passed;
  `git diff --check` passed. No publication or new Hodge-result claim follows
  from these automated checks.
