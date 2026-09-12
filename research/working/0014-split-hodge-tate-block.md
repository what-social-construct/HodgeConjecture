# Finite degree-zero Hodge structure and geometric Tate-block detection

Status: PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS.

Date: 2026-09-12. This advances
[0013-split-betti-cycle-class.md](0013-split-betti-cycle-class.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

## Checkpoint

For `Z_I = Spec(ℂ^I)` with finite `I`, the preceding checkpoint constructed
the actual complex-point topology, genuine singular degree-zero cohomology,
and its point-normalized cycle-class equivalence with actual rational Chow.
This step supplies the independent Hodge data and the actual geometric
block maps needed by the existing target theorem.

The result is a concrete codimension-zero `RationalHodgeCycleClassModel`,
with constructed graph encoding, lower-left Chow detection, and Hodge
compatibility. Its Hodge target, graph lifting, and Palomar target squares
are proved using the constructed objects.

## Independent Hodge data

Write `H_I = H_B^0(Z_I(ℂ);ℚ)`. Its complexification is the actual tensor
product `H_(I,ℂ) = ℂ ⊗[ℚ] H_I`, not a coefficient space by definition.
Scalar extension of the independently defined Betti coordinates proves

```text
H_(I,ℂ) ≃ₗ[ℂ] (I → ℂ),
c ⊗ u ↦ (c u_i)_i.
```

The canonical rational map `ι_I(u)=1⊗u` is injective. Coordinate
conjugation is proved to be the canonical tensor conjugation
`conj(c⊗u)=conj(c)⊗u`, including additivity, complex semilinearity,
involutivity, and fixation of the rational image. Both spaces have their
finite-dimensionality proved.

The effective degree-zero bigrading is specified on this tensor space:

```text
H_I^(p,q) = H_(I,ℂ) when (p,q)=(0,0), and 0 otherwise.
```

The formal proofs establish exhaustive direct decomposition, effective
weight zero, and conjugation symmetry. Directness is `iSupIndep` against
the sum of all other pieces, not merely pairwise disjointness.

The rational Hodge subspace is then defined by
`H_(I,Hdg) = ι_I⁻¹(H_I^(0,0))` and proved equal to `H_I`.
The cycle-class map is absent from its definition and proof. A Hodge
morphism is an actual rational linear map whose genuine complex scalar
extension preserves every bigrading piece. Every rational linear map
between these type-`(0,0)` spaces is proved to satisfy that predicate.

## Actual Chow block and fixed Betti coordinates

Set `I⁺={*}⊔I`, implemented by `Option I`. The existing scheme operations
give an actual isomorphism

```text
Z_(I⁺) ≅ Spec ℂ ⨿ Z_I,
```

respecting the distinguished point and complementary scheme inclusions.
On actual singular cohomology, point evaluation and restriction to the
complement give the fixed decomposition
`τ_I : H_B^0(X_(I⁺);ℚ) ≃ₗ[ℚ] ℚ(0) ⊕ H_I`.
In particular, its second component is actual continuous-map pullback,
not only an equality of label coordinate modules.

Let `j:Z_I→Z_(I⁺×I⁺)` be the actual map induced by `i↦(*,i)`. Define

```text
enc_I(z) = [(*,*)] + j_*z,
dec_I(c) = j^*c.
```

Encoding is affine because of its fixed point-pair summand; decoding is
linear and defined on the complete actual Chow correspondence algebra.
The previously constructed image/fiber geometry supplies these proper
pushforward and flat pullback operations.

Actual geometric composition has the matrix law, from which Lean proves
`enc_I(z)^2=enc_I(z)` and `dec_I(enc_I(z))=z`. Thus encoding is injective.
The matrix is computed from this geometric definition, not used to define
an unrelated graph correspondence.

The existing actual Betti action, in the fixed block coordinates, is
`ρ_I⁺(c)=τ_I ρ_(B,I⁺)(c) τ_I⁻¹`. Its two comparison laws are

```text
ρ_I⁺(enc_I(z)) = P_cl(z),
cl_I(dec_I(c)) = lowerLeft(ρ_I⁺(c)).
```

The detection equality holds for every Chow correspondence `c`, not just
the image of encoding. Here `lowerLeft(e)` is evaluation at `(1,0)`
followed by the second projection, exactly the existing target interface.

## Instantiated target

`hodgeModel I` uses actual Chow, actual singular cohomology, the independent
rational Hodge subspace above, and the constructed cycle-class map.
`construction I` and `detection I` package the two proved geometric laws.
`IsBlockHodgeMorphism I` uses the genuine complexified Hodge-morphism
predicate after the fixed coordinate change; `hodgeCompatibility I`
proves its graph criterion.

The cycle-class equivalence supplies a Chow representative of each
`α:H_I`. Applying the actual encoding gives its idempotent graph lift.
The generic target theorem now applies without supplied construction or
detection data, yielding

```text
HC_Q(hodgeModel I)
↔ every Hodge-class graph has an actual Chow projector lift
↔ every such class has ρ_I⁺ ∘ φ_(Π_α) = φ_(P_α).
```

The equivalent Hodge-morphism graph formulation is instantiated as well.
This uses the same universal one-idempotent algebra and target notation as
the general theorem, not a second projector interface.

## Source and scope match

- [Deligne, The Hodge Conjecture, §1](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf)
  describes the geometric Hodge decomposition by nonnegative form
  bidegrees with fixed total degree. In degree zero only `(0,0)` occurs.
- [Deligne, Théorie de Hodge II, §§2.1.5--2.1.13](https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf)
  gives the conjugate bigrading, rational structures, morphism convention,
  and Tate structure. In particular, `ℚ(0)` has type `(0,0)`. Weight zero
  alone would allow non-effective types; the geometric effectiveness
  condition is essential to the source match.
- [Stacks, Lemma 45.4.3, Tag 0FGC](https://stacks.math.columbia.edu/tag/0FGC)
  identifies the unit motive with `Spec k`.
  [Lemma 45.4.6, Tag 0FGF](https://stacks.math.columbia.edu/tag/0FGF)
  uses disjoint unions for direct sums with equal twists. These explain
  the degree-zero motive interpretation of the actual point-plus-scheme
  correspondence block.

Lean explicitly specifies and verifies the finite effective type-`(0,0)`
structure on actual Betti complexification. The source identifies this
with geometric degree zero; this step does not implement an analytic
forms/de Rham complex, a general Hodge comparison theorem, a general
Chow-motive category, or a nonzero Tate twist. The geometric block and its
maps are actual scheme Chow constructions.

## Lean and parity

Paths below are relative to `HodgeConjecture/Realization/`.

| Module | Principal declarations |
| --- | --- |
| `Betti/Examples/SplitHodgeStructure.lean` | `SplitHodgeStructure.Complexification`, `complexCoordinates`, `rationalEmbedding_injective`, `conjugation_tmul`, `bigrading_effective`, `bigrading_direct`, `bigrading_exhaustive`, `conjugation_bigrading`, `rationalHodgeClasses`, `rationalHodgeClasses_eq_top`, `IsHodgeMorphism`, `all_isHodgeMorphism` |
| `Chow/Examples/SplitTateBlock.lean` | `SplitChowTateBlock.encode`, `decode`, `matrix_encode`, `coordinates_decode`, `decode_encode`, `encode_isIdempotent`, `encode_injective`, `optionSchemeIso`, `pointInclusion_optionSchemeIso`, `mapSome_optionSchemeIso` |
| `Betti/Examples/SplitTateBlock.lean` | `SplitBettiTateBlock.blockCoordinates`, `blockCoordinates_snd`, `coordinateChange`, `realization`, `realization_encode`, `cycleClass_decode`, `hodgeModel`, `construction`, `detection`, `IsBlockHodgeMorphism`, `hodgeCompatibility`, `hodgeConjectureAt`, `graphProjectorLift`, `hodgeConjectureAt_iff_palomarTargetSquare`, `everyHodgeClassHasPalomarTargetSquare`, `hodgeConjectureAt_iff_hodgeMorphismLift` |

Claim A11l and semantic parity item SP24 record the result. The notation
registry distinguishes the actual Hodge complexification, rational
subspace, geometric encoding/decoding, and fixed block decomposition.
No implementation wrapper is treated as an additional mathematical object.

## Next bridge

Connect this concrete block action and detection to actual marked Galois
residual and cover data, with compactified projectors and their action
square, and establish the intended class-dependent coverage. Extending
the geometric Hodge/block construction beyond finite split degree zero
remains a separate task.

The actual Betti cycle class and the encoding are injective here. The
earlier loss from the free span source to its additive quotient remains
exactly the finite point-decomposition ideal; no Hodge interpretation
reverses that quotient.

## Verification record

- The Hodge structure, actual Chow block, and Betti block/interface modules
  each pass their direct build.
- The full `lake build` passes (3016 jobs); only the unchanged
  `Challenge.lean` admitted-statement warnings remain.
- The integrated verification harness exits successfully without new
  warnings. All 14 new axiom reports contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Empty-label, matrix-orientation/lower-left detection, and universal-square
  regressions pass. Independent mathematical and semantic-parity review
  also passes.
- Citation-key checks and `git diff --check` pass.
- The single-PDF `latexmk` build passes: 27 pages, 628796 bytes, with no
  warnings, undefined references, or overfull/underfull boxes in
  `paper/main.log`. Pages 17--19, including Theorem 7.9 on pages 18--19,
  were visually reviewed.
