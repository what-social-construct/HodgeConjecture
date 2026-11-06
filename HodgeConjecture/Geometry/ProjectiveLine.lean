module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual projective line and its two affine charts

Selected local proof adaptation from AxiomMath/Stacks at revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Scheme/Glueing/ProjectiveLine.lean`,
Apache-2.0. See `third_party/axiom-stacks/LICENSE`.
The two-chart scheme and structural morphism are actual Mathlib gluing
constructions; no scheme or covering property is supplied as an assumption.

The projective line over a commutative ring `k` is obtained by gluing two copies of the affine
line `Spec k[X]` along their standard punctured affine lines `Spec k[T, T⁻¹]`, with the
coordinates related by inversion. The coordinate functions of the two charts do not agree on the
overlap, but the constants do, so the two affine structure morphisms descend to a structure
morphism to `Spec k`. The points `0` and `∞` are the origins of the first and second chart.

## Main definitions

* `AlgebraicGeometry.projectiveLinePuncturedChart`: the open immersion
  `Spec k[T, T⁻¹] ⟶ Spec k[X]`, and `AlgebraicGeometry.projectiveLineInversionIso` the
  isomorphism of the punctured line given by `T ↦ T⁻¹`.
* `AlgebraicGeometry.projectiveLineGluingData'`, `AlgebraicGeometry.projectiveLineGluingData`:
  the two-chart gluing datum whose transition is inversion.
* `AlgebraicGeometry.projectiveLine`: the resulting glued scheme, with charts
  `AlgebraicGeometry.projectiveLineXChart` and `AlgebraicGeometry.projectiveLineYChart`.
* `AlgebraicGeometry.projectiveLineStructureMorphism`: the canonical morphism to `Spec k`,
  together with its chart restrictions.
* `AlgebraicGeometry.projectiveLineZero`, `AlgebraicGeometry.projectiveLineInfinity`: the two
  distinguished points.

## Main results

* `AlgebraicGeometry.projectiveLineXChart_comp_structureMorphism` and
  `AlgebraicGeometry.projectiveLineYChart_comp_structureMorphism`: the chart restrictions of the
  structure morphism are the standard affine-line structure morphisms.

## Implementation notes

The charts are indexed by `ULift Bool`. The overlap is `Spec k[T, T⁻¹]`, and its inclusion into
either affine line is induced by `Polynomial.toLaurent`, which realizes that ring as the
localization at `X`; the transition is induced contravariantly by `LaurentPolynomial.invert`, so
it sends the coordinate on either chart to the inverse coordinate on the other. The auxiliary
`CategoryTheory.GlueData'` form makes the cocycle condition vacuous, since three pairwise
distinct charts do not exist.

The construction works over any commutative ring. The distinguished points are defined over an
integral domain, in particular over every field as in the source, because the ideal `(X)` is
then prime. The chart maps have registered open-immersion instances, so their open ranges can
be used directly, and the base morphism is registered as the `Scheme.Over (Spec k)` structure.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The open immersion `Spec k[T,T⁻¹] ⟶ Spec k[X]` induced by the localization map at `X`. -/
abbrev projectiveLinePuncturedChart :
    Spec (.of (LaurentPolynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := k)))

/-- The map `projectiveLinePuncturedChart k` is an open immersion. -/
instance : IsOpenImmersion (projectiveLinePuncturedChart k) := by
  dsimp [projectiveLinePuncturedChart]
  exact IsOpenImmersion.of_isLocalization Polynomial.X

/-- The isomorphism `φ₁₂` of the gluing datum: the automorphism of the punctured affine line
induced by `T ↦ T⁻¹`, which is the identification `y = 1/x` of the two coordinates on the
overlap. -/
noncomputable def projectiveLineInversionIso :
    Spec (.of (LaurentPolynomial k)) ≅ Spec (.of (LaurentPolynomial k)) :=
  Scheme.Spec.mapIso LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.op

/-- Auxiliary two-chart gluing data before adjoining the diagonal overlaps. -/
def projectiveLineGluingData' : CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} Bool
  U _ := Spec (.of (Polynomial k))
  V _ _ _ := Spec (.of (LaurentPolynomial k))
  f _ _ _ := projectiveLinePuncturedChart k
  t i _ _ :=
    if i.down then (projectiveLineInversionIso k).inv
    else (projectiveLineInversionIso k).hom
  t' i j m hij him hjm := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (him rfl).elim | exact (hjm rfl).elim
  t_fac i j m hij him hjm := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (him rfl).elim | exact (hjm rfl).elim
  t_inv i j hij := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (projectiveLineInversionIso k).hom_inv_id
    · exact (projectiveLineInversionIso k).inv_hom_id
    · exact (hij rfl).elim
  cocycle i j m hij him hjm := by
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    obtain ⟨m⟩ := m
    cases i <;> cases j <;> cases m
    all_goals first | exact (hij rfl).elim | exact (him rfl).elim | exact (hjm rfl).elim

/-- The gluing datum for the projective line: two copies of `Spec k[X]`, glued along
`D(X) = Spec k[T,T⁻¹]` by inversion. -/
noncomputable def projectiveLineGluingData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (projectiveLineGluingData' k)
  f_open := by
    intro i j
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      projectiveLineGluingData']
    split_ifs <;> infer_instance

/-- The projective line over `k`, constructed by gluing its two standard affine charts. -/
noncomputable abbrev projectiveLine : Scheme.{u} :=
  (projectiveLineGluingData k).glued

/-- The index of the affine chart with coordinate `x`. -/
abbrev projectiveLineXIndex : (projectiveLineGluingData k).J := ULift.up false

/-- The index of the affine chart with coordinate `y`. -/
abbrev projectiveLineYIndex : (projectiveLineGluingData k).J := ULift.up true

/-- The inclusion of the affine chart with coordinate `x` into the projective line. -/
abbrev projectiveLineXChart : Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  (projectiveLineGluingData k).ι (projectiveLineXIndex k)

/-- The inclusion of the affine chart with coordinate `y` into the projective line. -/
abbrev projectiveLineYChart : Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  (projectiveLineGluingData k).ι (projectiveLineYIndex k)

/-- The `x`-chart of the projective line is an open immersion. -/
instance : IsOpenImmersion (projectiveLineXChart k) := by
  exact (projectiveLineGluingData k).ι_isOpenImmersion (projectiveLineXIndex k)

/-- The `y`-chart of the projective line is an open immersion. -/
instance : IsOpenImmersion (projectiveLineYChart k) := by
  exact (projectiveLineGluingData k).ι_isOpenImmersion (projectiveLineYIndex k)

/-- The standard structure morphism on either affine-line chart. -/
abbrev projectiveLineAffineStructureMorphism :
    Spec (.of (Polynomial k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

/-- The morphism from the projective line to `Spec k` whose restriction to each chart is the
standard structure morphism of the affine line. Its existence is the descent of the two affine
structure maps. -/
noncomputable def projectiveLineStructureMorphism :
    { f : projectiveLine k ⟶ Spec (.of k) //
      ∀ i : (projectiveLineGluingData k).J,
        (projectiveLineGluingData k).ι i ≫ f =
          projectiveLineAffineStructureMorphism k } := by
  let D := projectiveLineGluingData k
  refine ⟨CategoryTheory.Limits.Multicoequalizer.desc D.toGlueData.diagram _
    (fun _ => projectiveLineAffineStructureMorphism k) ?_,
    fun i => CategoryTheory.Limits.Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ i⟩
  · intro a
    rcases a with ⟨⟨i⟩, ⟨j⟩⟩
    change D.f ⟨i⟩ ⟨j⟩ ≫ projectiveLineAffineStructureMorphism k =
      D.t ⟨i⟩ ⟨j⟩ ≫ D.f ⟨j⟩ ⟨i⟩ ≫ projectiveLineAffineStructureMorphism k
    cases i <;> cases j <;>
      simp [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', projectiveLineGluingData', projectiveLinePuncturedChart,
        projectiveLineInversionIso, projectiveLineAffineStructureMorphism,
        ← Spec.map_comp, CategoryTheory.eqToHom_comp_iff,
        CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp,
        Spec.map_inj, CommRingCat.hom_ext_iff, RingHom.ext_iff,
        Polynomial.toLaurent_C, LaurentPolynomial.invert_C]

/-- The projective line is a scheme over `Spec k` via `projectiveLineStructureMorphism`. -/
instance : (projectiveLine k).Over (Spec (.of k)) where
  hom := (projectiveLineStructureMorphism k).1

/-- The restriction of the structure morphism of the projective line to the `x`-chart is the
standard structure morphism of the affine line. -/
@[simp] theorem projectiveLineXChart_comp_structureMorphism :
    projectiveLineXChart k ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k :=
  (projectiveLineStructureMorphism k).2 (projectiveLineXIndex k)

/-- The restriction of the structure morphism of the projective line to the `y`-chart is the
standard structure morphism of the affine line. -/
@[simp] theorem projectiveLineYChart_comp_structureMorphism :
    projectiveLineYChart k ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k :=
  (projectiveLineStructureMorphism k).2 (projectiveLineYIndex k)

/-- The origin of an affine-line chart, represented by the prime ideal `(X)`. -/
def affineLineOrigin [IsDomain k] : Spec (.of (Polynomial k)) :=
  ⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X⟩

/-- The point `0` of the projective line, namely the point `(X)` in the `x`-chart. -/
def projectiveLineZero [IsDomain k] : projectiveLine k :=
  projectiveLineXChart k (affineLineOrigin k)

/-- The point `∞` of the projective line, namely the point `(X)` in the `y`-chart. -/
def projectiveLineInfinity [IsDomain k] : projectiveLine k :=
  projectiveLineYChart k (affineLineOrigin k)

/-- The actual gluing charts form an open cover of the constructed scheme. -/
abbrev projectiveLineOpenCover : (projectiveLine k).OpenCover :=
  (projectiveLineGluingData k).openCover

/-- The two named affine-line charts jointly cover every actual point. -/
theorem projectiveLine_charts_cover (x : projectiveLine k) :
    (∃ y, projectiveLineXChart k y = x) ∨ (∃ y, projectiveLineYChart k y = x) := by
  obtain ⟨⟨i⟩, y, hy⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-- The two actual overlap morphisms agree in the glued scheme via coordinate inversion. -/
@[reassoc]
theorem projectiveLineOverlap_compat :
    projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
        projectiveLineYChart k := by
  symm
  simpa [projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', projectiveLineGluingData', projectiveLineXIndex,
    projectiveLineYIndex, projectiveLineXChart, projectiveLineYChart,
    CategoryTheory.eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.eqToHom_comp_iff] using
      (projectiveLineGluingData k).glue_condition (projectiveLineXIndex k)
        (projectiveLineYIndex k)

/-- The Laurent overlap is the actual scheme-theoretic intersection of the two affine charts. -/
theorem projectiveLineOverlap_isPullback :
    IsPullback (projectiveLinePuncturedChart k)
      ((projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k)
      (projectiveLineXChart k) (projectiveLineYChart k) := by
  let D := projectiveLineGluingData k
  let e : D.V (projectiveLineXIndex k, projectiveLineYIndex k) ≅
      Spec (.of (LaurentPolynomial k)) := eqToIso (by
    simp [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex])
  have h := IsPullback.of_isLimit
    (D.vPullbackConeIsLimit (projectiveLineXIndex k) (projectiveLineYIndex k))
  refine h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp [e, D, Scheme.GlueData.vPullbackCone, projectiveLineGluingData,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
    projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex,
    projectiveLineXChart, projectiveLineYChart, Category.assoc]

end AlgebraicGeometry

end

end
