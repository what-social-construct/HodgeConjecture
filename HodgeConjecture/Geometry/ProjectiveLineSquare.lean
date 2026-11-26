module

public import HodgeConjecture.CommutativeAlgebra.PolynomialSquare
public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import HodgeConjecture.Geometry.ProjectiveLineOpenCover
public import HodgeConjecture.Geometry.ProjectiveLineProductSections
public import HodgeConjecture.Geometry.ComplexPointsFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-!
# The actual squaring morphism of the glued projective line

Polynomial squaring on both original affine charts descends through the
actual Laurent overlap and its inversion transition. The resulting map is
an actual self-morphism of the existing glued projective line over its
original base. Over a field, its inverse images of the two chart opens are
the same chart opens, giving actual affine pullback squares.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-- Squaring on the actual affine coordinate scheme. -/
def chartSquare : Spec (.of (Polynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (PolynomialSquare.squareHom k))

instance chartSquare_isFinite : IsFinite (chartSquare k) := by
  unfold chartSquare
  rw [IsFinite.SpecMap_iff]
  exact PolynomialSquare.squareHom_finite k

instance chartSquare_isFlat : Flat (chartSquare k) := by
  unfold chartSquare
  rw [Flat.SpecMap_iff]
  exact PolynomialSquare.squareHom_flat k

/-- The affine morphism retains the rank of the exact original polynomial map. -/
theorem chartSquare_finrank [Nontrivial k] (x : Spec (.of (Polynomial k))) :
    (chartSquare k).finrank x = 2 := by
  change (Spec.map (CommRingCat.ofHom (PolynomialSquare.squareHom k))).finrank x = 2
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank
    (PolynomialSquare.squareHom_finite k) (PolynomialSquare.squareHom_flat k)]
  exact PolynomialSquare.squareHom_finrank k x

/-- The additive exponent map underlying Laurent squaring. -/
def doubleExponent : ℤ →+ ℤ where
  toFun n := n + n
  map_zero' := rfl
  map_add' a b := add_add_add_comm a b a b

/-- The original Laurent-polynomial endomorphism doubling each exponent. -/
def laurentSquareHom : LaurentPolynomial k →+* LaurentPolynomial k :=
  AddMonoidAlgebra.mapDomainRingHom k doubleExponent

@[simp]
theorem laurentSquareHom_C (c : k) :
    laurentSquareHom k (LaurentPolynomial.C c) = LaurentPolynomial.C c := by
  change AddMonoidAlgebra.mapDomain doubleExponent
    (AddMonoidAlgebra.single 0 c) = AddMonoidAlgebra.single 0 c
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

@[simp]
theorem laurentSquareHom_T (n : ℤ) :
    laurentSquareHom k (LaurentPolynomial.T n) = LaurentPolynomial.T (n + n) := by
  change AddMonoidAlgebra.mapDomain doubleExponent
    (AddMonoidAlgebra.single n (1 : k)) = AddMonoidAlgebra.single (n + n) (1 : k)
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

/-- Squaring commutes with the actual Laurent inversion transition. -/
theorem laurentSquareHom_invert :
    (laurentSquareHom k).comp (LaurentPolynomial.invert (R := k)).toRingHom =
      (LaurentPolynomial.invert (R := k)).toRingHom.comp (laurentSquareHom k) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    change laurentSquareHom k (LaurentPolynomial.invert (LaurentPolynomial.C c)) =
      LaurentPolynomial.invert (laurentSquareHom k (LaurentPolynomial.C c))
    simp
  · intro n
    change laurentSquareHom k (LaurentPolynomial.invert (LaurentPolynomial.T n)) =
      LaurentPolynomial.invert (laurentSquareHom k (LaurentPolynomial.T n))
    simp

/-- Squaring on the actual punctured coordinate scheme. -/
def overlapSquare : Spec (.of (LaurentPolynomial k)) ⟶
    Spec (.of (LaurentPolynomial k)) :=
  Spec.map (CommRingCat.ofHom (laurentSquareHom k))

@[reassoc]
theorem punctured_chart_square :
    overlapSquare k ≫ projectiveLinePuncturedChart k =
      projectiveLinePuncturedChart k ≫ chartSquare k := by
  unfold overlapSquare projectiveLinePuncturedChart chartSquare
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp [PolynomialSquare.squareHom]
  · simp [PolynomialSquare.squareHom]

@[reassoc]
theorem overlapSquare_inversion :
    overlapSquare k ≫ (projectiveLineInversionIso k).hom =
      (projectiveLineInversionIso k).hom ≫ overlapSquare k := by
  change Spec.map (CommRingCat.ofHom (laurentSquareHom k)) ≫
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := k)).toRingHom) =
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (laurentSquareHom k))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact laurentSquareHom_invert k

/-- The chart square maps satisfy the original gluing compatibility. -/
theorem overlap_compat :
    projectiveLinePuncturedChart k ≫ chartSquare k ≫ projectiveLineXChart k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
        chartSquare k ≫ projectiveLineYChart k := by
  calc
    projectiveLinePuncturedChart k ≫ chartSquare k ≫ projectiveLineXChart k =
        overlapSquare k ≫ projectiveLinePuncturedChart k ≫ projectiveLineXChart k := by
          rw [punctured_chart_square_assoc]
    _ = overlapSquare k ≫ (projectiveLineInversionIso k).hom ≫
        projectiveLinePuncturedChart k ≫ projectiveLineYChart k := by
          rw [projectiveLineOverlap_compat]
    _ = (overlapSquare k ≫ (projectiveLineInversionIso k).hom) ≫
        projectiveLinePuncturedChart k ≫ projectiveLineYChart k := by
          simp only [Category.assoc]
    _ = ((projectiveLineInversionIso k).hom ≫ overlapSquare k) ≫
        projectiveLinePuncturedChart k ≫ projectiveLineYChart k := by
          rw [overlapSquare_inversion]
    _ = (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
        chartSquare k ≫ projectiveLineYChart k := by
          simp only [Category.assoc, punctured_chart_square_assoc]

/-- The same gluing compatibility in the reverse chart order. -/
theorem overlap_compat_reverse :
    projectiveLinePuncturedChart k ≫ chartSquare k ≫ projectiveLineYChart k =
      (projectiveLineInversionIso k).inv ≫ projectiveLinePuncturedChart k ≫
        chartSquare k ≫ projectiveLineXChart k := by
  rw [← cancel_epi (projectiveLineInversionIso k).hom]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using (overlap_compat k).symm

/-- The actual gluing descent, together with its original affine chart equations. -/
def squareWithCharts :
    {f : projectiveLine k ⟶ projectiveLine k //
      ∀ i : (projectiveLineGluingData k).J,
        (projectiveLineGluingData k).ι i ≫ f =
          chartSquare k ≫ (projectiveLineGluingData k).ι i} := by
  let D := projectiveLineGluingData k
  refine ⟨Multicoequalizer.desc D.toGlueData.diagram _
    (fun i => chartSquare k ≫ D.ι i) ?_,
    fun i => Multicoequalizer.π_desc (I := D.toGlueData.diagram) _ _ _ i⟩
  intro a
  rcases a with ⟨⟨i⟩, ⟨j⟩⟩
  change D.f ⟨i⟩ ⟨j⟩ ≫ chartSquare k ≫ D.ι ⟨i⟩ =
    D.t ⟨i⟩ ⟨j⟩ ≫ D.f ⟨j⟩ ⟨i⟩ ≫ chartSquare k ≫ D.ι ⟨j⟩
  cases i <;> cases j
  · simp [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', projectiveLineGluingData']
  · simpa [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', projectiveLineGluingData', projectiveLineXChart,
      projectiveLineYChart, projectiveLineXIndex, projectiveLineYIndex,
      CategoryTheory.eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.eqToHom_comp_iff, Category.assoc] using overlap_compat k
  · simpa [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', projectiveLineGluingData', projectiveLineXChart,
      projectiveLineYChart, projectiveLineXIndex, projectiveLineYIndex,
      CategoryTheory.eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.eqToHom_comp_iff, Category.assoc] using overlap_compat_reverse k
  · simp [D, projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f', projectiveLineGluingData']

/-- The actual squaring self-morphism of the original glued projective line. -/
def square : projectiveLine k ⟶ projectiveLine k := (squareWithCharts k).1

@[reassoc (attr := simp)]
theorem chart_square_x :
    projectiveLineXChart k ≫ square k = chartSquare k ≫ projectiveLineXChart k :=
  (squareWithCharts k).2 (projectiveLineXIndex k)

@[reassoc (attr := simp)]
theorem chart_square_y :
    projectiveLineYChart k ≫ square k = chartSquare k ≫ projectiveLineYChart k :=
  (squareWithCharts k).2 (projectiveLineYIndex k)

@[simp, reassoc]
theorem chartSquare_over_base :
    chartSquare k ≫ projectiveLineAffineStructureMorphism k =
      projectiveLineAffineStructureMorphism k := by
  unfold chartSquare projectiveLineAffineStructureMorphism
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext c
  simp [PolynomialSquare.squareHom]

/-- The actual global squaring morphism retains the original structure map. -/
@[simp, reassoc]
theorem over_base :
    square k ≫ (projectiveLine k ↘ Spec (.of k)) =
      (projectiveLine k ↘ Spec (.of k)) := by
  apply (projectiveLineOpenCover k).hom_ext
  rintro ⟨i⟩
  cases i
  · change projectiveLineXChart k ≫ square k ≫ _ = projectiveLineXChart k ≫ _
    rw [chart_square_x_assoc, projectiveLineXChart_comp_structureMorphism,
      chartSquare_over_base]
  · change projectiveLineYChart k ≫ square k ≫ _ = projectiveLineYChart k ≫ _
    rw [chart_square_y_assoc, projectiveLineYChart_comp_structureMorphism,
      chartSquare_over_base]

/-- The actual affine section with the specified coordinate. -/
def affineSection (z : k) : Spec (.of k) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom z))

@[simp, reassoc]
theorem affineSection_square (z : k) :
    affineSection k z ≫ chartSquare k = affineSection k (z ^ 2) := by
  unfold affineSection chartSquare
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp [PolynomialSquare.squareHom]
  · simp [PolynomialSquare.squareHom]

/-- The actual finite-coordinate section of the original glued scheme. -/
def finiteSection (z : k) : Spec (.of k) ⟶ projectiveLine k :=
  affineSection k z ≫ projectiveLineXChart k

/-- The actual reciprocal-coordinate section of the original glued scheme. -/
def reciprocalSection (z : k) : Spec (.of k) ⟶ projectiveLine k :=
  affineSection k z ≫ projectiveLineYChart k

@[simp, reassoc]
theorem finiteSection_square (z : k) :
    finiteSection k z ≫ square k = finiteSection k (z ^ 2) := by
  unfold finiteSection
  rw [Category.assoc, chart_square_x, ← Category.assoc, affineSection_square]

@[simp, reassoc]
theorem reciprocalSection_square (z : k) :
    reciprocalSection k z ≫ square k = reciprocalSection k (z ^ 2) := by
  unfold reciprocalSection
  rw [Category.assoc, chart_square_y, ← Category.assoc, affineSection_square]

/-- The original evaluation-at-zero section of the affine chart. -/
def affineZeroSection : Spec (.of k) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))

@[simp, reassoc]
theorem affineZeroSection_square :
    affineZeroSection k ≫ chartSquare k = affineZeroSection k := by
  unfold affineZeroSection chartSquare
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp [PolynomialSquare.squareHom]
  · simp [PolynomialSquare.squareHom]

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The domain is the actual connected projective line, independently of its fibers. -/
theorem source_connected : ConnectedSpace (projectiveLine k) := inferInstance

/-- Squaring fixes the actual affine origin prime. -/
@[simp]
theorem chartSquare_origin : chartSquare k (affineLineOrigin k) = affineLineOrigin k := by
  apply eq_affineLineOrigin_of_X_mem
  change PolynomialSquare.squareHom k Polynomial.X ∈
    (affineLineOrigin k).asIdeal
  rw [PolynomialSquare.squareHom_X]
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (by simp)) 2 (by decide)

@[simp]
theorem zero_fixed : square k (projectiveLineZero k) = projectiveLineZero k := by
  change (projectiveLineXChart k ≫ square k) (affineLineOrigin k) = _
  rw [chart_square_x, Scheme.Hom.comp_apply, chartSquare_origin]
  rfl

@[simp]
theorem infinity_fixed :
    square k (projectiveLineInfinity k) = projectiveLineInfinity k := by
  change (projectiveLineYChart k ≫ square k) (affineLineOrigin k) = _
  rw [chart_square_y, Scheme.Hom.comp_apply, chartSquare_origin]
  rfl

/-- The actual existing zero section, retaining its original affine evaluation. -/
abbrev zeroSection : Spec (.of k) ⟶ projectiveLine k := projectiveLineZeroSection k

@[simp, reassoc]
theorem zeroSection_square : zeroSection k ≫ square k = zeroSection k := by
  change affineZeroSection k ≫ projectiveLineXChart k ≫ square k =
    affineZeroSection k ≫ projectiveLineXChart k
  rw [chart_square_x, ← Category.assoc, affineZeroSection_square]

/-- The original evaluation-at-zero section of the infinity chart. -/
def infinitySection : Spec (.of k) ⟶ projectiveLine k :=
  affineZeroSection k ≫ projectiveLineYChart k

@[simp, reassoc]
theorem infinitySection_square :
    infinitySection k ≫ square k = infinitySection k := by
  change affineZeroSection k ≫ projectiveLineYChart k ≫ square k =
    affineZeroSection k ≫ projectiveLineYChart k
  rw [chart_square_y, ← Category.assoc, affineZeroSection_square]

/-- The actual zero point lies outside the second original affine chart. -/
theorem zero_notMem_yChart :
    projectiveLineZero k ∉ Set.range (projectiveLineYChart k).base := by
  rintro ⟨b, hb⟩
  obtain ⟨w, hw, -⟩ :=
    (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k
      (affineLineOrigin k) b).mp hb.symm
  exact (mem_range_projectiveLinePuncturedChart_iff k _).mp ⟨w, hw⟩
    (Ideal.subset_span rfl)

/-- Every actual point lies in the second chart or is the original zero point. -/
theorem mem_yChart_or_eq_zero (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineYChart k).base ∨ x = projectiveLineZero k := by
  rcases projectiveLine_charts_cover k x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · by_cases ha : (Polynomial.X : Polynomial k) ∈ a.asIdeal
    · right
      rw [eq_affineLineOrigin_of_X_mem a ha]
      rfl
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLinePuncturedChart_iff k a).mpr ha
      left
      refine ⟨projectiveLineOverlapYInclusion k w, ?_⟩
      rw [← hw]
      exact congrArg (fun f : Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k => f w)
        (projectiveLineOverlap_compat k).symm
  · exact Or.inl ⟨b, rfl⟩

/-- The inverse image of the original finite-coordinate chart is the same chart. -/
theorem preimage_xChart :
    square k ⁻¹ᵁ (projectiveLineXChart k).opensRange =
      (projectiveLineXChart k).opensRange := by
  ext x
  change square k x ∈ Set.range (projectiveLineXChart k).base ↔
    x ∈ Set.range (projectiveLineXChart k).base
  constructor
  · intro hx
    rcases mem_range_projectiveLineXChart_or_eq_infinity x with h | rfl
    · exact h
    · exact (projectiveLineInfinity_notMem_range_XChart k (infinity_fixed k ▸ hx)).elim
  · rintro ⟨a, rfl⟩
    refine ⟨chartSquare k a, ?_⟩
    exact (congrArg (fun f : Spec (.of (Polynomial k)) ⟶ projectiveLine k => f a)
      (chart_square_x k)).symm

/-- The inverse image of the original infinity-coordinate chart is the same chart. -/
theorem preimage_yChart :
    square k ⁻¹ᵁ (projectiveLineYChart k).opensRange =
      (projectiveLineYChart k).opensRange := by
  ext x
  change square k x ∈ Set.range (projectiveLineYChart k).base ↔
    x ∈ Set.range (projectiveLineYChart k).base
  constructor
  · intro hx
    rcases mem_yChart_or_eq_zero k x with h | rfl
    · exact h
    · exact (zero_notMem_yChart k (zero_fixed k ▸ hx)).elim
  · rintro ⟨a, rfl⟩
    refine ⟨chartSquare k a, ?_⟩
    exact (congrArg (fun f : Spec (.of (Polynomial k)) ⟶ projectiveLine k => f a)
      (chart_square_y k)).symm

/-- The only actual scheme point over zero is zero; its scheme-fiber
multiplicity is retained separately by the finite flat theory. -/
@[simp]
theorem square_eq_zero_iff (x : projectiveLine k) :
    square k x = projectiveLineZero k ↔ x = projectiveLineZero k := by
  constructor
  · intro hx
    rcases mem_yChart_or_eq_zero k x with ⟨a, rfl⟩ | h
    · exfalso
      apply zero_notMem_yChart k
      refine ⟨chartSquare k a, ?_⟩
      exact (congrArg (fun f : Spec (.of (Polynomial k)) ⟶ projectiveLine k => f a)
        (chart_square_y k)).symm.trans hx
    · exact h
  · rintro rfl
    exact zero_fixed k

/-- The only actual scheme point over infinity is infinity. -/
@[simp]
theorem square_eq_infinity_iff (x : projectiveLine k) :
    square k x = projectiveLineInfinity k ↔ x = projectiveLineInfinity k := by
  constructor
  · intro hx
    rcases mem_range_projectiveLineXChart_or_eq_infinity x with ⟨a, rfl⟩ | h
    · exfalso
      apply projectiveLineInfinity_notMem_range_XChart k
      refine ⟨chartSquare k a, ?_⟩
      exact (congrArg (fun f : Spec (.of (Polynomial k)) ⟶ projectiveLine k => f a)
        (chart_square_x k)).symm.trans hx
    · exact h
  · rintro rfl
    exact infinity_fixed k

/-- The affine square is the actual pullback of global squaring along the first chart. -/
theorem chart_x_isPullback :
    IsPullback (projectiveLineXChart k) (chartSquare k) (square k)
      (projectiveLineXChart k) :=
  (IsOpenImmersion.isPullback (chartSquare k) (projectiveLineXChart k)
    (projectiveLineXChart k) (square k) (chart_square_x k) (preimage_xChart k)).flip

/-- The affine square is the actual pullback of global squaring along the second chart. -/
theorem chart_y_isPullback :
    IsPullback (projectiveLineYChart k) (chartSquare k) (square k)
      (projectiveLineYChart k) :=
  (IsOpenImmersion.isPullback (chartSquare k) (projectiveLineYChart k)
    (projectiveLineYChart k) (square k) (chart_square_y k) (preimage_yChart k)).flip

/-- Actual global finiteness follows from the two proved affine pullback squares. -/
instance square_isFinite : IsFinite (square k) := by
  apply IsZariskiLocalAtTarget.of_openCover (projectiveLineOpenCover k)
  rintro ⟨i⟩
  cases i
  · change IsFinite (pullback.snd (square k) (projectiveLineXChart k))
    rw [← (chart_x_isPullback k).isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (square k) (projectiveLineYChart k))
    rw [← (chart_y_isPullback k).isoPullback_inv_snd]
    infer_instance

/-- The original global map is flat, including its ramified fibers. -/
instance square_isFlat : Flat (square k) := by
  apply IsZariskiLocalAtTarget.of_openCover (projectiveLineOpenCover k)
  rintro ⟨i⟩
  cases i
  · change Flat (pullback.snd (square k) (projectiveLineXChart k))
    rw [← (chart_x_isPullback k).isoPullback_inv_snd]
    infer_instance
  · change Flat (pullback.snd (square k) (projectiveLineYChart k))
    rw [← (chart_y_isPullback k).isoPullback_inv_snd]
    infer_instance

/-- The original connected projective-line selfmap has constant geometric rank two. -/
theorem square_finrank (x : projectiveLine k) : (square k).finrank x = 2 := by
  rcases projectiveLine_charts_cover k x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have h := Scheme.Hom.finrank_of_isPullback (projectiveLineXChart k)
      (chartSquare k) (square k) (projectiveLineXChart k) (chart_x_isPullback k) a
    exact h.symm.trans (chartSquare_finrank k a)
  · have h := Scheme.Hom.finrank_of_isPullback (projectiveLineYChart k)
      (chartSquare k) (square k) (projectiveLineYChart k) (chart_y_isPullback k) a
    exact h.symm.trans (chartSquare_finrank k a)

/-- Positive actual geometric rank makes the original squaring morphism surjective. -/
instance square_isSurjective : Surjective (square k) := by
  apply (Scheme.Hom.one_le_finrank_iff_surjective (square k)).mp
  intro x
  rw [square_finrank]
  norm_num

end Field

/-- The canonical analytic map of actual scheme-valued complex points. -/
def complexMap :
    C(Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)),
      Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  ⟨Scheme.ComplexPoints.map (square ℂ) (over_base ℂ),
    Scheme.ComplexPoints.continuous_map (square ℂ) (over_base ℂ)⟩

@[simp]
theorem complexMap_hom
    (z : Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :
    (complexMap z).hom = z.hom ≫ square ℂ := rfl

end

end HodgeConjecture.ProjectiveLineSquare
