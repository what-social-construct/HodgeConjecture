module

public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import HodgeConjecture.Realization.Betti.Examples.AffineLineComplexPoints
public import HodgeConjecture.Realization.Betti.Examples.OnePointComplexInversion

/-!
# Complex-valued points of the actual projective line

The point type consists of actual morphisms `Spec ℂ ⟶ ℙ¹_ℂ` over `Spec ℂ`.
Its two charts are induced by polynomial evaluation in the original affine
charts of the glued scheme. The topology is the final topology for those
affine charts with their regular-function evaluation topologies.
-/

@[expose] public section

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

namespace ProjectiveLineComplexPoints

open AlgebraicGeometry CategoryTheory Polynomial Topology OnePoint

/-- Actual complex-valued points of the glued projective-line scheme. -/
def Point := {f : Spec (.of ℂ) ⟶ projectiveLine ℂ //
  f ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _}

/-- The actual scheme morphism underlying a complex point. -/
def schemeMorphism (p : Point) : Spec (.of ℂ) ⟶ projectiveLine ℂ := p.val

@[simp, reassoc]
theorem schemeMorphism_toBase (p : Point) :
    schemeMorphism p ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _ := p.property

@[ext]
theorem ext {p q : Point} (h : schemeMorphism p = schemeMorphism q) : p = q :=
  Subtype.ext h

/-- The affine scheme morphism of an evaluation point, with its coordinate ring explicit. -/
abbrev affineMorphism (p : AffineLineComplexPoints.Point) : Spec (.of ℂ) ⟶ Spec (.of ℂ[X]) :=
  Spec.map (CommRingCat.ofHom p.toRingHom)

/-- Evaluation points in the original first affine chart. -/
def xChart (p : AffineLineComplexPoints.Point) : Point :=
  ⟨affineMorphism p ≫ projectiveLineXChart ℂ, by
    rw [Category.assoc, projectiveLineXChart_comp_structureMorphism]
    unfold affineMorphism projectiveLineAffineStructureMorphism
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ) using 1
    congr 1
    ext c
    exact p.commutes c⟩

/-- Evaluation points in the original second affine chart. -/
def yChart (p : AffineLineComplexPoints.Point) : Point :=
  ⟨affineMorphism p ≫ projectiveLineYChart ℂ, by
    rw [Category.assoc, projectiveLineYChart_comp_structureMorphism]
    unfold affineMorphism projectiveLineAffineStructureMorphism
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ) using 1
    congr 1
    ext c
    exact p.commutes c⟩

/-- The first chart expressed using its complex coordinate. -/
def finite (z : ℂ) : Point := xChart (AffineLineComplexPoints.evalPoint z)

/-- The second chart expressed using its complex coordinate. -/
def reciprocal (z : ℂ) : Point := yChart (AffineLineComplexPoints.evalPoint z)

/-- The infinity point, defined as zero in the original second chart. -/
def infinity : Point := reciprocal 0

/-- An affine-scheme morphism over the complex base comes from evaluation
of an actual complex-algebra homomorphism. -/
theorem exists_affinePoint (f : Spec (.of ℂ) ⟶ Spec (.of ℂ[X]))
    (hf : f ≫ projectiveLineAffineStructureMorphism ℂ = 𝟙 _) :
    ∃ p : AffineLineComplexPoints.Point, affineMorphism p = f := by
  have hc := congrArg Spec.preimage hf
  rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hc
  let p : AffineLineComplexPoints.Point :=
    { (Spec.preimage f).hom with
      commutes' := fun c ↦ congrArg (fun h : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ h c) hc }
  exact ⟨p, Spec.map_preimage f⟩

/-- Every actual complex-valued point lies in one of the original two
affine evaluation charts. -/
theorem charts_cover (p : Point) :
    (∃ a, xChart a = p) ∨ (∃ a, yChart a = p) := by
  let q : Spec (.of ℂ) := default
  rcases projectiveLine_charts_cover ℂ (schemeMorphism p q) with ⟨a, ha⟩ | ⟨a, ha⟩
  · left
    have hr : Set.range (schemeMorphism p) ⊆ Set.range (projectiveLineXChart ℂ) := by
      rintro _ ⟨t, rfl⟩
      exact ⟨a, ha.trans (congrArg (schemeMorphism p) (Subsingleton.elim q t))⟩
    let f := IsOpenImmersion.lift (projectiveLineXChart ℂ) (schemeMorphism p) hr
    have hfac : f ≫ projectiveLineXChart ℂ = schemeMorphism p :=
      IsOpenImmersion.lift_fac _ _ hr
    have hf : f ≫ projectiveLineAffineStructureMorphism ℂ = 𝟙 _ := by
      rw [← projectiveLineXChart_comp_structureMorphism, ← Category.assoc, hfac]
      exact p.property
    obtain ⟨b, hb⟩ := exists_affinePoint f hf
    exact ⟨b, ext (by change affineMorphism b ≫ _ = _; rw [hb, hfac])⟩
  · right
    have hr : Set.range (schemeMorphism p) ⊆ Set.range (projectiveLineYChart ℂ) := by
      rintro _ ⟨t, rfl⟩
      exact ⟨a, ha.trans (congrArg (schemeMorphism p) (Subsingleton.elim q t))⟩
    let f := IsOpenImmersion.lift (projectiveLineYChart ℂ) (schemeMorphism p) hr
    have hfac : f ≫ projectiveLineYChart ℂ = schemeMorphism p :=
      IsOpenImmersion.lift_fac _ _ hr
    have hf : f ≫ projectiveLineAffineStructureMorphism ℂ = 𝟙 _ := by
      rw [← projectiveLineYChart_comp_structureMorphism, ← Category.assoc, hfac]
      exact p.property
    obtain ⟨b, hb⟩ := exists_affinePoint f hf
    exact ⟨b, ext (by change affineMorphism b ≫ _ = _; rw [hb, hfac])⟩

theorem affineMorphism_injective : Function.Injective affineMorphism := by
  intro p q h
  have hr := Spec.map_inj.mp h
  apply Polynomial.algHom_ext
  exact congrArg (fun f : CommRingCat.of ℂ[X] ⟶ CommRingCat.of ℂ ↦ f Polynomial.X) hr

theorem xChart_injective : Function.Injective xChart := by
  intro p q h
  apply affineMorphism_injective
  apply (cancel_mono (projectiveLineXChart ℂ)).mp
  exact congrArg schemeMorphism h

theorem yChart_injective : Function.Injective yChart := by
  intro p q h
  apply affineMorphism_injective
  apply (cancel_mono (projectiveLineYChart ℂ)).mp
  exact congrArg schemeMorphism h

theorem finite_injective : Function.Injective finite := by
  intro z w h
  have hp := xChart_injective h
  simpa using congrArg (fun p : AffineLineComplexPoints.Point ↦ p Polynomial.X) hp

/-- A nonzero complex coordinate defines a point in the actual Laurent overlap. -/
def overlapMorphism (z : ℂ) (hz : z ≠ 0) :
    Spec (.of ℂ) ⟶ Spec (.of (LaurentPolynomial ℂ)) :=
  Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z hz)))

theorem overlapMorphism_x (z : ℂ) (hz : z ≠ 0) :
    overlapMorphism z hz ≫ projectiveLinePuncturedChart ℂ =
      affineMorphism (AffineLineComplexPoints.evalPoint z) := by
  unfold overlapMorphism projectiveLinePuncturedChart affineMorphism
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  · simp [AffineLineComplexPoints.evalPoint]
  · simp [AffineLineComplexPoints.evalPoint]

theorem overlapMorphism_y (z : ℂ) (hz : z ≠ 0) :
    overlapMorphism z hz ≫ (projectiveLineInversionIso ℂ).hom ≫
      projectiveLinePuncturedChart ℂ =
      affineMorphism (AffineLineComplexPoints.evalPoint z⁻¹) := by
  have hi : (projectiveLineInversionIso ℂ).hom =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := ℂ)).toRingHom) := rfl
  rw [hi]
  unfold overlapMorphism projectiveLinePuncturedChart affineMorphism
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  · simp [AffineLineComplexPoints.evalPoint]
  · simp [AffineLineComplexPoints.evalPoint, LaurentPolynomial.eval₂_T]

/-- The chart coordinate change follows from the original scheme-gluing
square and actual Laurent-polynomial evaluation. -/
theorem finite_eq_reciprocal_inv (z : ℂ) (hz : z ≠ 0) :
    finite z = reciprocal z⁻¹ := by
  apply ext
  change affineMorphism _ ≫ _ = affineMorphism _ ≫ _
  rw [← overlapMorphism_x z hz, ← overlapMorphism_y z hz]
  simp only [Category.assoc]
  exact congrArg (overlapMorphism z hz ≫ ·) (projectiveLineOverlap_compat ℂ)

theorem reciprocal_eq_finite_inv (z : ℂ) (hz : z ≠ 0) :
    reciprocal z = finite z⁻¹ := by
  simpa using (finite_eq_reciprocal_inv z⁻¹ (inv_ne_zero hz)).symm

theorem affine_zero_base (q : Spec (.of ℂ)) :
    affineMorphism (AffineLineComplexPoints.evalPoint 0) q = affineLineOrigin ℂ := by
  apply eq_affineLineOrigin_of_X_mem
  change (AffineLineComplexPoints.evalPoint 0) Polynomial.X ∈ q.asIdeal
  simp

theorem infinity_base (q : Spec (.of ℂ)) :
    schemeMorphism infinity q = projectiveLineInfinity ℂ := by
  change projectiveLineYChart ℂ (affineMorphism (AffineLineComplexPoints.evalPoint 0) q) = _
  rw [affine_zero_base]
  rfl

theorem finite_ne_infinity (z : ℂ) : finite z ≠ infinity := by
  intro h
  apply projectiveLineInfinity_notMem_range_XChart ℂ
  refine ⟨affineMorphism (AffineLineComplexPoints.evalPoint z) default, ?_⟩
  exact (congrArg (fun p ↦ schemeMorphism p default) h).trans (infinity_base default)

/-- Every actual complex-valued scheme point is finite or is infinity. -/
theorem finite_or_infinity (p : Point) : (∃ z, finite z = p) ∨ p = infinity := by
  rcases charts_cover p with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact Or.inl ⟨a Polynomial.X, congrArg xChart (AffineLineComplexPoints.evalPoint_coordinate a)⟩
  · have ha : reciprocal (a Polynomial.X) = yChart a :=
      congrArg yChart (AffineLineComplexPoints.evalPoint_coordinate a)
    by_cases hz : a Polynomial.X = 0
    · exact Or.inr (ha.symm.trans (congrArg reciprocal hz))
    · exact Or.inl ⟨(a Polynomial.X)⁻¹, (reciprocal_eq_finite_inv _ hz).symm.trans ha⟩

/-- The algebraically defined map from the one-point set completion to
actual scheme-valued points, before making any topological comparison. -/
def fromOnePoint : OnePoint ℂ → Point := Option.elim' infinity finite

@[simp]
theorem fromOnePoint_infty : fromOnePoint ∞ = infinity := rfl

@[simp]
theorem fromOnePoint_coe (z : ℂ) : fromOnePoint (z : OnePoint ℂ) = finite z := rfl

theorem fromOnePoint_bijective : Function.Bijective fromOnePoint := by
  constructor
  · intro p q h
    cases p using OnePoint.rec with
    | infty =>
      cases q using OnePoint.rec with
      | infty => rfl
      | coe z => exact (finite_ne_infinity z h.symm).elim
    | coe z =>
      cases q using OnePoint.rec with
      | infty => exact (finite_ne_infinity z h).elim
      | coe w => exact congrArg OnePoint.some (finite_injective h)
  · intro p
    rcases finite_or_infinity p with ⟨z, hz⟩ | hp
    · exact ⟨(z : OnePoint ℂ), hz⟩
    · exact ⟨∞, hp.symm⟩

/-- The algebraic classification of actual `Spec ℂ`-valued points. -/
def onePointEquiv : Point ≃ OnePoint ℂ := (Equiv.ofBijective fromOnePoint fromOnePoint_bijective).symm

@[simp]
theorem onePointEquiv_finite (z : ℂ) : onePointEquiv (finite z) = (z : OnePoint ℂ) :=
  onePointEquiv.apply_symm_apply (z : OnePoint ℂ)

@[simp]
theorem onePointEquiv_infinity : onePointEquiv infinity = ∞ :=
  onePointEquiv.apply_symm_apply ∞

@[simp]
theorem onePointEquiv_xChart (p : AffineLineComplexPoints.Point) :
    onePointEquiv (xChart p) = (p Polynomial.X : OnePoint ℂ) := by
  calc
    onePointEquiv (xChart p) = onePointEquiv (finite (p Polynomial.X)) :=
      congrArg onePointEquiv (congrArg xChart (AffineLineComplexPoints.evalPoint_coordinate p)).symm
    _ = _ := onePointEquiv_finite _

@[simp]
theorem onePointEquiv_reciprocal (z : ℂ) :
    onePointEquiv (reciprocal z) = OnePointComplex.inversion (z : OnePoint ℂ) := by
  by_cases hz : z = 0
  · subst z
    simpa only [infinity, OnePointComplex.inversion_coe_zero] using onePointEquiv_infinity
  · simp [reciprocal_eq_finite_inv z hz, hz]

@[simp]
theorem onePointEquiv_yChart (p : AffineLineComplexPoints.Point) :
    onePointEquiv (yChart p) = OnePointComplex.inversion (p Polynomial.X : OnePoint ℂ) := by
  calc
    onePointEquiv (yChart p) = onePointEquiv (reciprocal (p Polynomial.X)) :=
      congrArg onePointEquiv (congrArg yChart (AffineLineComplexPoints.evalPoint_coordinate p)).symm
    _ = _ := onePointEquiv_reciprocal _

@[simp]
theorem fromOnePoint_inversion_coe (z : ℂ) :
    fromOnePoint (OnePointComplex.inversion (z : OnePoint ℂ)) = reciprocal z := by
  by_cases hz : z = 0
  · subst z
    simp [infinity]
  · simp [hz, reciprocal_eq_finite_inv z hz]

/-- The topology generated by the original two affine evaluation charts. -/
instance pointTopology : TopologicalSpace Point :=
  TopologicalSpace.coinduced (Sum.elim xChart yChart) inferInstance

theorem continuous_xChart : Continuous xChart :=
  (continuous_coinduced_rng (f := Sum.elim xChart yChart)).comp continuous_inl

theorem continuous_yChart : Continuous yChart :=
  (continuous_coinduced_rng (f := Sum.elim xChart yChart)).comp continuous_inr

theorem continuous_finite : Continuous finite :=
  continuous_xChart.comp AffineLineComplexPoints.continuous_evalPoint

theorem continuous_reciprocal : Continuous reciprocal :=
  continuous_yChart.comp AffineLineComplexPoints.continuous_evalPoint

/-- The universal property of the actual affine-chart evaluation topology. -/
theorem continuous_iff_charts {T : Type*} [TopologicalSpace T] (f : Point → T) :
    Continuous f ↔ Continuous (f ∘ xChart) ∧ Continuous (f ∘ yChart) := by
  change Continuous[TopologicalSpace.coinduced (Sum.elim xChart yChart) _, _] f ↔ _
  rw [continuous_coinduced_dom, continuous_sum_dom]
  rfl

theorem continuous_onePointEquiv : Continuous onePointEquiv := by
  rw [continuous_iff_charts]
  constructor
  · convert OnePoint.continuous_coe.comp
      (AffineLineComplexPoints.continuous_evaluation Polynomial.X) using 1
    ext p
    simp
  · convert OnePointComplex.continuous_inversion.comp
      (OnePoint.continuous_coe.comp
        (AffineLineComplexPoints.continuous_evaluation Polynomial.X)) using 1
    ext p
    simp

theorem continuous_fromOnePoint : Continuous fromOnePoint := by
  apply continuous_iff_continuousAt.mpr
  intro p
  cases p using OnePoint.rec with
  | coe z =>
    rw [OnePoint.continuousAt_coe]
    exact continuous_finite.continuousAt
  | infty =>
    have hi : ContinuousAt (fromOnePoint ∘ OnePointComplex.inversion)
        ((0 : ℂ) : OnePoint ℂ) := by
      rw [OnePoint.continuousAt_coe]
      simpa only [Function.comp_def, fromOnePoint_inversion_coe] using
        continuous_reciprocal.continuousAt (x := (0 : ℂ))
    have hg : ContinuousAt OnePointComplex.inversion (∞ : OnePoint ℂ) :=
      OnePointComplex.continuous_inversion.continuousAt
    have h := hi.comp (f := OnePointComplex.inversion) (x := (∞ : OnePoint ℂ)) hg
    simpa only [Function.comp_def, OnePointComplex.inversion_inversion] using h

/-- The native one-point compactification is homeomorphic to actual
complex-valued scheme points with the topology from their original affine
regular-function evaluations. -/
def onePointHomeomorph : Point ≃ₜ OnePoint ℂ where
  toEquiv := onePointEquiv
  continuous_toFun := continuous_onePointEquiv
  continuous_invFun := continuous_fromOnePoint

@[simp]
theorem onePointHomeomorph_finite (z : ℂ) :
    onePointHomeomorph (finite z) = (z : OnePoint ℂ) := onePointEquiv_finite z

@[simp]
theorem onePointHomeomorph_infinity : onePointHomeomorph infinity = ∞ := onePointEquiv_infinity

@[simp]
theorem onePointHomeomorph_reciprocal (z : ℂ) :
    onePointHomeomorph (reciprocal z) = OnePointComplex.inversion (z : OnePoint ℂ) :=
  onePointEquiv_reciprocal z

@[simp]
theorem onePointHomeomorph_xChart (p : AffineLineComplexPoints.Point) :
    onePointHomeomorph (xChart p) = (p Polynomial.X : OnePoint ℂ) := onePointEquiv_xChart p

@[simp]
theorem onePointHomeomorph_yChart (p : AffineLineComplexPoints.Point) :
    onePointHomeomorph (yChart p) = OnePointComplex.inversion (p Polynomial.X : OnePoint ℂ) :=
  onePointEquiv_yChart p

@[simp]
theorem onePointHomeomorph_symm_apply (p : OnePoint ℂ) :
    onePointHomeomorph.symm p = fromOnePoint p := rfl

instance pointCompactSpace : CompactSpace Point := onePointHomeomorph.symm.compactSpace

instance pointT2Space : T2Space Point := onePointHomeomorph.isEmbedding.t2Space

/-- The first analytic chart is open for the original affine evaluation topology. -/
theorem isOpenEmbedding_finite : IsOpenEmbedding finite := by
  simpa only [Function.comp_def, onePointHomeomorph_symm_apply, fromOnePoint_coe] using
    onePointHomeomorph.symm.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

/-- The second analytic chart is open, including its value at infinity. -/
theorem isOpenEmbedding_reciprocal : IsOpenEmbedding reciprocal := by
  simpa only [Function.comp_def, onePointHomeomorph_symm_apply,
    OnePointComplex.inversionHomeomorph_apply,
    fromOnePoint_inversion_coe] using
      onePointHomeomorph.symm.isOpenEmbedding.comp
        (OnePointComplex.inversionHomeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe)

/-- The finite analytic chart is exactly the complement of the actual infinity point. -/
theorem range_finite : Set.range finite = {infinity}ᶜ := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact finite_ne_infinity z
  · intro hp
    rcases finite_or_infinity p with h | h
    · exact h
    · exact (hp h).elim

/-- The two actual affine analytic chart ranges cover the complex point space. -/
theorem range_finite_union_reciprocal : Set.range finite ∪ Set.range reciprocal = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases finite_or_infinity p with h | h
  · exact Or.inl h
  · exact Or.inr ⟨0, h.symm⟩

end ProjectiveLineComplexPoints

end

end HodgeConjecture
