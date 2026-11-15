module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps

/-!
# A Mayer–Vietoris criterion for spanning the product's singular H²

The two projection classes are already independent. This theorem isolates the
local topological calculations that would also make them spanning: a generator
of the overlap's H¹ whose boundary is the first projection class, a generator
of one chart's H² given by the second class, and injectivity of the opposite
chart's restriction to the overlap. The argument uses the proved exact
singular Mayer–Vietoris sequence on the canonical scheme complex points.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductBetti

open AlgebraicGeometry CategoryTheory

abbrev ProductSpace := SchemeBetti.space
  (projectiveLineProductStructureMorphism ℂ)

/-- The proved one-dimensional coordinate on canonical projective-line H². -/
def lineCoordinate : LineH2 ≃ₗ[ℚ] ℚ :=
  canonicalBettiEquiv.symm.trans ProjectiveLineBettiCohomology.h2Equiv

@[simp] theorem lineCoordinate_generator : lineCoordinate lineGenerator = 1 := by
  change ProjectiveLineBettiCohomology.h2Equiv
    (canonicalBettiEquiv.symm (canonicalBettiEquiv
      ProjectiveLineBettiCohomology.coverGenerator)) = 1
  rw [LinearEquiv.symm_apply_apply,
    ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]

/-- The two coordinate-fiber probes, expressed as rational numbers. -/
def coordinateProbe : ProductH2 →ₗ[ℚ] ℚ × ℚ :=
  (lineCoordinate.toLinearMap.comp firstProbe.hom).prod
    (lineCoordinate.toLinearMap.comp secondProbe.hom)

/-- The obvious section given by the two projection-pullback classes. -/
def coordinateSection : ℚ × ℚ →ₗ[ℚ] ProductH2 where
  toFun ab := ab.1 • firstClass + ab.2 • secondClass
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c ab := by
    rcases ab with ⟨a, b⟩
    simp [Algebra.smul_def, smul_add, smul_smul]

/-- The actual coordinate probes split off a copy of `ℚ²` in product H². -/
theorem coordinateProbe_section (ab : ℚ × ℚ) :
    coordinateProbe (coordinateSection ab) = ab := by
  rcases ab with ⟨a, b⟩
  apply Prod.ext
  · simp [coordinateProbe, coordinateSection]
  · simp [coordinateProbe, coordinateSection]

theorem coordinateProbe_surjective : Function.Surjective coordinateProbe := by
  intro ab
  exact ⟨coordinateSection ab, coordinateProbe_section ab⟩

theorem firstClass_ne_zero : firstClass ≠ 0 := by
  intro h
  apply lineGenerator_ne_zero
  simpa only [firstProbe_firstClass, map_zero] using congrArg firstProbe h

/-- Joint injectivity of the two actual fiber probes is enough for spanning. -/
theorem classes_span_of_coordinateProbe_injective
    (hprobe : Function.Injective coordinateProbe) (z : ProductH2) :
    ∃ a b : ℚ, z = a • firstClass + b • secondClass := by
  refine ⟨(coordinateProbe z).1, (coordinateProbe z).2, ?_⟩
  change z = coordinateSection (coordinateProbe z)
  exact (hprobe (coordinateProbe_section (coordinateProbe z))).symm

/-- The two product classes span once the three local cohomology calculations
for an actual two-open cover have been supplied. -/
theorem classes_span_of_mayer_vietoris
    (U V : Set ProductSpace) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (κ : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1)
    (hκ : ∀ t : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1,
      ∃ a : ℚ, t = a • κ)
    (hboundary : SingularMayerVietoris.connecting ProductSpace U V hU hV hcover 1 κ =
      firstClass)
    (hchart : ∀ y : SingularCochains.Cohomology (TopCat.of U) 2,
      ∃ b : ℚ, y = b •
        (SingularMayerVietoris.restriction ProductSpace U V 2 secondClass).1)
    (hoverlap : Function.Injective
      (SingularCochains.cohomologyPullback
        (SingularMayerVietoris.intersectionToRight ProductSpace U V) 2))
    (z : ProductH2) :
    ∃ a b : ℚ, z = a • firstClass + b • secondClass := by
  let r := SingularMayerVietoris.restriction ProductSpace U V 2
  let d := SingularMayerVietoris.difference ProductSpace U V 2
  let c := SingularMayerVietoris.connecting ProductSpace U V hU hV hcover 1
  obtain ⟨b, hb⟩ := hchart (r z).1
  have hrd : d (r (z - b • secondClass)) = 0 := by
    have hcomp := SingularMayerVietoris.restriction_comp_difference
      ProductSpace U V hU hV hcover 2
    exact congrArg (fun f : ProductH2 ⟶ _ ↦ f (z - b • secondClass)) hcomp
  have hfirst : (r (z - b • secondClass)).1 = 0 := by
    simp only [map_sub, map_smul, Prod.fst_sub]
    rw [hb]
    exact sub_self _
  have hsecond : (r (z - b • secondClass)).2 = 0 := by
    rw [SingularMayerVietoris.difference_apply] at hrd
    rw [hfirst, map_zero, zero_sub] at hrd
    apply hoverlap
    simpa only [map_zero] using neg_eq_zero.mp hrd
  have hrzero : r (z - b • secondClass) = 0 :=
    Prod.ext hfirst hsecond
  let S := SingularMayerVietoris.unionSequence ProductSpace U V hU hV hcover 1
  have hS : S.Exact :=
    SingularMayerVietoris.unionSequence_exact ProductSpace U V hU hV hcover 1
  have hSg : S.g = r := by
    simpa only [S, r, Nat.reduceAdd] using
      SingularMayerVietoris.unionSequence_g ProductSpace U V hU hV hcover 1
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS
    (z - b • secondClass)
      (by rw [hSg]; exact hrzero)
  obtain ⟨a, ha⟩ := hκ t
  refine ⟨a, b, ?_⟩
  have hc : z - b • secondClass = a • firstClass := by
    have ht' : c t = z - b • secondClass := by
      have hSf : S.f = c := by
        simpa only [S, c] using
          SingularMayerVietoris.unionSequence_f ProductSpace U V hU hV hcover 1
      rw [hSf] at ht
      exact ht
    rw [ha, map_smul, hboundary] at ht'
    exact ht'.symm
  exact (sub_eq_iff_eq_add.mp hc)

/-- Exactness supplies the boundary normalization automatically when the
first projection class dies on the two charts. Thus no separate boundary
naturality calculation is needed for the spanning criterion. -/
theorem classes_span_of_local_cover
    (U V : Set ProductSpace) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (κ : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1)
    (hκ : ∀ t : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1,
      ∃ a : ℚ, t = a • κ)
    (hfirst : SingularMayerVietoris.restriction ProductSpace U V 2 firstClass = 0)
    (hchart : ∀ y : SingularCochains.Cohomology (TopCat.of U) 2,
      ∃ b : ℚ, y = b •
        (SingularMayerVietoris.restriction ProductSpace U V 2 secondClass).1)
    (hoverlap : Function.Injective
      (SingularCochains.cohomologyPullback
        (SingularMayerVietoris.intersectionToRight ProductSpace U V) 2))
    (z : ProductH2) :
    ∃ a b : ℚ, z = a • firstClass + b • secondClass := by
  let S := SingularMayerVietoris.unionSequence ProductSpace U V hU hV hcover 1
  have hS : S.Exact :=
    SingularMayerVietoris.unionSequence_exact ProductSpace U V hU hV hcover 1
  have hSg : S.g = SingularMayerVietoris.restriction ProductSpace U V 2 := by
    simpa only [S, Nat.reduceAdd] using
      SingularMayerVietoris.unionSequence_g ProductSpace U V hU hV hcover 1
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS firstClass
    (by rw [hSg]; exact hfirst)
  have hSf : S.f = SingularMayerVietoris.connecting
      ProductSpace U V hU hV hcover 1 := by
    simpa only [S] using
      SingularMayerVietoris.unionSequence_f ProductSpace U V hU hV hcover 1
  rw [hSf] at ht
  let u : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1 := t
  have hu : SingularMayerVietoris.connecting ProductSpace U V hU hV hcover 1 u =
      firstClass := ht
  obtain ⟨a, ha⟩ := hκ u
  have ha0 : a ≠ 0 := by
    intro hzero
    have huzero : u = 0 := by rw [ha, hzero, zero_smul]
    rw [huzero, map_zero] at hu
    exact firstClass_ne_zero hu.symm
  have htspan : ∀ s : SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) 1,
      ∃ b : ℚ, s = b • u := by
    intro s
    obtain ⟨b, hb⟩ := hκ s
    refine ⟨b / a, ?_⟩
    rw [hb, ha, smul_smul, div_mul_cancel₀ _ ha0]
  exact classes_span_of_mayer_vietoris U V hU hV hcover u htspan hu
    hchart hoverlap z

end HodgeConjecture.ProjectiveLineProductBetti

end
