module

public import HodgeConjecture.Correspondence.Examples.SplitPointDimension
public import HodgeConjecture.Cycles.Basic

@[expose] public section

/-!
# Integral closed subschemes of finite split schemes

An actual integral closed subscheme of `Spec (I → K)` is uniquely one of
the reduced rational point components. The isomorphism respects the given
closed immersion, not only the underlying topological point.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K] (I : Type u) [Finite I]

/-- The component inclusion has precisely its labelled point as image. -/
theorem range_pointInclusion (i : I) :
    Set.range (pointInclusion K I i).base = {labelEquivScheme K I i} := by
  apply Set.range_eq_singleton
  intro x
  rw [labelEquivScheme_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- An integral closed immersion into a split finite scheme is, over the
target scheme, uniquely the inclusion of one reduced rational point. -/
theorem existsUnique_pointIso_of_isIntegral
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ scheme K I) [IsClosedImmersion f] :
    ∃! i : I, ∃ e : X ≅ Spec (.of K), e.hom ≫ pointInclusion K I i = f := by
  classical
  obtain ⟨i, hi⟩ := range_eq_point K I f
  have hRange : Set.range f.base ⊆ Set.range (pointInclusion K I i).base := by
    rw [hi, range_pointInclusion]
  let g := IsOpenImmersion.lift (pointInclusion K I i) f hRange
  have hg : g ≫ pointInclusion K I i = f := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (g ≫ pointInclusion K I i) := hg.symm ▸ inferInstance
  haveI : IsClosedImmersion g :=
    IsClosedImmersion.of_comp_isClosedImmersion g (pointInclusion K I i)
  haveI : Surjective g := ⟨fun y ↦ ⟨Classical.arbitrary X, Subsingleton.elim _ y⟩⟩
  haveI : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  refine ⟨i, ⟨asIso g, hg⟩, ?_⟩
  rintro j ⟨e, he⟩
  apply (labelEquivScheme K I).injective
  have hx : f.base (Classical.arbitrary X) = labelEquivScheme K I i :=
    Function.apply_eq_of_range_eq_singleton hi _
  have hj : f.base (Classical.arbitrary X) = labelEquivScheme K I j := by
    rw [← he]
    exact Function.apply_eq_of_range_eq_singleton (range_pointInclusion K I j) _
  exact hj.symm.trans hx

/-- Integral closed subschemes are represented canonically by their actual
ideal-sheaf data and associated subschemes. -/
abbrev IntegralClosedSubscheme :=
  SchemeCycles.IntegralClosedSubscheme (scheme K I)

/-- The ideal sheaf of the labelled reduced point component. -/
def pointIdealSheaf (i : I) : (scheme K I).IdealSheafData :=
  (pointInclusion K I i).ker

omit [Finite I] in
/-- The canonical subscheme of a point's ideal sheaf is integral. -/
theorem pointIdealSheaf_isIntegral (i : I) :
    IsIntegral (pointIdealSheaf K I i).subscheme := by
  change IsIntegral (pointInclusion K I i).image
  haveI : Nonempty (pointInclusion K I i).image :=
    ⟨(pointInclusion K I i).toImage.base (default : PrimeSpectrum K)⟩
  exact isIntegral_of_isOpenImmersion (inv (pointInclusion K I i).toImage)

/-- A labelled point as an actual integral closed subscheme. -/
def pointIntegralSubscheme (i : I) : IntegralClosedSubscheme K I :=
  ⟨pointIdealSheaf K I i, pointIdealSheaf_isIntegral K I i⟩

/-- Every integral ideal-sheaf subscheme is the ideal sheaf of a point. -/
theorem exists_pointIdealSheaf (J : IntegralClosedSubscheme K I) :
    ∃ i : I, J.val = pointIdealSheaf K I i := by
  letI := J.property
  obtain ⟨i, ⟨e, he⟩, _⟩ := existsUnique_pointIso_of_isIntegral K I J.val.subschemeι
  refine ⟨i, ?_⟩
  rw [← J.val.ker_subschemeι, ← he, Scheme.Hom.ker_comp_of_isIso]
  rfl

/-- Distinct labels define distinct ideal-sheaf subschemes. -/
theorem pointIdealSheaf_injective : Function.Injective (pointIdealSheaf K I) := by
  intro i j hij
  apply (labelEquivScheme K I).injective
  have h := congrArg (fun J : (scheme K I).IdealSheafData ↦
    (J.support : Set (scheme K I))) hij
  simpa [pointIdealSheaf, Scheme.Hom.support_ker, range_pointInclusion] using h

/-- The labels are exactly the integral closed subschemes, with their full
scheme structure encoded by ideal sheaves. -/
def labelEquivIntegralClosedSubscheme : I ≃ IntegralClosedSubscheme K I :=
  Equiv.ofBijective (pointIntegralSubscheme K I) ⟨
    fun _ _ h ↦ pointIdealSheaf_injective K I (congrArg Subtype.val h),
    fun J ↦ by
      obtain ⟨i, hi⟩ := exists_pointIdealSheaf K I J
      exact ⟨i, Subtype.ext hi.symm⟩⟩

@[simp]
theorem labelEquivIntegralClosedSubscheme_apply (i : I) :
    labelEquivIntegralClosedSubscheme K I i = pointIntegralSubscheme K I i := rfl

instance : Finite (IntegralClosedSubscheme K I) :=
  Finite.of_equiv I (labelEquivIntegralClosedSubscheme K I)

/-- Every actual integral cycle-support subscheme has dimension zero. -/
theorem integralClosedSubscheme_dimension (J : IntegralClosedSubscheme K I) :
    topologicalKrullDim J.val.subscheme = 0 := by
  letI := J.property
  exact topologicalKrullDim_eq_zero_of_isClosedImmersion K I J.val.subschemeι

end SplitPointGeometry

end

end HodgeConjecture
