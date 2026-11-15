module

public import HodgeConjecture.SheafCohomology.LinearCoefficients
public import HodgeConjecture.SheafCohomology.TwoOpenModules
public import HodgeConjecture.SheafCohomology.DerivedPostcompose

@[expose] public section

/-!
# Higher derived sections of the existing flasque sheaves

The existing flasque Čech vanishing theorem and the complete shared
Čech-to-derived criterion apply to all opens and all their covers.
Exact coefficient forgetting identifies the actual module-valued
derived sections, rather than introducing another cohomology object.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology

universe u v w

namespace Cohomology.BasisCycles

open HodgeConjecture.SheafCohomology.Cohomology.Basis

variable {X : Type u} [TopologicalSpace X]
  {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- Flasqueness discharges the existing complete Čech-to-derived criterion. -/
theorem isZero_Hobj_of_isFlasque (hacyc : CechAcyclicInjectives T) (A : 𝒜)
    [TopCat.Presheaf.IsFlasque (X := TopCat.of X) (T.obj A).obj]
    (U : Opens X) (n : ℕ) (hn : 0 < n) :
    IsZero (Hobj T U n A) := by
  apply isZero_Hobj_of_le T hacyc A Set.univ Set.univ
    (fun _ _ ↦ ⟨trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩)
    (fun _ _ V hV ↦ ⟨V, trivial, hV, rfl, fun i ↦ ⟨i, le_rfl⟩⟩)
    (fun V _ q hq ↦ ?_) (injectiveResolution A) n U trivial n hn le_rfl
  exact Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (X := TopCat.of X) (T.obj A) V.carrier V.obj V.iSup_eq.symm q hq

end Cohomology.BasisCycles

namespace LinearCoefficients

variable (k : Type u) [CommRing k] (X : TopCat.{u})

/-- Forgetting the scalar action retains the original surjective restrictions. -/
theorem underlying_isFlasque_of_isFlasque (A : TopCat.Sheaf (ModuleCat.{u} k) X)
    [A.IsFlasque] : TopCat.Sheaf.IsFlasque (X := X) ((underlying k X).obj A) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (ModuleCat.epi_iff_surjective (A.obj.map i)).mp inferInstance

/-- The original coefficient-forgetting comparison, on any topological space and open. -/
def cohomologyForgetIso (A : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj
        (TwoOpenModules.Hobj k (𝟭 _) U n A) ≅
      Cohomology.Basis.Hobj (underlying k X) U n A :=
  BoundedBelowDerived.rightDerivedPostcomposeIso
    (TwoOpenModules.secFunctor k (𝟭 _) U)
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) A n

/-- Actual positive module-valued cohomology of a flasque sheaf vanishes on every open. -/
theorem isZero_cohomology_of_isFlasque (A : TopCat.Sheaf (ModuleCat.{u} k) X) [A.IsFlasque]
    (U : Opens X) (n : ℕ) (hn : 0 < n) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) U n A) := by
  let : TopCat.Sheaf.IsFlasque (X := X) ((underlying k X).obj A) :=
    underlying_isFlasque_of_isFlasque k X A
  have hAb : IsZero (Cohomology.Basis.Hobj (underlying k X) U n A) :=
    Cohomology.BasisCycles.isZero_Hobj_of_isFlasque (underlying k X)
      (cechAcyclicInjectives k X) A U n hn
  have hz := hAb.of_iso (cohomologyForgetIso k X A U n)
  rw [IsZero.iff_id_eq_zero]
  apply (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map_injective
  exact ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map_id _).trans (hz.eq_of_src _ _)

/-- The conclusion is about the existing global-sections functor itself. -/
theorem isZero_rightDerived_globalSections_of_isFlasque
    (A : TopCat.Sheaf (ModuleCat.{u} k) X) [A.IsFlasque] (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections k X).rightDerived n).obj A) := by
  exact isZero_cohomology_of_isFlasque k X A ⊤ n hn

end LinearCoefficients

end HodgeConjecture.SheafCohomology
