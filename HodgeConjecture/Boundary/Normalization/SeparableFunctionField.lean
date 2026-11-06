module

public import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

/-!
# Separability of the actual generic extension

The actual generic-stalk embedding of a dominant affine formally unramified
morphism of integral schemes is formally unramified. Localize the upstairs
affine section ring, compose over the downstairs section ring, and use the
proved section scalar tower to pass to the downstairs function field.

For a finite morphism, the existing finite-dimensionality theorem supplies
essential finite type, so the same extension is separable. An étale morphism
supplies the formal-unramifiedness hypothesis automatically. No normality,
perfectness or characteristic-zero input is needed.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (p : Y ⟶ X) [IsDominant p] [FormallyUnramified p]

/-- On a whole affine inverse image, localization gives formal unramifiedness
of the actual function-field map. -/
theorem functionFieldMapOfDominant_formallyUnramified_of_affine [IsAffineHom p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField := by
  letI := SchemeCycles.nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : Algebra.FormallyUnramified Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := by
    change (p.app U).hom.FormallyUnramified
    simpa only [Scheme.Hom.appLE_eq_app] using
      p.formallyUnramified_appLE hU (hU.preimage p) le_rfl
  letI : Algebra.FormallyUnramified Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := Y.functionField) Γ(Y, p ⁻¹ᵁ U)⁰
  letI : Algebra.FormallyUnramified Γ(X, U) Y.functionField :=
    Algebra.FormallyUnramified.comp Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField
  exact Algebra.FormallyUnramified.of_restrictScalars Γ(X, U) X.functionField Y.functionField

/-- An affine formally unramified dominant morphism induces formal
unramifiedness on its actual function fields. -/
theorem functionFieldMapOfDominant_formallyUnramified [IsAffineHom p] :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  exact functionFieldMapOfDominant_formallyUnramified_of_affine p U hU

/-- A finite formally unramified dominant morphism gives a separable extension
under its actual generic-stalk embedding; in particular this applies to finite
étale morphisms. -/
theorem functionFieldMapOfDominant_isSeparable [IsFinite p] :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.IsSeparable X.functionField Y.functionField := by
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Y.functionField :=
    functionFieldMapOfDominant_finiteDimensional p
  letI : Algebra.FormallyUnramified X.functionField Y.functionField :=
    functionFieldMapOfDominant_formallyUnramified p
  exact Algebra.FormallyUnramified.isSeparable X.functionField Y.functionField

end

end HodgeConjecture.CollisionFoundations
