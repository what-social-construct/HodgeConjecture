import HodgeConjecture.Cycles.FunctionFieldMap
import HodgeConjecture.Boundary.Normalization.FiniteAffineChart
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.RingHom.Finite

/-!
# The finite extension of actual function fields

The generic-stalk map of a dominant morphism commutes with the two scalar
routes from every nonempty base open. For a finite morphism, a nonempty
affine chart then gives a finite algebra of domains, whose fraction fields
are the actual function fields. Localizing that finite algebra proves that
the induced function-field extension is finite-dimensional.

No normality, étaleness, Noetherianity, or separately supplied field
extension is required.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (p : Y ⟶ X) [IsDominant p]

/-- Pullback of sections and the actual function-field map give compatible
scalar actions on the upstairs function field. -/
theorem functionFieldMapOfDominant_sectionScalarTower (U : X.Opens) [Nonempty U] :
    letI := SchemeCycles.nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    IsScalarTower Γ(X, U) X.functionField Y.functionField := by
  letI := SchemeCycles.nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg (fun f ↦ f.hom)
    (SchemeCycles.functionFieldMapOfDominant_germ p U)).symm

/-- A finite affine inverse-image algebra proves finiteness of the actual
function-field extension. -/
theorem functionFieldMapOfDominant_finiteDimensional_of_affine [IsFinite p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    FiniteDimensional X.functionField Y.functionField := by
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
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    finiteAffinePreimage_moduleFinite p U hU
  have hinj : Function.Injective (algebraMap Γ(X, U) Y.functionField) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) X.functionField Y.functionField]
    exact (algebraMap X.functionField Y.functionField).injective.comp
      (IsFractionRing.injective Γ(X, U) X.functionField)
  letI : FaithfulSMul Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective Γ(X, U) Γ(Y, p ⁻¹ᵁ U)).mpr (fun x y h ↦
      hinj (by simpa only
        [IsScalarTower.algebraMap_apply Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField] using
          congrArg (algebraMap Γ(Y, p ⁻¹ᵁ U) Y.functionField) h))
  exact Module.Finite.of_isLocalization Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Γ(X, U)⁰

/-- Every finite dominant morphism of integral schemes induces a finite
extension of its actual function fields. -/
theorem functionFieldMapOfDominant_finiteDimensional [IsFinite p] :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    FiniteDimensional X.functionField Y.functionField := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  exact functionFieldMapOfDominant_finiteDimensional_of_affine p U hU

/-- The actual section-ring square becomes a pushout after passage to the
two actual function fields. All scalar structures are the original pullbacks
and generic germs. -/
theorem functionFieldMapOfDominant_isPushout_of_affine [IsFinite p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
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
    Algebra.IsPushout Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField := by
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
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    finiteAffinePreimage_moduleFinite p U hU
  have hinj : Function.Injective (algebraMap Γ(X, U) Y.functionField) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) X.functionField Y.functionField]
    exact (algebraMap X.functionField Y.functionField).injective.comp
      (IsFractionRing.injective Γ(X, U) X.functionField)
  letI : FaithfulSMul Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective Γ(X, U) Γ(Y, p ⁻¹ᵁ U)).mpr (fun x y h ↦
      hinj (by simpa only
        [IsScalarTower.algebraMap_apply Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField] using
          congrArg (algebraMap Γ(Y, p ⁻¹ᵁ U) Y.functionField) h))
  infer_instance

end

end HodgeConjecture.CollisionFoundations
