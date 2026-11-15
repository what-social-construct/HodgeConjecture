module

public import HodgeConjecture.Realization.Betti.SingularCoefficientCohomology

@[expose] public noncomputable section

/-!
# Coefficient inclusion and tensor complexification

The original map on rational cohomology is the pure-tensor restriction of
the existing complex-linear coefficient comparison. This identifies the two
maps from their original cochain-level constructions.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex
open scoped TensorProduct

namespace HodgeConjecture.SingularCoefficientChange

/-- The natural unit from a rational module to its complexification, with scalars restricted. -/
def tensorUnit : 𝟭 (ModuleCat.{0} ℚ) ⟶
    HomCoefficients.tensorFunctor ℚ ℂ ⋙ ModuleCat.restrictScalars (algebraMap ℚ ℂ) where
  app V := ModuleCat.ofHom
    (X := V)
    (Y := (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
      ((HomCoefficients.tensorFunctor ℚ ℂ).obj V))
    { toFun := fun v ↦ (1 ⊗ₜ[ℚ] v : ℂ ⊗[ℚ] V)
      map_add' := by
        intro v w
        exact TensorProduct.tmul_add 1 v w
      map_smul' := by
        intro r v
        change (1 ⊗ₜ[ℚ] (r • v) : ℂ ⊗[ℚ] V) = (r : ℂ) • (1 ⊗ₜ[ℚ] v)
        simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp }
  naturality V W f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change 1 ⊗ₜ[ℚ] (f.hom v) = f.hom.baseChange ℂ (1 ⊗ₜ[ℚ] v)
    rw [LinearMap.baseChange_tmul]

variable (X : TopCat.{0})

/-- The degreewise pure-tensor unit as a map of the original cochain complexes. -/
def tensorUnitComplexMap : SingularCochains.complex X ⟶
    ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).obj
      (((HomCoefficients.tensorFunctor ℚ ℂ).mapHomologicalComplex (.up ℕ)).obj
        (SingularCochains.complex X)) :=
  (tensorUnit.mapHomologicalComplex (.up ℕ)).app (SingularCochains.complex X)

/-- The original coefficient cochain map factors through its literal pure-tensor unit. -/
@[reassoc]
theorem coefficientMap_factor : coefficientMap X =
    tensorUnitComplexMap X ≫
      ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
        (cochainComparison X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact coefficientMap_eq_one_tmul X n φ

end HodgeConjecture.SingularCoefficientChange
