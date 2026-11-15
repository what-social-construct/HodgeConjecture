module

public import HodgeConjecture.SheafCohomology.LinearCoefficients
public import HodgeConjecture.SheafCohomology.ConstantLift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.TensorProduct.Lift

@[expose] public noncomputable section

/-!
# Scalar restriction and the original constant sheaves

Native scalar restriction retains the original sections and restrictions.
Its exact sheaf functor and the native constant-sheaf compatibility give
coefficient maps without constructing another constant-sheaf model.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (X : TopCat.{u})

/-- Native postcomposition by scalar restriction, with the original sections and maps. -/
def sheaves : TopCat.Sheaf (ModuleCat.{u} S) X ⥤ TopCat.Sheaf (ModuleCat.{u} R) X :=
  sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars f)

instance : (sheaves f X).Additive where
  map_add := by intros; rfl

instance : PreservesLimits (sheaves f X) := by
  have : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u,u,u} f).isRightAdjoint
  have : (sheaves f X).IsRightAdjoint :=
    (Sheaf.adjunction (Opens.grothendieckTopology X)
      (ModuleCat.extendRestrictScalarsAdj.{u,u,u} f)).isRightAdjoint
  infer_instance

instance : (sheaves f X).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    have hlocal := (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} S) φ).2 hφ
    have : Sheaf.IsLocallySurjective ((sheaves f X).map φ) :=
      ⟨fun s ↦ hlocal.imageSieve_mem s⟩
    exact (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} R) ((sheaves f X).map φ)).1 this

instance : PreservesFiniteColimits (sheaves f X) := by
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (sheaves f X)
  exact (sheaves f X).preservesFiniteColimits_of_preservesHomology

/-- Scalar restriction retains the same surjective restriction functions. -/
theorem isFlasque (F : TopCat.Sheaf (ModuleCat.{u} S) X) [F.IsFlasque] :
    ((sheaves f X).obj F).IsFlasque where
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    exact (ModuleCat.epi_iff_surjective (F.obj.map i)).mp inferInstance

/-- The existing supported-section theorem makes restricted injective terms flasque. -/
theorem injective_isFlasque (I : TopCat.Sheaf (ModuleCat.{u} S) X) [Injective I] :
    ((sheaves f X).obj I).IsFlasque where
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    exact Cohomology.LinearRestriction.injective_linear_restriction_surjective I (leOfHom i.unop)

/-- The ring map as a linear map into the native restricted coefficient module. -/
def coefficientModuleMap : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S))
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a b ↦ by
        change f (a * b) = f a * f b
        exact f.map_mul a b }

@[simp]
theorem coefficientModuleMap_apply (a : R) : coefficientModuleMap f a = f a := rfl

/-- The native constant-sheaf functor commutes with scalar restriction. -/
def constantIso : (sheaves f X).obj (ConstantLift.sheaf S X) ≅
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) :=
  (constantCommuteCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars f)).app
    (ModuleCat.of S S)

/-- Coefficient inclusion between the original constant sheaves, using native functoriality. -/
def constantMap : ConstantLift.sheaf R X ⟶ (sheaves f X).obj (ConstantLift.sheaf S X) :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (coefficientModuleMap f) ≫ (constantIso f X).inv

variable [Algebra R S]

/-- Native tensor extension using the existing algebra structure on the coefficient ring. -/
def extendLinear {V : ModuleCat.{u} R} {W : ModuleCat.{u} S}
    (φ : V ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj W) :
    S ⊗[R] V →ₗ[S] W := by
  let : Module R W := Module.compHom W (algebraMap R S)
  let : IsScalarTower R S W := IsScalarTower.of_compHom R S W
  let ψ : V →ₗ[R] W := φ.hom
  exact ψ.liftBaseChange S

@[simp]
theorem extendLinear_tmul {V : ModuleCat.{u} R} {W : ModuleCat.{u} S}
    (φ : V ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj W) (s : S) (v : V) :
    extendLinear φ (s ⊗ₜ[R] v) = s • (show W from φ v) := by
  let : Module R W := Module.compHom W (algebraMap R S)
  let : IsScalarTower R S W := IsScalarTower.of_compHom R S W
  let ψ : V →ₗ[R] W := φ.hom
  exact LinearMap.liftBaseChange_tmul S ψ s v

@[simp]
theorem extendLinear_one_tmul {V : ModuleCat.{u} R} {W : ModuleCat.{u} S}
    (φ : V ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj W) (v : V) :
    extendLinear φ (1 ⊗ₜ[R] v) = (show W from φ v) := by
  rw [extendLinear_tmul, one_smul]

end HodgeConjecture.SheafCohomology.ScalarRestriction
