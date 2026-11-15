module

public import HodgeConjecture.Geometry.Holomorphic.FunctionAlgebra
public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.SheafCohomology.ConstantLift
public import Mathlib.Algebra.Homology.HomologicalComplex

@[expose] public section

/-!
# The holomorphic de Rham sheaf complex on a complex coordinate space

Every degree is the existing sheaf of complex-smooth maps into native
alternating coefficients, upgraded to fixed-complex-scalar modules.
The arrows are the constructed exterior derivatives on actual sections.
The constant augmentation is induced by constant zero-forms and actual
sheafification. General scheme analytification is a separate construction.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff
open HolomorphicForms

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The existing holomorphic section spaces with their actual restriction maps. -/
def formsPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of E) where
  obj U := ModuleCat.of ℂ (Sections U.unop n)
  map i := ModuleCat.ofHom (restrict (leOfHom i.unop) n)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaf property is inherited from Mathlib's complex smooth-function sheaf. -/
def formsSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of E) where
  obj := formsPresheaf E n
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat ℂ))]
    exact (smoothSheaf 𝓘(ℂ, E) 𝓘(ℂ, Coeff E n) E (Coeff E n)).property

/-- The native exterior differential as a morphism of actual sheaves. -/
def differential (n : ℕ) : formsSheaf E n ⟶ formsSheaf E (n + 1) :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (HolomorphicForms.differential U.unop n)
    naturality _ _ i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (restrict_differential (leOfHom i.unop) n f).symm }

theorem differential_comp (n : ℕ) : differential E n ≫ differential E (n + 1) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact ModuleCat.hom_ext (HolomorphicForms.differential_comp U.unop n)

/-- The actual all-degree holomorphic de Rham sheaf complex on E. -/
def complex : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of E)) ℕ :=
  CochainComplex.of (formsSheaf E) (differential E) (differential_comp E)

@[simp]
theorem complex_X (n : ℕ) : (complex E).X n = formsSheaf E n := rfl

@[simp]
theorem complex_d (n : ℕ) : (complex E).d n (n + 1) = differential E n :=
  by apply CochainComplex.of_d

/-- Sectionwise evaluation of the same differential, without replacing the sheaf complex. -/
def sectionComplex (U : Opens E) : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℂ (Sections U n))
    (fun n ↦ ModuleCat.ofHom (HolomorphicForms.differential U n))
    (fun n ↦ ModuleCat.hom_ext (HolomorphicForms.differential_comp U n))


/-- Constants on the constant presheaf, with literal constant restriction maps. -/
abbrev constantPresheaf : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of E) :=
  SheafCohomology.ConstantLift.presheaf ℂ (TopCat.of E)

def constantPresheafMap :
    constantPresheaf E ⟶ (formsSheaf E 0).obj where
  app U := ModuleCat.ofHom (constant U.unop)
  naturality _ _ _ := rfl

/-- The genuine constant sheaf with complex coefficients. -/
abbrev constantSheaf : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of E) :=
  SheafCohomology.ConstantLift.sheaf ℂ (TopCat.of E)

/-- The constant-sheaf augmentation, constructed by the actual sheafification universal property. -/
def augmentation : constantSheaf E ⟶ formsSheaf E 0 :=
  SheafCohomology.ConstantLift.lift (formsSheaf E 0) (constantPresheafMap E)

theorem toSheafify_augmentation :
    toSheafify _ _ ≫ (augmentation E).hom = constantPresheafMap E :=
  SheafCohomology.ConstantLift.toSheafify_lift (formsSheaf E 0) (constantPresheafMap E)

theorem augmentation_differential : augmentation E ≫ differential E 0 = 0 := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (formsSheaf E 1).property
  rw [ObjectProperty.FullSubcategory.comp_hom]
  rw [← Category.assoc, toSheafify_augmentation]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact differential_constant U.unop c

end HodgeConjecture.HolomorphicDeRham
