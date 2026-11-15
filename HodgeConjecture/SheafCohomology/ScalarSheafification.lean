module

public import HodgeConjecture.SheafCohomology.ScalarRestriction

@[expose] public noncomputable section

/-!
# Native sheafification and scalar-restriction coefficient maps

The native compatibility isomorphism gives coefficient maps between
the original sheafifications. The unit formulas retain the actual maps,
including coefficient inclusion on the native constant sheaves.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (X : TopCat.{0})

def sheafifyMap {P : TopCat.Presheaf (ModuleCat.{0} R) X}
    {Q : TopCat.Presheaf (ModuleCat.{0} S) X} (φ : P ⟶ Q ⋙ ModuleCat.restrictScalars f) :
    (sheafification R X).obj P ⟶ (sheaves f X).obj ((sheafification S X).obj Q) :=
  (sheafification R X).map φ ≫
    (sheafComposeNatIso (Opens.grothendieckTopology X) (ModuleCat.restrictScalars f)
      (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).hom.app Q

@[reassoc]
theorem sheafifyMap_fac {P : TopCat.Presheaf (ModuleCat.{0} R) X}
    {Q : TopCat.Presheaf (ModuleCat.{0} S) X} (φ : P ⟶ Q ⋙ ModuleCat.restrictScalars f) :
    toSheafify (Opens.grothendieckTopology X) P ≫ (sheafifyMap f X φ).hom =
      φ ≫ whiskerRight (toSheafify (Opens.grothendieckTopology X) Q) (ModuleCat.restrictScalars f) := by
  change toSheafify _ P ≫ (CategoryTheory.sheafifyMap _ φ ≫
    (sheafifyComposeIso _ (ModuleCat.restrictScalars f) Q).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, sheafComposeIso_hom_fac]

def constantPresheafMap : ConstantLift.presheaf R X ⟶
    ConstantLift.presheaf S X ⋙ ModuleCat.restrictScalars f :=
  (Functor.const (Opens X)ᵒᵖ).map (coefficientModuleMap f) ≫
    (constComp (Opens X)ᵒᵖ (ModuleCat.of S S) (ModuleCat.restrictScalars f)).inv

@[simp]
theorem constantPresheafMap_apply (U : (Opens X)ᵒᵖ) (a : R) :
    (constantPresheafMap f X).app U a = f a := rfl

/-- The existing native constant-sheaf coefficient map retains its literal representatives. -/
@[reassoc]
theorem constantMap_fac :
    toSheafify (Opens.grothendieckTopology X) (ConstantLift.presheaf R X) ≫ (constantMap f X).hom =
      constantPresheafMap f X ≫
        whiskerRight (toSheafify (Opens.grothendieckTopology X) (ConstantLift.presheaf S X))
          (ModuleCat.restrictScalars f) := by
  let e := (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).mapIso (constantIso f X)
  change toSheafify _ _ ≫
    (CategoryTheory.sheafifyMap _ ((Functor.const (Opens X)ᵒᵖ).map (coefficientModuleMap f)) ≫ e.inv) = _
  rw [← Category.assoc]
  apply e.comp_inv_eq.mpr
  erw [← toSheafify_naturality]
  change _ = (constantPresheafMap f X ≫ _) ≫
    ((constantCommuteCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars f)).hom.app
      (ModuleCat.of S S)).hom
  rw [constantCommuteCompose_hom_app_hom]
  simp only [constantPresheafMap, Category.assoc]
  rw [sheafComposeIso_inv_fac_assoc, ← toSheafify_naturality]
  simp only [Iso.inv_hom_id_assoc]

/-- A literal coefficient square with constants remains that square after native sheafification. -/
theorem sheafifyMap_constant_naturality
    {P : TopCat.Presheaf (ModuleCat.{0} R) X} {Q : TopCat.Presheaf (ModuleCat.{0} S) X}
    (a : ConstantLift.presheaf R X ⟶ P) (b : ConstantLift.presheaf S X ⟶ Q)
    (φ : P ⟶ Q ⋙ ModuleCat.restrictScalars f)
    (h : a ≫ φ = constantPresheafMap f X ≫ whiskerRight b (ModuleCat.restrictScalars f)) :
    (sheafification R X).map a ≫ sheafifyMap f X φ =
      constantMap f X ≫ (sheaves f X).map ((sheafification S X).map b) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((sheaves f X).obj ((sheafification S X).obj Q)).property
  change toSheafify _ _ ≫ (CategoryTheory.sheafifyMap _ a ≫ (sheafifyMap f X φ).hom) =
    toSheafify _ _ ≫ ((constantMap f X).hom ≫
      whiskerRight (CategoryTheory.sheafifyMap _ b) (ModuleCat.restrictScalars f))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, sheafifyMap_fac]
  erw [constantMap_fac_assoc, ← whiskerRight_comp,
    ← toSheafify_naturality, whiskerRight_comp]
  simpa only [← Category.assoc] using congrArg
    (fun τ ↦ τ ≫ whiskerRight (toSheafify (Opens.grothendieckTopology X) Q)
      (ModuleCat.restrictScalars f)) h

end HodgeConjecture.SheafCohomology.ScalarRestriction
