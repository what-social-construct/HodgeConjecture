module

public import HodgeConjecture.SheafCohomology.ScalarSheafification

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (X : TopCat.{0})

def presheaves : TopCat.Presheaf (ModuleCat.{0} S) X ⥤ TopCat.Presheaf (ModuleCat.{0} R) X :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars f)

instance : (presheaves f X).Additive where
  map_add := by intros; rfl

/-- The native coefficient/sheafification isomorphism applied to the original complexes. -/
def sheafifyComplexMap
    {K : CochainComplex (TopCat.Presheaf (ModuleCat.{0} R) X) ℕ}
    {L : CochainComplex (TopCat.Presheaf (ModuleCat.{0} S) X) ℕ}
    (φ : K ⟶ ((presheaves f X).mapHomologicalComplex (.up ℕ)).obj L) :
    sheafifyComplex R X K ⟶ ((sheaves f X).mapHomologicalComplex (.up ℕ)).obj
      (sheafifyComplex S X L) :=
  ((sheafification R X).mapHomologicalComplex (.up ℕ)).map φ ≫
    ((sheafComposeNatIso (Opens.grothendieckTopology X) (ModuleCat.restrictScalars f)
      (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).hom.mapHomologicalComplex
        (.up ℕ)).app L

@[simp]
theorem sheafifyComplexMap_f
    {K : CochainComplex (TopCat.Presheaf (ModuleCat.{0} R) X) ℕ}
    {L : CochainComplex (TopCat.Presheaf (ModuleCat.{0} S) X) ℕ}
    (φ : K ⟶ ((presheaves f X).mapHomologicalComplex (.up ℕ)).obj L) (n : ℕ) :
    (sheafifyComplexMap f X φ).f n = sheafifyMap f X (φ.f n) := rfl

end HodgeConjecture.SheafCohomology.ScalarRestriction
