module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

@[expose] public noncomputable section

/-!
# Fixed-ring sheaf infrastructure

Named aliases to Mathlib's actual sheafification and abelian-category
instances keep repeated scheme and derived-section constructions from
repeating their generic instance search.
-/

open CategoryTheory TopologicalSpace

universe u

namespace HodgeConjecture.SheafCohomology

variable (k : Type u) [CommRing k] (X : TopCat.{u})

instance linearHasSheafify : HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} k) :=
  inferInstance

instance linearSheafPreadditive : Preadditive (TopCat.Sheaf (ModuleCat.{u} k) X) :=
  inferInstanceAs (Preadditive
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)))

instance linearSheafAbelian : Abelian (TopCat.Sheaf (ModuleCat.{u} k) X) :=
  inferInstanceAs (Abelian
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)))

instance linearSheafGrothendieck : IsGrothendieckAbelian.{u}
    (TopCat.Sheaf (ModuleCat.{u} k) X) :=
  inferInstanceAs (IsGrothendieckAbelian.{u}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)))

instance linearSheafEnoughInjectives : EnoughInjectives (TopCat.Sheaf (ModuleCat.{u} k) X) :=
  inferInstance

end HodgeConjecture.SheafCohomology
