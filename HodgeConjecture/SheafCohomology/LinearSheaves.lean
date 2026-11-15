module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Additive
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

/-- Shared native fixed-ring sheafification, independent of a realization. -/
def sheafification : TopCat.Presheaf (ModuleCat.{u} k) X ⥤
    TopCat.Sheaf (ModuleCat.{u} k) X :=
  presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)

instance : (sheafification k X).Additive :=
  inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).Additive

/-- Apply that same sheafification to every term and differential. -/
def sheafifyComplex (K : CochainComplex (TopCat.Presheaf (ModuleCat.{u} k) X) ℕ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ :=
  ((sheafification k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The native unit, as a map of the original complexes. -/
def toSheafifyComplex (K : CochainComplex (TopCat.Presheaf (ModuleCat.{u} k) X) ℕ) : K ⟶
    ((TopCat.Sheaf.forget (ModuleCat.{u} k) X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (sheafifyComplex k X K) where
  f n := toSheafify (Opens.grothendieckTopology X) (K.X n)
  comm' i j _ := ((sheafificationAdjunction (Opens.grothendieckTopology X)
    (ModuleCat.{u} k)).unit.naturality (K.d i j)).symm

end HodgeConjecture.SheafCohomology

namespace HodgeConjecture.SheafHypercohomology

variable (k : Type u) [CommRing k] (X : TopCat.{u})

/-- The existing global-sections functor, shared by all realizations. -/
def globalSections : TopCat.Sheaf (ModuleCat.{u} k) X ⥤ ModuleCat.{u} k :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (Opposite.op ⊤)

instance : (globalSections k X).Additive where
  map_add := by intros; rfl

end HodgeConjecture.SheafHypercohomology
