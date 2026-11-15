module

public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

/-!
# Exact postcomposition and the original right derived functors

This is the existing comparison, moved unchanged from the de Rham
hypercohomology file. Its public namespace and name are retained.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.BoundedBelowDerived

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

/-- Exact coefficient forgetting commutes with ordinary right derived functors.
Both sides are computed on the same actual injective resolution of the source object. -/
def rightDerivedPostcomposeIso {E : Type*} [Category* E] [Abelian E]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology] (M : C) (n : ℕ) :
    T.obj ((F.rightDerived n).obj M) ≅ ((F ⋙ T).rightDerived n).obj M :=
  let I := injectiveResolution M
  T.mapIso (I.isoRightDerivedObj F n) ≪≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso T).symm ≪≫
    (I.isoRightDerivedObj (F ⋙ T) n).symm

end HodgeConjecture.BoundedBelowDerived
