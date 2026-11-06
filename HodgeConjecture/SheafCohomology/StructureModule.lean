module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

/-! The actual structure module is quasi-coherent by its global rank-one presentation. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace HodgeConjecture.SheafCohomology

noncomputable section

universe u

/-- The structure sheaf read as a module over itself, on the original scheme. -/
def structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- One global generator, with the zero relation map, presents the structure module. -/
def structureModulePresentation (X : Scheme.{u}) : (structureModule X).Presentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅ structureModule X :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  apply SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ⟶ _)
    e.hom zero_comp
  refine Cofork.IsColimit.mk _ (fun s => e.inv ≫ s.π) (fun s => ?_) (fun s m hm => ?_)
  · simp
  · apply (cancel_epi e.hom).mp
    simpa using hm

instance structureModule_isQuasicoherent (X : Scheme.{u}) :
    (structureModule X).IsQuasicoherent :=
  (structureModulePresentation X).isQuasicoherent

end

end HodgeConjecture.SheafCohomology
