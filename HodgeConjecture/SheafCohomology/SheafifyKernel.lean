module

public import HodgeConjecture.SheafCohomology.LocalExactness

@[expose] public section

/-!
# The actual sheafification unit kills exactly locally zero sections

The native unit has the same stalks as the original presheaf. Equality
of germs is witnessed on an actual smaller open set; equality of sheaf
sections is detected on those stalks. No separation or covering-finiteness
hypothesis is needed.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SheafCohomology

open CategoryTheory TopologicalSpace Opposite

universe u

variable {k : Type u} [CommRing k] {X : TopCat.{u}}

/-- This characterizes the kernel of the native unit on every original open. -/
theorem toSheafify_app_eq_zero_iff (P : TopCat.Presheaf (ModuleCat.{u} k) X)
    (U : Opens X) (s : P.obj (op U)) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op U) s = 0 ↔
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        P.map (homOfLE hVU).op s = 0 := by
  let η := toSheafify (Opens.grothendieckTopology X) P
  constructor
  · intro hs x hx
    let e := (LocalExactness.sheafifyStalkIso (k := k) x).app P
    have hg : TopCat.Presheaf.germ P U x hx s = 0 := by
      apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
      change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map η
          (TopCat.Presheaf.germ P U x hx s) =
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map η 0
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs, map_zero, map_zero]
    obtain ⟨V, hxV, iU, iU', hV⟩ := TopCat.Presheaf.germ_eq P x hx hx s 0 (by
      rw [map_zero]; exact hg)
    refine ⟨V, leOfHom iU, hxV, ?_⟩
    rw [show homOfLE (leOfHom iU) = iU from Subsingleton.elim _ _]
    simpa only [map_zero] using hV
  · intro hs
    let F := (sheafification k X).obj P
    apply TopCat.Presheaf.section_ext F U _ _
    intro x hx
    obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
    have hg : TopCat.Presheaf.germ P U x hx s = 0 := by
      rw [← TopCat.Presheaf.germ_res_apply P (homOfLE hVU) x hxV s, hV, map_zero]
    change TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) P) U x hx
        (η.app (op U) s) =
      TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) P) U x hx 0
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx η s, hg, map_zero, map_zero]

end HodgeConjecture.SheafCohomology
