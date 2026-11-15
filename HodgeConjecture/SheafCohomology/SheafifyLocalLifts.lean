module

public import HodgeConjecture.SheafCohomology.SheafifyKernel
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

/-!
# Local representatives under the existing sheafification unit

The original stalk isomorphism supplies actual local lifts of sheaf
sections and detects equality of germs of original presheaf sections.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SheafCohomology

open CategoryTheory TopologicalSpace Opposite

universe u

variable {k : Type u} [CommRing k] {X : TopCat.{u}}

/-- Every sheafified section is represented on an actual smaller open. -/
theorem toSheafify_exists_local_lift (P : TopCat.Presheaf (ModuleCat.{u} k) X)
    (U : Opens X) (s : (sheafify (Opens.grothendieckTopology X) P).obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ ∃ t : P.obj (op V),
      (toSheafify (Opens.grothendieckTopology X) P).app (op V) t =
        (sheafify (Opens.grothendieckTopology X) P).map (homOfLE hVU).op s := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      (toSheafify (Opens.grothendieckTopology X) P) := by
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
    intro y
    exact (ModuleCat.epi_iff_surjective ((LocalExactness.sheafifyStalkIso (k := k) y).app P).hom).mp
      inferInstance
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hlocal U s x hx
  exact ⟨V, hVU, hxV, t, ht⟩

/-- Equality after applying the unit on stalks is actual equality on a smaller open. -/
theorem toSheafify_germ_eq_iff (P : TopCat.Presheaf (ModuleCat.{u} k) X)
    (U : Opens X) (s t : P.obj (op U)) (x : X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) P) U x hx
        ((toSheafify (Opens.grothendieckTopology X) P).app (op U) s) =
      TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) P) U x hx
        ((toSheafify (Opens.grothendieckTopology X) P).app (op U) t) ↔
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        P.map (homOfLE hVU).op s = P.map (homOfLE hVU).op t := by
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  constructor
  · intro h
    have hg : TopCat.Presheaf.germ P U x hx s = TopCat.Presheaf.germ P U x hx t := by
      apply (ModuleCat.mono_iff_injective
        ((LocalExactness.sheafifyStalkIso (k := k) x).app P).hom).mp inferInstance
      exact h
    obtain ⟨V, hxV, iU, iU', hV⟩ := TopCat.Presheaf.germ_eq P x hx hx s t hg
    refine ⟨V, leOfHom iU, hxV, ?_⟩
    simpa only [Subsingleton.elim iU' iU,
      show homOfLE (leOfHom iU) = iU from Subsingleton.elim _ _] using hV
  · rintro ⟨V, hVU, hxV, hV⟩
    have hg : TopCat.Presheaf.germ P U x hx s = TopCat.Presheaf.germ P U x hx t := by
      rw [← TopCat.Presheaf.germ_res_apply P (homOfLE hVU) x hxV s,
        ← TopCat.Presheaf.germ_res_apply P (homOfLE hVU) x hxV t, hV]
    exact congrArg
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map (toSheafify _ P)).hom hg

end HodgeConjecture.SheafCohomology
