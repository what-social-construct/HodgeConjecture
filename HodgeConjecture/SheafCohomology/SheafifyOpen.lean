module

public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.SheafCohomology.OpenImmersionRestriction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# The existing sheafification commutes with restriction to an open

The open-embedding functor lifts genuine covering sieves. The native
sheafification compatibility isomorphism then compares the existing
restricted presheaf and restricted sheaf, including their actual units.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SheafCohomology

open CategoryTheory TopologicalSpace Opposite

universe u

/-- Covers lift along the original open-embedding functor on opens. -/
theorem openEmbedding_isCocontinuous {Y X : TopCat.{u}} {f : Y ⟶ X}
    (hf : Topology.IsOpenEmbedding f) :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) where
  cover_lift {U} {S} hS y hy := by
    obtain ⟨V, i, hi, hyV⟩ := hS (f y) ⟨y, hy, rfl⟩
    let W := (Opens.map f).obj V
    have hWU : W ≤ U := by
      intro z hz
      obtain ⟨w, hw, he⟩ := i.le hz
      exact (hf.injective he) ▸ hw
    have e : hf.functor.obj W = V := by
      apply Opens.ext
      exact Set.image_preimage_eq_of_subset fun z hz ↦ by
        obtain ⟨w, hw, he⟩ := i.le hz
        exact ⟨w, he⟩
    refine ⟨W, homOfLE hWU, ?_, hyV⟩
    change S (hf.functor.map (homOfLE hWU))
    rw [show hf.functor.map (homOfLE hWU) = eqToHom e ≫ i from Subsingleton.elim _ _]
    exact S.downward_closed hi _

variable {k : Type u} [CommRing k] {X : TopCat.{u}}

/-- This is the native compatibility isomorphism, on the existing restriction objects. -/
def sheafifyOpenIso (P : TopCat.Presheaf (ModuleCat.{u} k) X) (U : Opens X) :
    (sheafification k ((Opens.toTopCat X).obj U)).obj (restrictPresheaf P U) ≅
      local_restrictSheaf ((sheafification k X).obj P) U := by
  let : U.isOpenEmbedding.functor.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  let : U.isOpenEmbedding.functor.IsCocontinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := openEmbedding_isCocontinuous U.isOpenEmbedding
  exact (U.isOpenEmbedding.functor.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u} k) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).app P

/-- The comparison intertwines the actual native units, on all original subopens. -/
theorem toSheafify_sheafifyOpenIso (P : TopCat.Presheaf (ModuleCat.{u} k) X) (U : Opens X) :
    toSheafify (Opens.grothendieckTopology U) (restrictPresheaf P U) ≫
        (sheafifyOpenIso P U).hom.hom =
      Functor.whiskerLeft U.isOpenEmbedding.functor.op (toSheafify (Opens.grothendieckTopology X) P) := by
  let : U.isOpenEmbedding.functor.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  let : U.isOpenEmbedding.functor.IsCocontinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := openEmbedding_isCocontinuous U.isOpenEmbedding
  exact U.isOpenEmbedding.functor.toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{u} k) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) P

/-- Unit surjectivity transfers through an isomorphism of the original presheaves. -/
theorem toSheafify_app_surjective_of_iso
    {P Q : TopCat.Presheaf (ModuleCat.{u} k) X} (e : P ≅ Q) (U : Opens X)
    (h : Function.Surjective ((toSheafify (Opens.grothendieckTopology X) P).app (op U))) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X) Q).app (op U)) := by
  let e' := (CategoryTheory.sheafification (Opens.grothendieckTopology X)
    (ModuleCat.{u} k)).mapIso e
  have : Epi ((toSheafify (Opens.grothendieckTopology X) P).app (op U)) :=
    (ModuleCat.epi_iff_surjective _).mpr h
  have : IsIso ((sheafifyMap (Opens.grothendieckTopology X) e.hom).app (op U)) := by
    change IsIso (e'.hom.app (op U))
    infer_instance
  have he := congrArg (fun f ↦ f.app (op U))
    (toSheafify_naturality (Opens.grothendieckTopology X) e.hom)
  simp only [NatTrans.comp_app] at he
  have : Epi (e.hom.app (op U) ≫ (toSheafify (Opens.grothendieckTopology X) Q).app (op U)) := by
    rw [he]
    infer_instance
  have := epi_of_epi (e.hom.app (op U))
    ((toSheafify (Opens.grothendieckTopology X) Q).app (op U))
  exact (ModuleCat.epi_iff_surjective _).mp this

/-- A lift on the restricted presheaf gives a lift on the same ambient open. -/
theorem toSheafify_app_surjective_of_restrict
    (P : TopCat.Presheaf (ModuleCat.{u} k) X) (U : Opens X)
    (h : Function.Surjective
      ((toSheafify (Opens.grothendieckTopology U) (restrictPresheaf P U)).app (op ⊤))) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X) P).app (op U)) := by
  let e := (TopCat.Sheaf.forget (ModuleCat.{u} k) ((Opens.toTopCat X).obj U)).mapIso
    (sheafifyOpenIso P U)
  have : Epi ((toSheafify (Opens.grothendieckTopology U) (restrictPresheaf P U)).app (op ⊤)) :=
    (ModuleCat.epi_iff_surjective _).mpr h
  have he := congrArg (fun f ↦ f.app (op ⊤)) (toSheafify_sheafifyOpenIso P U)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at he
  have hh : Epi ((toSheafify (Opens.grothendieckTopology X) P).app
      (U.isOpenEmbedding.functor.op.obj (op ⊤))) := by
    rw [← he]
    change Epi (_ ≫ e.hom.app (op ⊤))
    infer_instance
  have ht : U.isOpenEmbedding.functor.op.obj (op ⊤) = op U :=
    congrArg op (Opens.isOpenEmbedding_obj_top U)
  have hU : Epi ((toSheafify (Opens.grothendieckTopology X) P).app (op U)) := ht ▸ hh
  exact (ModuleCat.epi_iff_surjective _).mp hU

end HodgeConjecture.SheafCohomology
