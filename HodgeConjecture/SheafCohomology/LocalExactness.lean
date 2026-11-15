module

public import HodgeConjecture.SheafCohomology.LinearSheaves
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Sheafify

@[expose] public section

/-!
# Exactness of fixed-ring sheaves from actual local lifts

Adapted from `TopCat.Sheaf.exact_of_exists_local_preimage` in Axiom Weil,
revision `27cdb2049be62ee2911429b47f54774078450e32`,
`Weil/Geometry/Manifold/Sheaf/Holomorphic.lean` (Apache-2.0).
This version works directly with the existing fixed-ring module sheaves.
See `third_party/axiom-weil/LICENSE`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology.LocalExactness

universe u

variable {k : Type u} [CommRing k] {X : TopCat.{u}}

/-- Local lifts in presheaves prove exactness on the original stalks. -/
theorem stalk_exact_of_exists_local_preimage
    (S : ShortComplex (TopCat.Presheaf (ModuleCat.{u} k) X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj (op U)), S.g.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : S.X₁.obj (op V), S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s)
    (x : X) : (S.map (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂ y
  have h0 : TopCat.Presheaf.germ S.X₃ U x hxU (S.g.app (op U) s) =
      TopCat.Presheaf.germ S.X₃ U x hxU 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU S.g s).symm.trans hy
  obtain ⟨W, hxW, iU, iU', hW⟩ := TopCat.Presheaf.germ_eq S.X₃ x hxU hxU _ _ h0
  have hgW : S.g.app (op W) (S.X₂.map iU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.naturality, ConcreteCategory.comp_apply, hW,
      map_zero]
  obtain ⟨V, hVW, hxV, t, ht⟩ := h W _ hgW x hxW
  refine ⟨TopCat.Presheaf.germ S.X₁ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor _ x).map S.f _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply]

/-- Local section lifts prove exactness of the already instantiated sheaves. -/
theorem exact_of_exists_local_preimage (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} k) X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : S.X₁.obj.obj (op V), S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE hVU).op s) :
    S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := ModuleCat.{u} k) (X := X) S).mpr
  exact stalk_exact_of_exists_local_preimage (S.map (TopCat.Sheaf.forget _ _)) h

/-- Sheafification leaves the stalk functor unchanged. -/
def sheafifyStalkIso (x : X) :
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x ≅
      sheafification k X ⋙
        TopCat.Sheaf.forget (ModuleCat.{u} k) X ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x :=
  NatIso.ofComponents (fun F ↦ by
    letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u} k) F
    exact asIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map (toSheafify _ F)))
    (fun {F G} f ↦ by
      change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map f ≫
          (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map (toSheafify _ G) =
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map (toSheafify _ F) ≫
          (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map
            (sheafifyMap (Opens.grothendieckTopology X) f)
      rw [← Functor.map_comp, ← Functor.map_comp, toSheafify_naturality])

/-- Presheaf local lifts prove exactness after native sheafification. -/
theorem sheafify_exact_of_exists_local_preimage
    (S : ShortComplex (TopCat.Presheaf (ModuleCat.{u} k) X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj (op U)), S.g.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : S.X₁.obj (op V), S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s) :
    (S.map (sheafification k X)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := ModuleCat.{u} k) (X := X) _).mpr
  intro x
  exact ShortComplex.exact_of_iso (S.mapNatIso (sheafifyStalkIso x))
    (stalk_exact_of_exists_local_preimage S h x)

end HodgeConjecture.SheafCohomology.LocalExactness
