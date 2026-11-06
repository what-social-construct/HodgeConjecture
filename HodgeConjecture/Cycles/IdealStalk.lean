/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Sources: Divisors/FittingIdeals/Basic.lean and Divisors/RegularImmersion/FlatAtDivisor.lean.
Only ideal stalks, their affine computation, and closed-immersion kernels are retained.
Inverse-image and point-closure calculations also adapt ResolutionsAndBounds/IdealSheafStalk.lean
and Chow/RationalEquivalence/FlatPullbackPrincipalDivisor.lean.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.Cycles.PointSupport
public import HodgeConjecture.Cycles.IdealComap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace IdealSheafData

/-- The stalk of an ideal sheaf at a point, as an ideal of the local ring. -/
public noncomputable def stalk {X : Scheme.{u}} (I : X.IdealSheafData) (s : X) :
    Ideal (X.presheaf.stalk s) :=
  ⨆ (U : X.affineOpens) (hs : s ∈ U.1),
    (I.ideal U).map (X.presheaf.germ U.1 s hs).hom

end IdealSheafData

/-- The ideal induced in a local ring by an ideal sheaf is the image, under the germ map, of
the sections of the ideal sheaf on any affine open neighbourhood of the point. -/
theorem IdealSheafData.stalk_eq_map_germ
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hx : x ∈ U.1) :
    IdealSheafData.stalk I x =
      (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  rw [IdealSheafData.stalk]
  apply le_antisymm
  · refine iSup_le fun V ↦ iSup_le fun hxV ↦ ?_
    obtain ⟨f, g, hfg, hxf⟩ :=
      exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hx, hxV⟩
    let W := X.affineBasicOpen f
    have hWU : W ≤ U := X.basicOpen_le f
    have hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
    have hxW : x ∈ W.1 := hxf
    let rUWcat := X.presheaf.map
      (homOfLE (X := X.Opens) (show (W : X.Opens) ≤ (U : X.Opens) from hWU)).op
    let rVWcat := X.presheaf.map
      (homOfLE (X := X.Opens) (show (W : X.Opens) ≤ (V : X.Opens) from hWV)).op
    have hcompU : rUWcat ≫ X.presheaf.germ W.1 x hxW =
        X.presheaf.germ U.1 x hx :=
      X.presheaf.germ_res (homOfLE (X := X.Opens)
        (show (W : X.Opens) ≤ (U : X.Opens) from hWU)) x hxW
    have hcompV : rVWcat ≫ X.presheaf.germ W.1 x hxW =
        X.presheaf.germ V.1 x hxV :=
      X.presheaf.germ_res (homOfLE (X := X.Opens)
        (show (W : X.Opens) ≤ (V : X.Opens) from hWV)) x hxW
    exact le_of_eq <| calc
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom =
          ((I.ideal V).map rVWcat.hom).map (X.presheaf.germ W.1 x hxW).hom := by
            rw [Ideal.map_map]
            congr 1
            simpa only [CommRingCat.hom_comp] using
              (CommRingCat.hom_ext_iff.mp hcompV).symm
      _ = (I.ideal W).map (X.presheaf.germ W.1 x hxW).hom := by
            rw [← I.map_ideal hWV]
            rfl
      _ = ((I.ideal U).map rUWcat.hom).map (X.presheaf.germ W.1 x hxW).hom := by
            rw [← I.map_ideal hWU]
            rfl
      _ = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
            rw [Ideal.map_map]
            congr 1
            simpa only [CommRingCat.hom_comp] using
              CommRingCat.hom_ext_iff.mp hcompU
  · exact le_iSup_of_le U (le_iSup_of_le hx le_rfl)

/-- **The kernel of the stalk map of a closed immersion, after localization.**  On affine charts
`U ⊆ Y` and `V ⊆ f⁻¹U` the stalk map of `f` at `x ∈ V` is the localization of
`Γ(Y, U) ⟶ Γ(X, V)` at the prime of `x`, so its kernel is the extension of the kernel of the
map on sections. -/
theorem stalkMap_ker_localized
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V)
    (hgsurj : Function.Surjective (f.appLE U V hVU).hom) :
    let p := hU.primeIdealOf ⟨f x, (show f x ∈ U from hVU hx)⟩
    let g := (f.appLE U V hVU).hom
    let e := (asIso (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx).hom.left)
      |>.commRingCatIsoToRingEquiv
    Ideal.map e.toRingHom (RingHom.ker (f.stalkMap x).hom) =
      Ideal.map (algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
  classical
  dsimp only
  have hfx : f x ∈ U := hVU hx
  let p := hU.primeIdealOf ⟨f x, hfx⟩
  let q := hV.primeIdealOf ⟨x, hx⟩
  let g := (f.appLE U V hVU).hom
  have hcomap : p.asIdeal = Ideal.comap g q.asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm
  let loc := Localization.localRingHom p.asIdeal q.asIdeal g hcomap
  let hArrow := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx
  let e₁ : Y.presheaf.stalk (f x) ≃+* Localization.AtPrime p.asIdeal :=
    (asIso hArrow.hom.left).commRingCatIsoToRingEquiv
  let e₂ : X.presheaf.stalk x ≃+* Localization.AtPrime q.asIdeal :=
    (asIso hArrow.hom.right).commRingCatIsoToRingEquiv
  have hcomm (a : Y.presheaf.stalk (f x)) :
      loc (e₁ a) = e₂ ((f.stalkMap x).hom a) := by
    have hcat := hArrow.hom.w
    change (asIso hArrow.hom.left).hom ≫ CommRingCat.ofHom loc =
      CommRingCat.ofHom (f.stalkMap x).hom ≫ (asIso hArrow.hom.right).hom at hcat
    have hfun := CommRingCat.hom_ext_iff.mp hcat
    have h := congrArg (fun φ : Y.presheaf.stalk (f x) →+* _ => φ a) hfun
    convert h using 1 <;> rfl
  have htransport :
      Ideal.map e₁.toRingHom (RingHom.ker (f.stalkMap x).hom) = RingHom.ker loc := by
    ext z
    rw [Ideal.mem_map_iff_of_surjective e₁.toRingHom e₁.surjective]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      show loc (e₁ a) = 0
      exact (hcomm a).trans ((congrArg e₂ ha).trans (map_zero e₂))
    · intro hz
      obtain ⟨a, rfl⟩ := e₁.surjective z
      refine ⟨a, ?_, rfl⟩
      apply e₂.injective
      rw [RingHom.mem_ker] at hz
      exact (hcomm a).symm.trans (hz.trans (map_zero e₂).symm)
  have hT : Submonoid.map g p.asIdeal.primeCompl = q.asIdeal.primeCompl := by
    simpa only [hcomap] using Ideal.map_primeCompl_comap_of_surjective g hgsurj q.asIdeal
  have hkerLoc : RingHom.ker loc =
      Ideal.map (algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal))
        (RingHom.ker g) := by
    simpa [loc, Localization.localRingHom] using
      (IsLocalization.ker_map (Localization.AtPrime q.asIdeal) g hT)
  rw [htransport, hkerLoc]

/-- **The stalk of the ideal sheaf of a closed immersion is the kernel of its stalk map.** -/
theorem stalk_ker_eq_of_affine_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U) :
    IdealSheafData.stalk f.ker (f x) =
      RingHom.ker (f.stalkMap x).hom := by
  classical
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  have hxV : x ∈ V := by simpa [V] using hx
  let hVU : V ≤ f ⁻¹ᵁ U := le_rfl
  let g := (f.appLE U V hVU).hom
  have hgsurj : Function.Surjective g := by
    simpa [g, V, hVU, Scheme.Hom.appLE] using f.app_surjective U hU
  have hcomap : (hU.primeIdealOf ⟨f x, hx⟩).asIdeal =
      Ideal.comap g (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm
  let p := hU.primeIdealOf ⟨f x, hx⟩
  let _ : Algebra Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    Y.presheaf.algebra_section_stalk ⟨f x, hx⟩
  have _ : IsLocalization p.asIdeal.primeCompl (Y.presheaf.stalk (f x)) :=
    hU.isLocalization_stalk ⟨f x, hx⟩
  let hArrow := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV
  let e₁ : Y.presheaf.stalk (f x) ≃+* Localization.AtPrime p.asIdeal :=
    (asIso hArrow.hom.left).commRingCatIsoToRingEquiv
  have hring : e₁.toRingHom.comp (Y.presheaf.germ U (f x) hx).hom =
      algebraMap Γ(Y, U) (Localization.AtPrime p.asIdeal) := by
    ext s
    show (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).toRingEquiv
        ((Y.presheaf.germ U (f x) hx).hom s) = _
    show (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).toRingEquiv
        (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x)) s) = _
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) (Localization.AtPrime p.asIdeal)).commutes s
  have happ : g = (f.app U).hom := by
    simp [g, V, Scheme.Hom.appLE]
  have hmapIdeal :
      Ideal.map e₁.toRingHom (IdealSheafData.stalk f.ker (f x)) =
        Ideal.map (algebraMap Γ(Y, U)
          (Localization.AtPrime (hU.primeIdealOf ⟨f x, hx⟩).asIdeal))
          (RingHom.ker g) := by
    rw [IdealSheafData.stalk_eq_map_germ f.ker (f x) ⟨U, hU⟩ hx, Scheme.Hom.ker_apply, ← happ,
      Ideal.map_map]
    exact congrArg (fun φ : Γ(Y, U) →+* _ =>
      Ideal.map φ (RingHom.ker g)) hring
  have hmapKer' :
      Ideal.map e₁.toRingHom (RingHom.ker (f.stalkMap x).hom) =
        Ideal.map (algebraMap Γ(Y, U)
          (Localization.AtPrime (hU.primeIdealOf ⟨f x, hx⟩).asIdeal))
          (RingHom.ker g) := by
    simpa [g, hcomap] using stalkMap_ker_localized f x U hU V hV hVU hxV hgsurj
  simpa only [Ideal.comap_map_of_bijective e₁.toRingHom e₁.bijective] using
    congrArg (Ideal.comap e₁.toRingHom) (hmapIdeal.trans hmapKer'.symm)

/-- The closed immersion of the actual subscheme has its defining stalk ideal as kernel. -/
theorem IdealSheafData.ker_stalkMap_subschemeι_eq_stalk {X : Scheme.{u}}
    (I : X.IdealSheafData) (z : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap z).hom = stalk I (I.subschemeι.base z) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (I.subschemeι.base z)) isOpen_univ
  rw [← stalk_ker_eq_of_affine_target I.subschemeι z U hU hzU, I.ker_subschemeι]

/-- Inverse image of the original ideal sheaf extends its stalk ideal along the original
local-ring map. -/
theorem IdealSheafData.stalk_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) (x : X) :
    stalk (I.comap f) x = Ideal.map (f.stalkMap x).hom (stalk I (f.base x)) := by
  obtain ⟨V, hV, hfx, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f.base x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hfx)
  have happ : f.appLE V U hUV ≫ X.presheaf.germ U x hxU =
      Y.presheaf.germ V (f.base x) hfx ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc,
      X.presheaf.germ_res (homOfLE hUV) x hxU]
  rw [stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    stalk_eq_map_germ I _ ⟨V, hV⟩ hfx,
    HodgeConjecture.SchemeCycles.IdealComap.ideal_comap_appLE I f ⟨V, hV⟩ ⟨U, hU⟩ hUV,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, happ]

end AlgebraicGeometry

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry

/-- On an affine chart the existing reduced point closure has the point's original prime. -/
theorem pointSupport_ideal {X : Scheme.{u}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    (pointSupport X x).val.ideal U = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  letI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hsingle : hU.fromSpec.base ⁻¹' ({x} : Set X) = {hU.primeIdealOf ⟨x, hx⟩} := by
    ext z
    exact ⟨fun hz ↦ hU.fromSpec.isOpenEmbedding.injective
        (by rw [hU.fromSpec_primeIdealOf]; exact hz),
      by rintro rfl; exact hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
  have hcl : hU.fromSpec.base ⁻¹' closure ({x} : Set X) =
      closure {hU.primeIdealOf ⟨x, hx⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous, hsingle]
  rw [pointSupport_val, Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (congrArg PrimeSpectrum.vanishingIdeal hcl).trans
    (by rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton])

/-- At its generic point, the existing reduced point closure cuts out the maximal ideal. -/
theorem pointSupport_stalk_self {X : Scheme.{u}} (x : X) :
    IdealSheafData.stalk (pointSupport X x).val x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, pointSupport_ideal x ⟨U, hU⟩ hxU]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk x)

end HodgeConjecture.SchemeCycles
