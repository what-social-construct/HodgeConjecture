module

public import HodgeConjecture.Realization.Betti.SingularSheafGlobalSections
public import HodgeConjecture.SheafCohomology.SheafifyOpen
public import Mathlib.Topology.Sheaves.Flasque

@[expose] public section

/-!
# Restricting the original singular cochain sheaves to open subspaces

The existing cochains on an open subspace identify with the existing
restricted presheaf through the native image homeomorphism. Native
sheafification compatibility preserves the original units.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

variable (X : TopCat.{0})

/-- The original subopen and its original ambient image have the same native cochains. -/
def openPresheafIso (U : Opens X) (n : ℕ) :
    restrictPresheaf (presheaf X n) U ≅ presheaf ((Opens.toTopCat X).obj U) n :=
  NatIso.ofComponents (fun V ↦
    (eval _ _ n).mapIso (functor.mapIso
      (TopCat.isoOfHomeo (U.isOpenEmbedding.isEmbedding.homeomorphImage V.unop.carrier)).op)) (by
    intro V W i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    funext σ
    rfl)

/-- The actual native unit is surjective on a paracompact Hausdorff open subspace. -/
theorem toSheafify_open_surjective (U : Opens X) [ParacompactSpace U] [T2Space U] (n : ℕ) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op U)) := by
  let : ParacompactSpace ((Opens.toTopCat X).obj U) := ‹ParacompactSpace U›
  let : T2Space ((Opens.toTopCat X).obj U) := ‹T2Space U›
  have h : Function.Surjective
      ((toSheafify (Opens.grothendieckTopology U)
        (presheaf ((Opens.toTopCat X).obj U) n)).app (op ⊤)) := by
    intro s
    obtain ⟨φ, hφ⟩ := globalCochainsToSheaf_surjective ((Opens.toTopCat X).obj U) n s
    exact ⟨(pullback (Opens.inclusion' (⊤ : Opens ((Opens.toTopCat X).obj U)))).f n φ, hφ⟩
  apply SheafCohomology.toSheafify_app_surjective_of_restrict (presheaf X n) U
  exact SheafCohomology.toSheafify_app_surjective_of_iso (openPresheafIso X U n).symm ⊤ h

/-- Every sheafified section on such an open is represented by an original global cochain. -/
theorem exists_global_cochain_open_lift (U : Opens X) [ParacompactSpace U] [T2Space U]
    (n : ℕ) (s : (cochainSheaf X n).obj.obj (op U)) :
    ∃ φ : Cochain X n,
      (cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((globalCochainsToSheaf X).f n φ) = s := by
  obtain ⟨φ, hφ⟩ := toSheafify_open_surjective X U n s
  refine ⟨openExtension X U n φ, ?_⟩
  rw [globalCochainsToSheaf_restrict, pullback_openExtension]
  exact hφ

/-- Only the smaller open needs to be paracompact Hausdorff. -/
theorem cochainSheaf_restriction_surjective {V U : Opens X} (hVU : V ≤ U)
    [ParacompactSpace V] [T2Space V] (n : ℕ) :
    Function.Surjective ((cochainSheaf X n).obj.map (homOfLE hVU).op) := by
  intro s
  obtain ⟨φ, hφ⟩ := exists_global_cochain_open_lift X V n s
  refine ⟨(cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
    ((globalCochainsToSheaf X).f n φ), ?_⟩
  rw [← Functor.map_comp_apply]
  exact hφ

/-- Native flasqueness of the existing module-valued sheaf, without a replacement sheaf. -/
theorem cochainSheaf_isFlasque [T2Space X]
    (hpara : ∀ U : Opens X, ParacompactSpace U) (n : ℕ) :
    (cochainSheaf X n).IsFlasque where
  epi {U V} i := by
    let : ParacompactSpace V.unop := hpara V.unop
    exact (ModuleCat.epi_iff_surjective _).mpr
      (cochainSheaf_restriction_surjective X (leOfHom i.unop) n)

/-- Locally compact second-countable Hausdorff spaces satisfy the open-subspace hypotheses. -/
theorem cochainSheaf_isFlasque_of_locallyCompact_secondCountable
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (n : ℕ) :
    (cochainSheaf X n).IsFlasque := by
  apply cochainSheaf_isFlasque X (fun U ↦ ?_) n
  let : LocallyCompactSpace U := U.isOpenEmbedding.locallyCompactSpace
  infer_instance

end HodgeConjecture.SingularCochains
