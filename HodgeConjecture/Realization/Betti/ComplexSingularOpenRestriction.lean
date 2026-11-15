module

public import HodgeConjecture.Realization.Betti.ComplexSingularOpenExtension
public import HodgeConjecture.Realization.Betti.ComplexSingularGlobalSections
public import HodgeConjecture.SheafCohomology.SheafifyOpen
public import Mathlib.Topology.Sheaves.Flasque

@[expose] public noncomputable section

/-!
# Open restrictions of the original complex singular cochain sheaf

The original complex-valued cochains on an open subspace identify with the
restricted presheaf. Global unit surjectivity and actual zero extension
give section lifts, hence flasqueness of the same sheaf terms under the
stated topology hypotheses.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

/-- The original subopen and its ambient image have the same complex cochains. -/
def openPresheafIso (U : Opens X) (n : ℕ) :
    restrictPresheaf (presheaf X n) U ≅ presheaf ((Opens.toTopCat X).obj U) n :=
  NatIso.ofComponents (fun V ↦
    (eval _ _ n).mapIso (functor.mapIso
      (TopCat.isoOfHomeo (U.isOpenEmbedding.isEmbedding.homeomorphImage V.unop.carrier)).op)) (by
    intro V W i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (complexCoordinates _ n).injective
    funext σ
    let jV := (TopCat.isoOfHomeo
      (U.isOpenEmbedding.isEmbedding.homeomorphImage V.unop.carrier) :
      (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V.unop ≅
        (Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj V.unop)).hom
    let jW := (TopCat.isoOfHomeo
      (U.isOpenEmbedding.isEmbedding.homeomorphImage W.unop.carrier) :
      (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj W.unop ≅
        (Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj W.unop)).hom
    let g := (Opens.toTopCat X).map (U.isOpenEmbedding.functor.map i.unop)
    let h := (Opens.toTopCat ((Opens.toTopCat X).obj U)).map i.unop
    change (complexCochains ((Opens.toTopCat X).obj
      (U.isOpenEmbedding.functor.obj V.unop))).X n at φ
    change complexCoordinates _ n ((pullback jW).f n ((pullback g).f n φ)) σ =
      complexCoordinates _ n ((pullback h).f n ((pullback jV).f n φ)) σ
    rw [pullback_coordinates, pullback_coordinates, pullback_coordinates, pullback_coordinates]
    rfl)

/-- Native sheafification of the complex cochain presheaf is onto on a paracompact Hausdorff open. -/
theorem toSheafify_open_surjective (U : Opens X) [ParacompactSpace U] [T2Space U]
    (n : ℕ) :
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

/-- Every complex sheaf section on such an open comes from an original ambient cochain. -/
theorem exists_global_cochain_open_lift (U : Opens X) [ParacompactSpace U] [T2Space U]
    (n : ℕ) (s : (cochainSheaf X n).obj.obj (op U)) :
    ∃ φ : (complexCochains X).X n,
      (cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((globalCochainsToSheaf X).f n φ) = s := by
  obtain ⟨φ, hφ⟩ := toSheafify_open_surjective X U n s
  refine ⟨openExtension X U n φ, ?_⟩
  rw [globalCochainsToSheaf_restrict, pullback_openExtension]
  exact hφ

/-- Only the smaller open requires paracompact Hausdorff topology. -/
theorem cochainSheaf_restriction_surjective {V U : Opens X} (hVU : V ≤ U)
    [ParacompactSpace V] [T2Space V] (n : ℕ) :
    Function.Surjective ((cochainSheaf X n).obj.map (homOfLE hVU).op) := by
  intro s
  obtain ⟨φ, hφ⟩ := exists_global_cochain_open_lift X V n s
  refine ⟨(cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
    ((globalCochainsToSheaf X).f n φ), ?_⟩
  rw [← Functor.map_comp_apply]
  exact hφ

/-- Native flasqueness of the original complex coefficient sheaf. -/
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

end HodgeConjecture.SingularCoefficientChange
