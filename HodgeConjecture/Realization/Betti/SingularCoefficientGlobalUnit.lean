module

public import HodgeConjecture.Realization.Betti.SingularCoefficientSheafMap

@[expose] public noncomputable section

/-!
# Coefficient inclusion and the original global singular-cochain unit

The original coefficient map ℚ → ℂ commutes with the original maps from
global singular cochains to termwise sections of the native sheafifications.
This is a strict cochain-level comparison, before derived sections or any
cohomology isomorphism is invoked.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor TopologicalSpace Opposite HomologicalComplex

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

/-- The original global sheafification unit respects literal coefficient inclusion. -/
@[reassoc]
theorem globalUnit_coefficient (n : ℕ) :
    (SingularCochains.globalCochainsToSheaf X).f n ≫
        (SheafHypercohomology.globalSections ℚ X).map ((sheafCoefficientMap X).f n) =
      (coefficientMap X).f n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map ((globalCochainsToSheaf X).f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have hfac := congrArg (fun τ ↦ τ.app (op (⊤ : Opens X)))
    (SheafCohomology.ScalarRestriction.sheafifyMap_fac (algebraMap ℚ ℂ) X
      (presheafCoefficientMap X n))
  have hnat := coefficientMap_naturality X (Opens.inclusion' (⊤ : Opens X)) n
  have hfacφ := congrArg
    (fun f ↦ f ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) hfac
  have hnatφ := congrArg (fun f ↦ f φ) hnat
  change ((sheafCoefficientMap X).f n).hom.app (op (⊤ : Opens X))
      ((SingularCochains.globalCochainsToSheaf X).f n φ) =
    (globalCochainsToSheaf X).f n ((coefficientMap X).f n φ)
  change ((sheafCoefficientMap X).f n).hom.app (op (⊤ : Opens X))
      ((toSheafify (Opens.grothendieckTopology X) (SingularCochains.presheaf X n)).app
        (op ⊤) ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) = _
  change
    (SheafCohomology.ScalarRestriction.sheafifyMap (algebraMap ℚ ℂ) X
        (presheafCoefficientMap X n)).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology X) (SingularCochains.presheaf X n)).app
        (op ⊤) ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) =
    (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op ⊤)
      ((pullback (Opens.inclusion' (⊤ : Opens X))).f n ((coefficientMap X).f n φ))
  change
    (SheafCohomology.ScalarRestriction.sheafifyMap (algebraMap ℚ ℂ) X
        (presheafCoefficientMap X n)).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology X) (SingularCochains.presheaf X n)).app
        (op ⊤) ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) =
    (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op ⊤)
      ((coefficientMap ((Opens.toTopCat X).obj ⊤)).f n
        ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) at hfacφ
  change (coefficientMap ((Opens.toTopCat X).obj ⊤)).f n
      ((SingularCochains.pullback (Opens.inclusion' (⊤ : Opens X))).f n φ) =
    (pullback (Opens.inclusion' (⊤ : Opens X))).f n ((coefficientMap X).f n φ) at hnatφ
  exact hfacφ.trans (congrArg
    (fun z ↦ (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op ⊤) z)
    hnatφ)

/-- The same strict square on the original global cochain complexes. -/
@[reassoc]
theorem globalUnit_coefficient_complex :
    SingularCochains.globalCochainsToSheaf X ≫
        ((SheafHypercohomology.globalSections ℚ X).mapHomologicalComplex (.up ℕ)).map
          (sheafCoefficientMap X) =
      coefficientMap X ≫
        ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
          (globalCochainsToSheaf X) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact globalUnit_coefficient X n

/-- The cohomology square is induced by those same original cochain maps. -/
@[reassoc]
theorem globalUnit_coefficient_homology (n : ℕ) :
    homologyMap (SingularCochains.globalCochainsToSheaf X) n ≫
        homologyMap
          (((SheafHypercohomology.globalSections ℚ X).mapHomologicalComplex (.up ℕ)).map
            (sheafCoefficientMap X)) n =
      homologyMap (coefficientMap X) n ≫
        homologyMap
          (((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
            (globalCochainsToSheaf X)) n := by
  have h := congrArg (fun f ↦ homologyMap f n) (globalUnit_coefficient_complex X)
  rw [homologyMap_comp] at h
  refine h.trans ?_
  exact homologyMap_comp
    (φ := coefficientMap X)
    (ψ := ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).map
      (globalCochainsToSheaf X))
    (i := n)

end HodgeConjecture.SingularCoefficientChange
