module

public import HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison

@[expose] public section

/-!
# The actual degree-two Hodge filtration of the original projective line

The filtration is the image of actual derived maps from the degree-filtered
scheme de Rham complex. The original sheaf terms vanish above degree one.
The actual degree-one inclusion is invertible on H² because H¹ and H² of
the regular-function term vanish. Consequently F¹ is all of H² and F² is
zero. The comparison with H¹(Ω¹) retains that original inclusion.

The computation works over any field and concerns this bounded degree.
It is not a general Hodge-to-de Rham spectral-sequence degeneration proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDeRham

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

attribute [local instance] HasDerivedCategory.standard

/-- The image of the actual degree-filtered de Rham inclusion on the original scheme H². -/
def hodgeFiltration (p : ℤ) : Submodule k (SchemeH2 k) :=
  SchemeDeRham.hodgeFiltration k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) 2 p

theorem hodgeFiltration_antitone : Antitone (hodgeFiltration k) :=
  SchemeDeRham.hodgeFiltration_antitone k _ _ 2

/-- The original F¹ inclusion induces an isomorphism, by the proved geometric vanishings. -/
theorem hodgeFiltrationOne_isIso :
    IsIso (SchemeDeRham.hodgeFiltrationMap k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) 2 1) :=
  HypercohomologyFiltration.filtration_one_map_isIso
    (SheafHypercohomology.globalSections k (projectiveLine k))
    (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)))
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn)
    (schemeZeroFormsH1_isZero k) (schemeZeroFormsH2_isZero k)

/-- The actual F¹ image is the whole original H². -/
@[simp]
theorem hodgeFiltration_one : hodgeFiltration k 1 = ⊤ := by
  change HypercohomologyFiltration.filtration
    (SheafHypercohomology.globalSections k (projectiveLine k))
    (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))) 2 1 = ⊤
  exact HypercohomologyFiltration.filtration_one_of_twoTerm _ _
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn)
    (schemeZeroFormsH1_isZero k) (schemeZeroFormsH2_isZero k)

/-- Nonpositive filtration indices retain the actual original complex. -/
theorem hodgeFiltration_eq_top_of_nonpos (p : ℤ) (hp : p ≤ 0) :
    hodgeFiltration k p = ⊤ :=
  SchemeDeRham.hodgeFiltration_eq_top_of_nonpos k _ _ 2 p hp

theorem hodgeFiltration_eq_top (p : ℤ) (hp : p ≤ 1) : hodgeFiltration k p = ⊤ := by
  by_cases h0 : p ≤ 0
  · exact hodgeFiltration_eq_top_of_nonpos k p h0
  · have hp1 : p = 1 := by omega
    subst p
    exact hodgeFiltration_one k

/-- Every higher filtration complex is actually zero because its original sheaf terms vanish. -/
theorem hodgeFiltration_eq_bot (p : ℤ) (hp : 2 ≤ p) : hodgeFiltration k p = ⊥ := by
  change HypercohomologyFiltration.filtration
    (SheafHypercohomology.globalSections k (projectiveLine k))
    (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)))
      2 p.toNat = ⊥
  exact HypercohomologyFiltration.filtration_eq_bot_of_twoTerm _ _
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn) 2 p.toNat (by omega)

@[simp]
theorem hodgeFiltration_zero : hodgeFiltration k 0 = ⊤ :=
  hodgeFiltration_eq_top k 0 (by decide)

@[simp]
theorem hodgeFiltration_two : hodgeFiltration k 2 = ⊥ :=
  hodgeFiltration_eq_bot k 2 le_rfl

/-- This formula is a consequence of the original derived maps, rather than the definition. -/
theorem hodgeFiltration_eq (p : ℤ) :
    hodgeFiltration k p = if p ≤ 1 then ⊤ else ⊥ := by
  split_ifs with hp
  · exact hodgeFiltration_eq_top k p hp
  · exact hodgeFiltration_eq_bot k p (by omega)

/-- The constructed Chern coordinate lies in the actual geometric F¹. -/
theorem chernCoordinate_mem_hodgeFiltration_one :
    schemeChernCoordinate k ∈ hodgeFiltration k 1 := by
  rw [hodgeFiltration_one]
  trivial

/-- Its nonzero leading filtration degree is exactly one. -/
theorem chernCoordinate_not_mem_hodgeFiltration_two :
    schemeChernCoordinate k ∉ hodgeFiltration k 2 := by
  rw [hodgeFiltration_two, Submodule.mem_bot]
  exact schemeChernCoordinate_ne_zero k

/-- The actual filtered inclusion retains the original comparison with H¹ of one-forms. -/
@[reassoc]
theorem hodgeFiltrationOne_comparison :
    SchemeDeRham.hodgeFiltrationMap k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) 2 1 ≫ (schemeH2IsoSheafH1 k).hom =
      (HypercohomologyFiltration.functor
        (SheafHypercohomology.globalSections k (projectiveLine k)) 2).map
          (DegreeFiltration.degreeOneIso
            (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)))
            (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn)).hom ≫
        (BoundedBelowDerived.degreeOneHypercohomologyIsoRightDerived
          (SheafHypercohomology.globalSections k (projectiveLine k)) (schemeFormsSheaf k 1)).hom := by
  change (HypercohomologyFiltration.functor
    (SheafHypercohomology.globalSections k (projectiveLine k)) 2).map
      (DegreeFiltration.inclusion
        (SchemeDeRham.sheafComplex k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))) 1) ≫
      (schemeH2IsoSheafH1 k).hom = _
  rw [← DegreeFiltration.degreeOneIso_hom_inclusion _
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn), Functor.map_comp, Category.assoc]
  congr 1
  exact BoundedBelowDerived.twoTermHypercohomologyIsoRightDerived_inclusion
    (SheafHypercohomology.globalSections k (projectiveLine k)) _
    (fun n hn ↦ higherSchemeFormsSheaf_isZero k n hn)
    (schemeZeroFormsH1_isZero k) (schemeZeroFormsH2_isZero k)

end HodgeConjecture.ProjectiveLineDeRham
