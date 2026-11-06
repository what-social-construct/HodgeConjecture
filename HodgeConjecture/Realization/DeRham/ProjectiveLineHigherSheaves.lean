module

public import HodgeConjecture.Realization.DeRham.AffineFormsSheaf
public import HodgeConjecture.Realization.DeRham.OpenImmersionForms
public import HodgeConjecture.Geometry.ProjectiveLineOpenCover

@[expose] public section

/-!
# The actual projective-line form sheaves vanish above degree one

On every open of either affine chart, the original coordinate-ring Kähler
module has the proved differential-coordinate basis. The canonical
sheafification comparison identifies those actual forms with the sections
of the actual sheaf complex. Sheaf locality on the original covering then
proves global vanishing of the higher sheaf terms.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open KaehlerDifferential

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Every open inside an actual affine-line chart has zero higher-form sheaf sections. -/
theorem affineLineChartHigherFormsSheaf_subsingleton
    (i : Spec (.of (Polynomial k)) ⟶ X) [IsOpenImmersion i]
    (hi : i ≫ f = affineStructureMorphism k (Polynomial k))
    (U : (Spec (.of (Polynomial k))).Opens) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton ((formsSheaf k X f n).obj.obj (op (i ''ᵁ U))) := by
  have hunit : IsIso (toSheafify (Opens.grothendieckTopology
      (Spec (.of (Polynomial k)))) (formsPresheaf k (Spec (.of (Polynomial k)))
        (i ≫ f) n)) := by
    rw [hi]
    exact affineLineFormsSheafUnit_isIso k n
  have := openImmersionFormsSheafUnit_app_isIso k f i n U hunit
  have : Subsingleton ((formsPresheaf k (Spec (.of (Polynomial k))) (i ≫ f) n).obj
      (op U)) := by
    rw [hi]
    let := sectionAlgebra k (Spec (.of (Polynomial k)))
      (affineStructureMorphism k (Polynomial k)) U
    exact affineHigherForms_subsingleton k (Polynomial k) (polynomialEquiv k)
      Polynomial.X (by simp) U n hn
  let e := (asIso ((toSheafify (Opens.grothendieckTopology X)
    (formsPresheaf k X f n)).app (op (i ''ᵁ U)))).symm ≪≫
      (openImmersionFormsPresheafIso k f i n).app (op U)
  exact e.toLinearEquiv.injective.subsingleton

end

end HodgeConjecture.SchemeDeRham

namespace HodgeConjecture.ProjectiveLineDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The actual higher form sheaf has only its zero section on every open. -/
theorem higherSchemeFormsSheaf_sections_subsingleton (n : ℕ) (hn : 2 ≤ n)
    (U : (projectiveLine k).Opens) :
    Subsingleton ((SchemeDeRham.formsSheaf k (projectiveLine k)
      (projectiveLineStructureMorphism k) n).obj.obj (op U)) := by
  let F := SchemeDeRham.formsSheaf k (projectiveLine k) (projectiveLineStructureMorphism k) n
  have hF : TopCat.Presheaf.IsSheaf F.obj := F.property
  refine ⟨fun s t ↦ TopCat.Presheaf.IsSheaf.section_ext hF (fun x hx ↦ ?_)⟩
  have hchart : ∃ i : Spec (.of (Polynomial k)) ⟶ projectiveLine k,
      IsOpenImmersion i ∧ i ≫ projectiveLineStructureMorphism k =
        SchemeDeRham.affineStructureMorphism k (Polynomial k) ∧ x ∈ Set.range i := by
    rcases projectiveLine_charts_cover k x with hx | hx
    · exact ⟨projectiveLineXChart k, inferInstance,
        projectiveLineXChart_comp_structureMorphism k, hx⟩
    · exact ⟨projectiveLineYChart k, inferInstance,
        projectiveLineYChart_comp_structureMorphism k, hx⟩
  obtain ⟨i, hi, hif, hxi⟩ := hchart
  let := hi
  have hle : i ''ᵁ i ⁻¹ᵁ U ≤ U := i.image_preimage_le U
  have hxlocal : x ∈ i ''ᵁ i ⁻¹ᵁ U := by
    rw [i.image_preimage_eq_opensRange_inf]
    exact ⟨hxi, hx⟩
  have := SchemeDeRham.affineLineChartHigherFormsSheaf_subsingleton k
    (projectiveLineStructureMorphism k) i hif (i ⁻¹ᵁ U) n hn
  exact ⟨_, hle, hxlocal, Subsingleton.elim _ _⟩

/-- Every sheaf term of the actual scheme complex above degree one is zero. -/
theorem higherSchemeFormsSheaf_isZero (n : ℕ) (hn : 2 ≤ n) :
    IsZero (SchemeDeRham.formsSheaf k (projectiveLine k)
      (projectiveLineStructureMorphism k) n) := by
  let F := SchemeDeRham.formsSheaf k (projectiveLine k) (projectiveLineStructureMorphism k) n
  apply IsZero.of_full_of_faithful_of_isZero
    (TopCat.Sheaf.forget (ModuleCat.{u} k) (projectiveLine k)) F
  apply Functor.isZero
  intro U
  have : Subsingleton (F.obj.obj U) :=
    higherSchemeFormsSheaf_sections_subsingleton k n hn U.unop
  exact ModuleCat.isZero_of_subsingleton (F.obj.obj U)

end

end HodgeConjecture.ProjectiveLineDeRham
