module

public import HodgeConjecture.Geometry.Holomorphic.Wedge
public import HodgeConjecture.Realization.DeRham.HolomorphicKaehler

@[expose] public section

/-!
# The all-degree algebraic-to-holomorphic forms map

We apply the existing functorial map on algebraic differential forms,
then the exterior-power universal property to the original Kähler lift.
The analytic alternating product is the determinant wedge, with no
factorial normalization. No comparison isomorphism is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open TopologicalSpace KaehlerDifferential
open scoped Manifold ContDiff
open HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Exterior powers of the existing Kähler realization, into genuine coordinate forms. -/
def formsRealization (U : Opens E) (n : ℕ) :
    ⋀[Functions U]^n Ω[Functions U⁄ℂ] →ₗ[Functions U] Sections U n :=
  exteriorPower.alternatingMapLinearEquiv
    ((wedgeOneForms U n).compLinearMap (kaehlerRealization U))

theorem formsRealization_ιMulti (U : Opens E) (n : ℕ) (v : Fin n → Ω[Functions U⁄ℂ]) :
    formsRealization U n (exteriorPower.ιMulti (Functions U) n v) =
      wedgeOneForms U n (fun i ↦ kaehlerRealization U (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The original algebraic exterior powers map to holomorphic forms in every degree. -/
def algebraicFormsMap (U : Opens E) (φ : A →ₐ[ℂ] Functions U) (n : ℕ) :
    ⋀[A]^n Ω[A⁄ℂ] →ₗ[ℂ] Sections U n :=
  ((formsRealization U n).restrictScalars ℂ).comp (AlgebraDeRham.formsMap ℂ φ n)

theorem algebraicFormsMap_smul (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : A) (η : ⋀[A]^n Ω[A⁄ℂ]) :
    algebraicFormsMap U φ n (a • η) = φ a • algebraicFormsMap U φ n η := by
  change formsRealization U n (AlgebraDeRham.formsMap ℂ φ n (a • η)) = _
  rw [AlgebraDeRham.formsMap_smul, map_smul]
  rfl

theorem algebraicFormsMap_ιMulti_D (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin n → A) :
    algebraicFormsMap U φ n (exteriorPower.ιMulti A n (fun i ↦ D ℂ A (a i))) =
      wedgeOneForms U n (fun i ↦ HolomorphicForms.differential U 0
        ((functionsEquiv U).symm (φ (a i)))) := by
  change formsRealization U n (AlgebraDeRham.formsMap ℂ φ n _) = _
  rw [AlgebraDeRham.formsMap_ιMulti_D, formsRealization_ιMulti]
  simp only [kaehlerRealization_D]

/-- The all-degree construction extends the previously constructed Kähler map. -/
theorem algebraicFormsMap_one (U : Opens E) (φ : A →ₐ[ℂ] Functions U) (η : Ω[A⁄ℂ]) :
    algebraicFormsMap U φ 1 (exteriorPower.ιMulti A 1 (fun _ ↦ η)) =
      algebraicOneFormsMap U φ η := by
  change formsRealization U 1 (AlgebraDeRham.formsMap ℂ φ 1 _) = _
  rw [AlgebraDeRham.formsMap_ιMulti, formsRealization_ιMulti, wedgeOneForms_one]
  rfl

/-- The expected coefficient on the same spanning generators used by algebraic de Rham. -/
theorem algebraicFormsMap_generator (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin (n + 1) → A) (x : U) (v : Fin n → E) :
    algebraicFormsMap U φ n
        (a 0 • exteriorPower.ιMulti A n (fun i ↦ D ℂ A (a i.succ))) x v =
      φ (a 0) x * Matrix.det (fun i j ↦ fderiv ℂ (extend (φ (a j.succ))) x (v i)) := by
  rw [algebraicFormsMap_smul, algebraicFormsMap_ιMulti_D]
  change φ (a 0) x * wedgeOneForms U n _ x v = _
  rw [wedgeOneForms_apply]
  congr 2
  funext i j
  exact congrArg (fun l : E →L[ℂ] ℂ ↦ l (v i))
    (oneFormsEquiv_differential U (φ (a j.succ)) x)

end HodgeConjecture.HolomorphicDeRham
