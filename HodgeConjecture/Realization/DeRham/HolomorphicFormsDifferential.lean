module

public import HodgeConjecture.Realization.DeRham.HolomorphicFormsNaturality

@[expose] public section

/-! # Differential compatibility in all degrees

Every algebraic spanning generator is the pullback of the coordinate
form z₀ dz₁ ∧ ... ∧ dzₙ. Its derivative is the constant volume form by
Laplace expansion of the determinant. Pullback naturality of d then
gives the chain-map law on the original algebraic de Rham complex.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open CategoryTheory TopologicalSpace KaehlerDifferential
open scoped Manifold ContDiff
open HolomorphicForms

/-- The universal generator z₀ dz₁ ∧ ... ∧ dzₙ as a continuous linear coefficient map. -/
def coordinateGeneratorCoeff (n : ℕ) :
    (Fin (n + 1) → ℂ) →L[ℂ] Coeff (Fin (n + 1) → ℂ) n :=
  (ContinuousLinearMap.proj 0).smulRight
    (covectorWedge n (fun i ↦ ContinuousLinearMap.proj i.succ))

theorem coordinateGeneratorCoeff_apply (n : ℕ) (x : Fin (n + 1) → ℂ)
    (v : Fin n → (Fin (n + 1) → ℂ)) :
    coordinateGeneratorCoeff n x v = x 0 * Matrix.det (fun i j ↦ v i j.succ) := by
  change x 0 * covectorWedge n _ v = _
  rw [covectorWedge_apply]
  rfl

theorem extDeriv_coordinateGenerator (n : ℕ) (x : Fin (n + 1) → ℂ) :
    extDeriv (coordinateGeneratorCoeff n) x =
      covectorWedge (n + 1) (fun i ↦ ContinuousLinearMap.proj i) := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [extDeriv, (coordinateGeneratorCoeff n).fderiv]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, covectorWedge_apply,
    Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateGeneratorCoeff_apply]
  simp [Fin.removeNth, Matrix.submatrix, mul_assoc]
  left
  congr 1

def coordinateGenerator (n : ℕ) : Sections (⊤ : Opens (Fin (n + 1) → ℂ)) n :=
  ⟨fun x ↦ coordinateGeneratorCoeff n x,
    (coordinateGeneratorCoeff n).contMDiff.comp contMDiff_subtype_val⟩

theorem differential_coordinateGenerator (n : ℕ) :
    HolomorphicForms.differential (⊤ : Opens (Fin (n + 1) → ℂ)) n (coordinateGenerator n) =
      (ContMDiffMap.const (covectorWedge (n + 1) (fun i ↦ ContinuousLinearMap.proj i)) :
        Sections (⊤ : Opens (Fin (n + 1) → ℂ)) (n + 1)) := by
  apply ContMDiffMap.ext
  intro x
  rw [differential_eq_of_extension _ (coordinateGeneratorCoeff n) (fun _ ↦ rfl)]
  exact extDeriv_coordinateGenerator n x

variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CommRing A] [Algebra ℂ A]

def generatorCoordinates (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin (n + 1) → A) (y : E) : Fin (n + 1) → ℂ :=
  fun i ↦ extend (φ (a i)) y

theorem generatorCoordinates_contDiffOn (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin (n + 1) → A) :
    ContDiffOn ℂ ∞ (generatorCoordinates U φ n a) U := by
  apply contDiffOn_pi.mpr
  intro i y hy
  exact (contDiffAt_extend (φ (a i)) ⟨y, hy⟩).contDiffWithinAt

theorem generatorCoordinates_fderiv (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin (n + 1) → A) (x : U) (v : E) (i : Fin (n + 1)) :
    fderiv ℂ (generatorCoordinates U φ n a) x v i = fderiv ℂ (extend (φ (a i))) x v := by
  change fderiv ℂ (fun y i ↦ extend (φ (a i)) y) (x : E) v i = _
  rw [fderiv_pi
    (fun i ↦ (contDiffAt_extend (φ (a i)) x).differentiableAt (by simp))]
  rfl

/-- A spanning generator is the actual pullback of the universal coordinate generator. -/
theorem algebraicFormsMap_generator_pullback (U : Opens E) (φ : A →ₐ[ℂ] Functions U)
    (n : ℕ) (a : Fin (n + 1) → A) :
    algebraicFormsMap U φ n
      (a 0 • exteriorPower.ιMulti A n (fun i ↦ D ℂ A (a i.succ))) =
      pullback (V := ⊤) (generatorCoordinates U φ n a)
        (generatorCoordinates_contDiffOn U φ n a) (fun _ _ ↦ trivial) n
          (coordinateGenerator n) := by
  apply ContMDiffMap.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [algebraicFormsMap_generator]
  change _ = coordinateGeneratorCoeff n (generatorCoordinates U φ n a x)
    (fun i ↦ fderiv ℂ (generatorCoordinates U φ n a) x (v i))
  rw [coordinateGeneratorCoeff_apply]
  simp only [generatorCoordinates, extend_of_mem]
  congr 2
  funext i j
  exact (generatorCoordinates_fderiv U φ n a x (v i) j.succ).symm

/-- The constructed all-degree map commutes with the original algebraic differential. -/
theorem algebraicFormsMap_differential (U : Opens E) (φ : A →ₐ[ℂ] Functions U) (n : ℕ) :
    (HolomorphicForms.differential U n).comp (algebraicFormsMap U φ n) =
      (algebraicFormsMap U φ (n + 1)).comp (deRhamDifferential (A := ℂ) n) := by
  apply AlgebraDeRham.forms_linearMap_ext ℂ n
  intro a
  change HolomorphicForms.differential U n (algebraicFormsMap U φ n _) = _
  rw [algebraicFormsMap_generator_pullback, pullback_differential,
    differential_coordinateGenerator]
  change _ = algebraicFormsMap U φ (n + 1) (deRhamDifferential (A := ℂ) n _)
  rw [deRhamDifferential_smul_ιMulti_D, algebraicFormsMap_ιMulti_D]
  apply ContMDiffMap.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change covectorWedge (n + 1) (fun i ↦ ContinuousLinearMap.proj i)
    (fun i ↦ fderiv ℂ (generatorCoordinates U φ n a) x (v i)) = _
  rw [covectorWedge_apply, wedgeOneForms_apply]
  congr 1
  funext i j
  change fderiv ℂ (generatorCoordinates U φ n a) x (v i) j = _
  rw [generatorCoordinates_fderiv]
  exact (congrArg (fun l : E →L[ℂ] ℂ ↦ l (v i))
    (oneFormsEquiv_differential U (φ (a j)) x)).symm

/-- The map is a morphism of the existing sectionwise cochain complexes. -/
def algebraicComplexMap (U : Opens E) (φ : A →ₐ[ℂ] Functions U) :
    deRhamComplex ℂ A ⟶ sectionComplex E U where
  f n := ModuleCat.ofHom (algebraicFormsMap U φ n)
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    simp only [deRhamComplex_d, sectionComplex, CochainComplex.of_d]
    exact ModuleCat.hom_ext (algebraicFormsMap_differential U φ i)

end HodgeConjecture.HolomorphicDeRham
