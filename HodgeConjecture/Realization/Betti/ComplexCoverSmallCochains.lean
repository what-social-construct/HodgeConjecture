module

public import HodgeConjecture.Realization.Betti.ComplexSingularPresheaf
public import HodgeConjecture.Realization.Betti.CoverSmallChains
public import HodgeConjecture.SheafCohomology.ComplexKernelComparison

@[expose] public noncomputable section

/-!
# Unrestricted complex cochains on an indexed small singular cover

The original rational small-chain inclusion is dualized with unrestricted
complex-valued functionals. Exactness of that functional functor transfers
the proved chain quasi-isomorphism without a finite-dimensionality premise.
Actual extension of a functional from the small-chain subspace makes the
restriction termwise surjective; its native kernel is therefore acyclic.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

namespace HodgeConjecture.ComplexCoverSmallCochains

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial
open SingularSubcomplexes

universe v

variable {ι : Type v} (X : TopCat.{0}) (U : ι → Set X)

/-- Original indexed small chains with unrestricted complex coefficients on their dual. -/
abbrev complex := HomCoefficients.dualComplex ℚ ℂ (coverComplex X U)

/-- Literal precomposition with the original indexed small-chain inclusion. -/
def restriction : SingularCoefficientChange.complexCochains X ⟶ complex X U :=
  ((HomologicalComplex.opFunctor _ (.down ℕ)) ⋙
    (HomCoefficients.functor ℚ ℂ).mapHomologicalComplex (.up ℕ)).map
      (coverInclusion X U).op

/-- The small-chain dual retains the original complex-valued simplex coordinates. -/
def coverCoordinates (n : ℕ) :
    (complex X U).X n ≃ₗ[ℂ] ((coverSingular X U).obj (op ⦋n⦌) → ℂ) :=
  ((SingularChainCoordinates.coordinates (coverSingular X U : SSet) n).symm.congrLeft ℂ ℂ).trans
    (Finsupp.llift ℂ ℚ ℂ ((coverSingular X U).obj (op ⦋n⦌))).symm

/-- The native dual map literally restricts the original complex-valued simplex function. -/
theorem restriction_coordinates (n : ℕ)
    (φ : (SingularCoefficientChange.complexCochains X).X n)
    (σ : (coverSingular X U).obj (op ⦋n⦌)) :
    coverCoordinates X U n ((restriction X U).f n φ) σ =
      SingularCoefficientChange.complexCoordinates X n φ σ.val := by
  change (show SingularCoefficientChange.chains X |>.X n →ₗ[ℚ] ℂ from φ)
    ((coverInclusion X U).f n
      (SingularChainCoordinates.coordinates (coverSingular X U : SSet) n
        (Finsupp.single σ 1))) =
      (show SingularCoefficientChange.chains X |>.X n →ₗ[ℚ] ℂ from φ)
        (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
          (Finsupp.single σ.val 1))
  rw [SubcomplexChainCoordinates.inclusion_coordinates]
  simp [SubcomplexChainCoordinates.inclusionCoordinates]

/-- Vanishing under actual small restriction is vanishing on each contained simplex. -/
theorem restriction_eq_zero_iff (n : ℕ)
    (φ : (SingularCoefficientChange.complexCochains X).X n) :
    (restriction X U).f n φ = 0 ↔
      ∀ σ : (coverSingular X U).obj (op ⦋n⦌),
        SingularCoefficientChange.complexCoordinates X n φ σ.val = 0 := by
  constructor
  · intro h σ
    have hσ := congrArg (fun z ↦ coverCoordinates X U n z σ) h
    simpa only [restriction_coordinates, map_zero, Pi.zero_apply] using hσ
  · intro h
    apply (coverCoordinates X U n).injective
    funext σ
    rw [restriction_coordinates]
    simpa only [map_zero, Pi.zero_apply] using h σ

/-- Exact unrestricted complex-valued dualization preserves the actual small-chain equivalence. -/
theorem restriction_quasiIso (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) : QuasiIso (restriction X U) := by
  letI : QuasiIso (coverInclusion X U) := CoverSmallChains.inclusion_quasiIso X U hU hcover
  change QuasiIso (((HomCoefficients.functor ℚ ℂ).mapHomologicalComplex (.up ℕ)).map
    ((HomologicalComplex.opFunctor _ (.down ℕ)).map (coverInclusion X U).op))
  infer_instance

/-- A complex functional on actual small chains extends to the original full chains. -/
theorem restriction_surjective (n : ℕ) : Function.Surjective ((restriction X U).f n) := by
  intro φ
  have hi := SubcomplexChainCoordinates.inclusion_injective (coverSingular X U) n
  have hker : LinearMap.ker ((coverInclusion X U).f n).hom ≤ LinearMap.ker φ := by
    rw [LinearMap.ker_eq_bot.mpr hi]
    exact bot_le
  obtain ⟨ψ, hψ⟩ := HomCoefficients.exists_factor ℚ ℂ ((coverInclusion X U).f n) φ hker
  refine ⟨ψ, ?_⟩
  change ψ.comp ((coverInclusion X U).f n).hom = φ
  exact hψ

/-- The actual native kernel of complex-valued restriction to cover-small chains. -/
abbrev vanishingComplex := kernel (restriction X U)

/-- The native kernel is acyclic for every actual indexed open cover. -/
theorem vanishingComplex_acyclic (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) : (vanishingComplex X U).Acyclic := by
  letI : Epi (restriction X U) :=
    epi_of_epi_f _ (fun n ↦ (ModuleCat.epi_iff_surjective _).mpr (restriction_surjective X U n))
  letI : Epi (ShortComplex.kernelSequence (restriction X U)).g := by
    change Epi (restriction X U)
    infer_instance
  have hshort : (ShortComplex.kernelSequence (restriction X U)).ShortExact :=
    ⟨ShortComplex.kernelSequence_exact (restriction X U)⟩
  exact hshort.acyclic_X₁ (restriction_quasiIso X U hU hcover)

end HodgeConjecture.ComplexCoverSmallCochains
