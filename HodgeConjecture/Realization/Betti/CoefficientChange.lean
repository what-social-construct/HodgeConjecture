module

public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import HodgeConjecture.Realization.HodgeFiltration

@[expose] public noncomputable section

/-!
# Coefficient change for the original rational singular complex

Complex-valued cochains are unrestricted functionals on the original
rational singular chains. The actual coefficient map is a cohomology
isomorphism when the original rational group in that degree is finite
dimensional. This does not identify a holomorphic or sheaf comparison map.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomologicalComplex Opposite Simplicial
open scoped TensorProduct

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

/-- The existing native rational singular chains, unchanged. -/
abbrev chains := SingularChainCoordinates.complex (TopCat.toSSet.obj X)

/-- Unrestricted complex-valued functionals on those same rational chains. -/
abbrev complexCochains := HomCoefficients.dualComplex ℚ ℂ (chains X)

abbrev ComplexCohomology (n : ℕ) := (complexCochains X).homology n

/-- The original rational coordinate isomorphism, after shared ownership of linear duals. -/
def rationalComplexIso : SingularCochains.complex X ≅ HomCoefficients.dualComplex ℚ ℚ (chains X) :=
  (CochainDualComparison.comparisonIso (TopCat.toSSet.obj X)).symm

/-- The same unrestricted complex simplex functions, by the original native chain coordinates. -/
def complexCoordinates (n : ℕ) :
    (complexCochains X).X n ≃ₗ[ℂ] (SingularCochains.Simplex X n → ℂ) :=
  ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm.congrLeft ℂ ℂ).trans
    (Finsupp.llift ℂ ℚ ℂ (SingularCochains.Simplex X n)).symm

/-- The original complexification of cochains maps by literal scalar evaluation. -/
def cochainComparison :
    ((HomCoefficients.tensorFunctor ℚ ℂ).mapHomologicalComplex (.up ℕ)).obj
        (SingularCochains.complex X) ⟶ complexCochains X :=
  ((HomCoefficients.tensorFunctor ℚ ℂ).mapHomologicalComplex (.up ℕ)).map
      (rationalComplexIso X).hom ≫
    HomCoefficients.complexComparison ℚ ℂ (chains X)

@[simp]
theorem cochainComparison_apply (n : ℕ) (c : ℂ) (φ : SingularCochains.Cochain X n)
    (σ : SingularCochains.Simplex X n) :
    complexCoordinates X n ((cochainComparison X).f n (c ⊗ₜ[ℚ] φ)) σ = c * (φ σ : ℂ) := by
  change c * algebraMap ℚ ℂ
      ((CochainDualCoordinates.coordinates (TopCat.toSSet.obj X) n).symm φ
        (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ 1))) = _
  rw [CochainDualCoordinates.coordinates_symm_coordinates_single]
  simp

/-- The map on the original tensor complexification of rational singular cohomology. -/
def cohomologyComparison (n : ℕ) :
    ModuleCat.of ℂ (RationalComplexification.Space (SingularCochains.Cohomology X n)) ⟶
      ComplexCohomology X n :=
  (HomCoefficients.tensorFunctor ℚ ℂ).map (homologyMapIso (rationalComplexIso X) n).hom ≫
    HomCoefficients.cohomologyComparison ℚ ℂ (chains X) n

/-- The comparison on cohomology is fixed by the actual simplex-function coefficient map. -/
@[reassoc]
theorem cohomologyComparison_induced (n : ℕ) :
    (HomCoefficients.tensorHomologyIso ℚ ℂ (SingularCochains.complex X) n).hom ≫
        cohomologyComparison X n = homologyMap (cochainComparison X) n := by
  unfold cohomologyComparison cochainComparison
  rw [homologyMap_comp]
  simp only [homologyMapIso_hom]
  rw [← Category.assoc, ← HomCoefficients.tensorHomologyIso_naturality,
    Category.assoc, HomCoefficients.tensorHomologyIso_cohomologyComparison]

/-- Finiteness of the original rational cohomology suffices; no finiteness of chain terms is assumed. -/
theorem finiteHomology_of_finiteCohomology (n : ℕ)
    [FiniteDimensional ℚ (SingularCochains.Cohomology X n)] :
    FiniteDimensional ℚ ((chains X).homology n) := by
  have : FiniteDimensional ℚ (Module.Dual ℚ ((chains X).homology n)) :=
    Module.Finite.equiv ((homologyMapIso (rationalComplexIso X) n) ≪≫
      HomCoefficients.dualHomologyIso ℚ ℚ (chains X) n).toLinearEquiv
  exact (Module.finite_dual_iff ℚ).mp this

theorem cohomologyComparison_isIso (n : ℕ)
    [FiniteDimensional ℚ (SingularCochains.Cohomology X n)] :
    IsIso (cohomologyComparison X n) := by
  have := finiteHomology_of_finiteCohomology X n
  have := HomCoefficients.cohomologyComparison_isIso ℚ ℂ (chains X) n
  unfold cohomologyComparison
  infer_instance

/-- This isomorphism is induced by the original scalar-evaluation map on actual cochains. -/
def cohomologyIso (n : ℕ) [FiniteDimensional ℚ (SingularCochains.Cohomology X n)] :
    ModuleCat.of ℂ (RationalComplexification.Space (SingularCochains.Cohomology X n)) ≅
      ComplexCohomology X n := by
  have := cohomologyComparison_isIso X n
  exact asIso (cohomologyComparison X n)

end HodgeConjecture.SingularCoefficientChange
