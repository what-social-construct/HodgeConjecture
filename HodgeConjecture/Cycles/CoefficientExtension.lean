module

public import HodgeConjecture.Cycles.CycleDegree
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.LinearMap.Rat

@[expose] public section

/-!
# Rational coefficients on the existing homogeneous cycles

Coefficient extension leaves the actual integral closed supports unchanged.
The degree submodule with rational coefficients is canonically the scalar
extension of the integral degree submodule, including when the set of
supports in that degree is infinite or empty.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry TensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- Coefficientwise extension on the existing degree submodule. -/
def cyclesOfDegreeRationalize (δ : DimensionFunction X) (n : ℤ) :
    cyclesOfDegree ℤ δ n →ₗ[ℤ] cyclesOfDegree ℚ δ n :=
  ((Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap).comp
    (cyclesOfDegree ℤ δ n).subtype).codRestrict
    ((cyclesOfDegree ℚ δ n).restrictScalars ℤ) (by
      intro c
      apply (mem_cyclesOfDegree_iff ℚ δ n _).mpr
      intro Z hZ
      exact (mem_cyclesOfDegree_iff ℤ δ n c.val).mp c.property Z (by
        intro hz
        apply hZ
        change (c.val Z : ℚ) = 0
        simp [hz]))

@[simp]
theorem cyclesOfDegreeRationalize_apply (δ : DimensionFunction X) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) (Z : IntegralClosedSubscheme X) :
    (cyclesOfDegreeRationalize δ n c : Cycles X ℚ) Z = (c.val Z : ℚ) := rfl

/-- Coefficient extension is injective before taking the relation quotient. -/
theorem cyclesOfDegreeRationalize_injective (δ : DimensionFunction X) (n : ℤ) :
    Function.Injective (cyclesOfDegreeRationalize δ n) := by
  intro c e h
  apply Subtype.ext
  apply Finsupp.ext
  intro Z
  exact Int.cast_injective (congrArg (fun t : cyclesOfDegree ℚ δ n ↦ t.val Z) h)

@[simp]
theorem cyclesOfDegreeRationalize_single (δ : DimensionFunction X) (n : ℤ)
    (Z : IntegralClosedSubscheme X) (a : ℤ) (hZ : supportDegree δ Z = n) :
    cyclesOfDegreeRationalize δ n
      ⟨Finsupp.single Z a, single_mem_cyclesOfDegree ℤ δ n Z a hZ⟩ =
      ⟨Finsupp.single Z (a : ℚ), single_mem_cyclesOfDegree ℚ δ n Z (a : ℚ) hZ⟩ := by
  apply Subtype.ext
  change Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) (Finsupp.single Z a) = _
  simp

/-- Rational homogeneous cycles are the scalar extension of the same
integral homogeneous cycles. -/
def cyclesOfDegreeRationalizationEquiv (δ : DimensionFunction X) (n : ℤ) :
    (ℚ ⊗[ℤ] cyclesOfDegree ℤ δ n) ≃ₗ[ℚ] cyclesOfDegree ℚ δ n := by
  classical
  let s := {Z : IntegralClosedSubscheme X | supportDegree δ Z = n}
  let e := TensorProduct.finsuppScalarRight ℤ ℚ ℚ s
  let eQ : (ℚ ⊗[ℤ] (s →₀ ℤ)) ≃ₗ[ℚ] (s →₀ ℚ) :=
    { e.toAddEquiv with map_smul' := map_rat_smul e }
  exact (LinearEquiv.baseChange ℤ ℚ _ _
    (Finsupp.supportedEquivFinsupp (M := ℤ) (R := ℤ) s)).trans
    (eQ.trans (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ) s).symm)

@[simp]
theorem cyclesOfDegreeRationalizationEquiv_tmul (δ : DimensionFunction X) (n : ℤ)
    (q : ℚ) (c : cyclesOfDegree ℤ δ n) :
    cyclesOfDegreeRationalizationEquiv δ n (q ⊗ₜ[ℤ] c) =
      q • cyclesOfDegreeRationalize δ n c := by
  classical
  apply (Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    {Z : IntegralClosedSubscheme X | supportDegree δ Z = n}).injective
  change (Finsupp.supportedEquivFinsupp _)
    ((Finsupp.supportedEquivFinsupp _).symm
      (TensorProduct.finsuppScalarRight ℤ ℚ ℚ _
        (q ⊗ₜ[ℤ] (Finsupp.supportedEquivFinsupp _) c))) = _
  rw [LinearEquiv.apply_symm_apply, map_smul]
  ext Z
  rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  change c.val Z.val • q = q * (c.val Z.val : ℚ)
  simp [mul_comm]

@[simp]
theorem cyclesOfDegreeRationalizationEquiv_one_tmul (δ : DimensionFunction X) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    cyclesOfDegreeRationalizationEquiv δ n (1 ⊗ₜ[ℤ] c) =
      cyclesOfDegreeRationalize δ n c := by
  simp

end

end HodgeConjecture.SchemeCycles
