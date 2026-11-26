module

public import HodgeConjecture.Realization.Chow.FiniteCoverageCertificate
public import HodgeConjecture.LinearAlgebra.GaloisDescent
public import HodgeConjecture.LinearAlgebra.Harmonic.Transport

@[expose] public section

/-!
# Descent and harmonic transport gates for finite coverage

Galois-fixed tensors in the scalar extension of the existing rational Chow
module descend uniquely to that same Chow module. Exact extended cycle-class
columns then descend by injectivity of scalar extension. These tensors are
coefficient data, not Chow groups of a base-changed scheme.

The harmonic constructor transports its witness through the native cellular
cohomology quotient. Symmetry identifies this map with the raw cellular
endomorphism on harmonic representatives. Injectivity of the transported
witness is mandatory: a projector that loses a target direction cannot bind
columns by killing their differences. The combined constructor applies both
gates before the existing arithmetic checker and fixed-target coverage theorem.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.FiniteCoverageCertificate

open scoped TensorProduct

variable {Chow H ι N : Type*}
  [AddCommGroup Chow] [Module ℚ Chow] [AddCommGroup H] [Module ℚ H]
  [Field N] [Algebra ℚ N]

/-- Scalar extension of the original cycle map, with no new geometric map. -/
def extendedCycleClass (M : RationalHodgeCycleClassModel Chow H) :
    N ⊗[ℚ] Chow →ₗ[ℚ] N ⊗[ℚ] H :=
  TensorProduct.map (LinearMap.id : N →ₗ[ℚ] N) M.cycleClass

@[simp]
theorem extendedCycleClass_tensorInclude (M : RationalHodgeCycleClassModel Chow H) (z : Chow) :
    extendedCycleClass (N := N) M (GaloisDescent.tensorInclude (N := N) z) =
      GaloisDescent.tensorInclude (N := N) (M.cycleClass z) := by
  simp [extendedCycleClass, GaloisDescent.tensorInclude]

variable [FiniteDimensional ℚ N] [IsGalois ℚ N]

/-- The actual original Chow classes recovered from invariant coefficient tensors. -/
def descendedCycles (upstairs : ι → N ⊗[ℚ] Chow)
    (fixed : ∀ j (g : N ≃ₐ[ℚ] N), GaloisDescent.scalarAction g (upstairs j) = upstairs j) :
    ι → Chow :=
  fun j => GaloisDescent.descendFixed (upstairs j) (fixed j)

@[simp]
theorem include_descendedCycles (upstairs : ι → N ⊗[ℚ] Chow)
    (fixed : ∀ j (g : N ≃ₐ[ℚ] N), GaloisDescent.scalarAction g (upstairs j) = upstairs j)
    (j : ι) :
    GaloisDescent.tensorInclude (N := N) (descendedCycles upstairs fixed j) = upstairs j :=
  GaloisDescent.include_descendFixed (upstairs j) (fixed j)

variable [Fintype ι] [DecidableEq ι]

/-- Fixed coefficient tensors and exact extended columns bind an original aggregate. -/
def of_galois_fixed
    (M : RationalHodgeCycleClassModel Chow H) (b : Module.Basis ι ℚ M.hodgeClasses)
    (upstairs : ι → N ⊗[ℚ] Chow)
    (fixed : ∀ j (g : N ≃ₐ[ℚ] N), GaloisDescent.scalarAction g (upstairs j) = upstairs j)
    (A : Matrix ι ι ℚ) (arithmetic : ModularRankCertificate.Certificate ι)
    (extended_columns : ∀ j, extendedCycleClass M (upstairs j) =
      GaloisDescent.tensorInclude (N := N) (b.equivFun.symm (fun i => A i j) : H)) :
    Certificate M b where
  cycles := descendedCycles upstairs fixed
  coordinates := A
  arithmetic := arithmetic
  column_binding j := by
    apply Subtype.ext
    change M.cycleClass (descendedCycles upstairs fixed j) = _
    apply GaloisDescent.tensorInclude_injective (K := ℚ) (N := N) (V := H)
    rw [← extendedCycleClass_tensorInclude, include_descendedCycles]
    exact extended_columns j

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : Harmonic.OrientedTwoComplex Vertex Edge Face}

/-- Raw symmetric cellular certificates are checked through the quotient-defined transport. -/
def of_transported_harmonic
    (M : RationalHodgeCycleClassModel Chow H) (b : Module.Basis ι ℚ M.hodgeClasses)
    (cycles : ι → Chow) (A : Matrix ι ι ℚ)
    (arithmetic : ModularRankCertificate.Certificate ι)
    (F : Harmonic.CellularSheaf X) (η : F.Morphism F) (symmetric : η.mapC1.IsSymmetric)
    (W : H →ₗ[ℚ] F.harmonicOneSubspace)
    (faithful : Function.Injective (η.transportHarmonicWitness W))
    (column_certificates : ∀ j, F.IsExactOneCochain
      (η.mapC1 (W (M.cycleClass (cycles j))) -
        η.mapC1 (W (b.equivFun.symm (fun i => A i j) : H)))) : Certificate M b := by
  apply of_harmonic M b cycles A arithmetic F (η.transportHarmonicWitness W) faithful
  intro j
  have transport_coe (x : H) :
      (η.transportHarmonicWitness W x : F.C1) = η.mapC1 (W x) := by
    rw [η.transportHarmonicWitness_apply symmetric W x]
    rfl
  simpa only [transport_coe] using column_certificates j

/-- Both Galois coefficient descent and faithful harmonic transport are mandatory. -/
def of_galois_transported_harmonic
    (M : RationalHodgeCycleClassModel Chow H) (b : Module.Basis ι ℚ M.hodgeClasses)
    (upstairs : ι → N ⊗[ℚ] Chow)
    (fixed : ∀ j (g : N ≃ₐ[ℚ] N), GaloisDescent.scalarAction g (upstairs j) = upstairs j)
    (A : Matrix ι ι ℚ) (arithmetic : ModularRankCertificate.Certificate ι)
    (F : Harmonic.CellularSheaf X) (η : F.Morphism F) (symmetric : η.mapC1.IsSymmetric)
    (W : H →ₗ[ℚ] F.harmonicOneSubspace)
    (faithful : Function.Injective (η.transportHarmonicWitness W))
    (column_certificates : ∀ j, F.IsExactOneCochain
      (η.mapC1 (W (M.cycleClass (descendedCycles upstairs fixed j))) -
        η.mapC1 (W (b.equivFun.symm (fun i => A i j) : H)))) : Certificate M b :=
  of_transported_harmonic M b (descendedCycles upstairs fixed) A arithmetic
    F η symmetric W faithful column_certificates

end HodgeConjecture.FiniteCoverageCertificate

end
