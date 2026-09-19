import HodgeConjecture.Boundary.Normalization.NormalizationBaseChange
import Lean.Util.CollectAxioms

/-!
SP78 regressions for the canonical normalization tensor base-change square.
Run with `lake env lean research/NormalizationBaseChangeVerification.lean`.

The generic finite-tensor comparison is tested at independent universes and
at empty and singleton index types. The one-factor comparison requires only
algebraicity, with no normality, Noetherianity, separability, or finite-degree
premise. Actual function-field tests use the original generic-germ and
section-pullback scalar maps on a nonempty affine chart. All thirteen new
public declarations have enforced standard-three axiom audits.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open scoped TensorProduct Classical

noncomputable section

universe u uI uB uA uK uC

section Factorwise

variable {ι : Type uI} {R : Type uB}
variable {A : ι → Type uA} {C : ι → Type uC}
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, CommRing (C i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R (C i)]
variable (e : ∀ i, A i ≃ₐ[R] C i)

-- Factorwise equivalence itself does not need finite indexing.
example : (⨂[R] i, A i) ≃ₐ[R] (⨂[R] i, C i) :=
  piTensorProductCongr e

example (x y : ⨂[R] i, A i) :
    piTensorProductCongr e (x * y) = piTensorProductCongr e x * piTensorProductCongr e y :=
  (piTensorProductCongr e).map_mul x y

example (x : ∀ i, A i) :
    piTensorProductCongr e (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => e i (x i)) :=
  piTensorProductCongr_tprod e x

example (i : ι) (a : A i) :
    piTensorProductCongr e (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom i (e i a) :=
  piTensorProductCongr_singleAlgHom e i a

end Factorwise

section GenericTensor

variable {ι : Type uI} {B : Type uB} {A : Type uA} {K : Type uK}
variable [Fintype ι] [CommRing B] [CommRing A] [CommRing K]
variable [Algebra B A] [Algebra B K]

-- The generic construction is not restricted to fields or a single universe.
example : (K ⊗[B] (⨂[B] _ : ι, A)) ≃ₐ[K] (⨂[K] _ : ι, K ⊗[B] A) := by
  fail_if_success have _ : Field K := inferInstance
  exact piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)

example (k : K) (x : K ⊗[B] (⨂[B] _ : ι, A)) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K) (k • x) =
      k • piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K) x :=
  map_smul (piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)) k x

example (x y : K ⊗[B] (⨂[B] _ : ι, A)) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K) (x * y) =
      piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K) x *
        piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K) y :=
  (piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)).map_mul x y

example (k : K) (i : ι) (a : A) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)
        (k ⊗ₜ[B] (PiTensorProduct.singleAlgHom i a : ⨂[B] _ : ι, A)) =
      k • (PiTensorProduct.singleAlgHom i ((1 : K) ⊗ₜ[B] a) :
        ⨂[K] _ : ι, K ⊗[B] A) :=
  piTensorProductBaseChangeEquiv_tmul_singleAlgHom (ι := ι) (B := B) (A := A) (K := K) k i a

example (i : ι) (k : K) (a : A) :
    (piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)).symm
        (PiTensorProduct.singleAlgHom i (k ⊗ₜ[B] a)) =
      k ⊗ₜ[B] (PiTensorProduct.singleAlgHom i a : ⨂[B] _ : ι, A) :=
  piTensorProductBaseChangeEquiv_symm_singleAlgHom_tmul (ι := ι) (B := B) (A := A) (K := K) i k a

example (k : K) (x : ι → A) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)
        (k ⊗ₜ[B] PiTensorProduct.tprod B x) =
      k • PiTensorProduct.tprod K (fun i => (1 : K) ⊗ₜ[B] x i) :=
  piTensorProductBaseChangeEquiv_tmul_tprod (ι := ι) (B := B) (A := A) (K := K) k x

end GenericTensor

section EmptyAndSingleton

variable {B : Type uB} {A : Type uA} {K : Type uK}
variable [CommRing B] [CommRing A] [CommRing K] [Algebra B A] [Algebra B K]

-- No nonempty-index premise is hidden in the comparison.
example : (K ⊗[B] (⨂[B] _ : PEmpty.{uI+1}, A)) ≃ₐ[K]
    (⨂[K] _ : PEmpty.{uI+1}, K ⊗[B] A) :=
  piTensorProductBaseChangeEquiv (ι := PEmpty.{uI+1}) (B := B) (A := A) (K := K)

example (k : K) (a : A) :
    letI : DecidableEq PUnit.{uI+1} := fun x y => Classical.propDecidable (x = y)
    (piTensorProductBaseChangeEquiv (ι := PUnit.{uI+1})
      (B := B) (A := A) (K := K)).symm
        (PiTensorProduct.singleAlgHom PUnit.unit (k ⊗ₜ[B] a)) =
      k ⊗ₜ[B] (PiTensorProduct.singleAlgHom PUnit.unit a : ⨂[B] _ : PUnit.{uI+1}, A) := by
  letI : DecidableEq PUnit.{uI+1} := fun x y => Classical.propDecidable (x = y)
  exact piTensorProductBaseChangeEquiv_symm_singleAlgHom_tmul
    (ι := PUnit.{uI+1}) (B := B) (A := A) (K := K) PUnit.unit k a

end EmptyAndSingleton

section OneFactor

variable {B K L : Type u} [CommRing B] [Field K] [Field L]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra B L] [IsScalarTower B K L]
variable [Algebra.IsAlgebraic K L]

example : (K ⊗[B] normalizedCoordinateRing B L) ≃ₐ[K] L := by
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  fail_if_success have _ : FiniteDimensional K L := inferInstance
  exact normalizedCoordinateRingBaseChangeEquiv B K L

example (k : K) (x : normalizedCoordinateRing B L) :
    normalizedCoordinateRingBaseChangeEquiv B K L (k ⊗ₜ[B] x) =
      algebraMap K L k * (x : L) :=
  normalizedCoordinateRingBaseChangeEquiv_tmul B K L k x

example (x : normalizedCoordinateRing B L) :
    (normalizedCoordinateRingBaseChangeEquiv B K L).symm (x : L) = (1 : K) ⊗ₜ[B] x := by
  apply (normalizedCoordinateRingBaseChangeEquiv B K L).injective
  simp [normalizedCoordinateRingBaseChangeEquiv_tmul]

example (x y : K ⊗[B] normalizedCoordinateRing B L) :
    normalizedCoordinateRingBaseChangeEquiv B K L (x * y) =
      normalizedCoordinateRingBaseChangeEquiv B K L x *
        normalizedCoordinateRingBaseChangeEquiv B K L y :=
  (normalizedCoordinateRingBaseChangeEquiv B K L).map_mul x y

-- Compatibility with B is inherited from the original B → K → L tower.
example (b : B) :
    normalizedCoordinateRingBaseChangeEquiv B K L
        ((algebraMap B K b) ⊗ₜ[B] (1 : normalizedCoordinateRing B L)) = algebraMap B L b := by
  rw [normalizedCoordinateRingBaseChangeEquiv_tmul]
  simpa using (IsScalarTower.algebraMap_apply B K L b).symm

end OneFactor

section MarkedTensor

variable {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable (D : NormalClosureData K L N)

example :
    (K ⊗[B] (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L)) ≃ₐ[K]
      (⨂[K] _ : L →ₐ[K] N, L) := by
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact D.normalizationTensorBaseChangeEquiv (B := B)

example (k : K) (σ : L →ₐ[K] N) (x : normalizedCoordinateRing B L) :
    D.normalizationTensorBaseChangeEquiv (B := B)
        (k ⊗ₜ[B] PiTensorProduct.singleAlgHom σ x) =
      k • (PiTensorProduct.singleAlgHom σ (x : L) : ⨂[K] _ : L →ₐ[K] N, L) :=
  D.normalizationTensorBaseChangeEquiv_tmul_singleAlgHom (B := B) k σ x

example (k : K) (x : (L →ₐ[K] N) → normalizedCoordinateRing B L) :
    D.normalizationTensorBaseChangeEquiv (B := B) (k ⊗ₜ[B] PiTensorProduct.tprod B x) =
      k • PiTensorProduct.tprod K (fun σ => (x σ : L)) :=
  D.normalizationTensorBaseChangeEquiv_tmul_tprod (B := B) k x

-- This is equality of the full K-algebra maps, not just pure-tensor agreement.
example :
    letI : FiniteDimensional K N := D.finiteNormal
    D.tensorEvaluation.comp (D.normalizationTensorBaseChangeEquiv (B := B)).toAlgHom =
      (normalizedCoordinateRingBaseChangeEquiv B K N).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K K) (D.normalizationTensorEvaluation (B := B))) :=
  D.normalizationTensorEvaluation_baseChange (B := B)

example (k : K) (x : ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) :
    D.tensorEvaluation (D.normalizationTensorBaseChangeEquiv (B := B) (k ⊗ₜ[B] x)) =
      algebraMap K N k * (D.normalizationTensorEvaluation (B := B) x : N) := by
  letI : FiniteDimensional K N := D.finiteNormal
  have h := DFunLike.congr_fun (D.normalizationTensorEvaluation_baseChange (B := B))
    (k ⊗ₜ[B] x)
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h
  change D.tensorEvaluation (D.normalizationTensorBaseChangeEquiv (B := B) (k ⊗ₜ[B] x)) =
    normalizedCoordinateRingBaseChangeEquiv B K N
      (k ⊗ₜ[B] D.normalizationTensorEvaluation (B := B) x) at h
  rw [normalizedCoordinateRingBaseChangeEquiv_tmul] at h
  exact h

end MarkedTensor

section ActualFunctionField

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)

-- The intermediate field uses the actual pullback to the actual inverse
-- image, followed by its generic germ, with compatibility proved in SP72.
example :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Nonempty ((X.functionField ⊗[Γ(X, U)] normalizedCoordinateRing Γ(X, U) Y.functionField)
      ≃ₐ[X.functionField] Y.functionField) := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : FiniteDimensional X.functionField Y.functionField :=
    functionFieldMapOfDominant_finiteDimensional p
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  exact ⟨normalizedCoordinateRingBaseChangeEquiv Γ(X, U) X.functionField Y.functionField⟩

example :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    let D := functionFieldNormalClosureData p
    letI : FiniteDimensional X.functionField N := D.finiteNormal
    D.tensorEvaluation.comp (D.normalizationTensorBaseChangeEquiv (B := Γ(X, U))).toAlgHom =
      (normalizedCoordinateRingBaseChangeEquiv Γ(X, U) X.functionField N).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id X.functionField X.functionField)
          (D.normalizationTensorEvaluation (B := Γ(X, U)))) := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact (functionFieldNormalClosureData p).normalizationTensorEvaluation_baseChange (B := Γ(X, U))

-- The actual base scalar still passes through X's generic germ, not a new
-- choice of the field inclusion induced by the tensor comparison.
example (b : Γ(X, U)) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : FiniteDimensional X.functionField N := (functionFieldNormalClosureData p).finiteNormal
    normalizedCoordinateRingBaseChangeEquiv Γ(X, U) X.functionField N
        ((X.germToFunctionField U b) ⊗ₜ[Γ(X, U)] (1 : normalizedCoordinateRing Γ(X, U) N)) =
      algebraMap Γ(X, U) N b := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : FiniteDimensional X.functionField N := (functionFieldNormalClosureData p).finiteNormal
  simp only [normalizedCoordinateRingBaseChangeEquiv_tmul, OneMemClass.coe_one, mul_one]
  rfl

end ActualFunctionField

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.piTensorProductCongr,
      `HodgeConjecture.CollisionFoundations.piTensorProductCongr_tprod,
      `HodgeConjecture.CollisionFoundations.piTensorProductCongr_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.piTensorProductBaseChangeEquiv,
      `HodgeConjecture.CollisionFoundations.piTensorProductBaseChangeEquiv_tmul_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.piTensorProductBaseChangeEquiv_symm_singleAlgHom_tmul,
      `HodgeConjecture.CollisionFoundations.piTensorProductBaseChangeEquiv_tmul_tprod,
      `HodgeConjecture.CollisionFoundations.normalizedCoordinateRingBaseChangeEquiv,
      `HodgeConjecture.CollisionFoundations.normalizedCoordinateRingBaseChangeEquiv_tmul,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorBaseChangeEquiv,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorBaseChangeEquiv_tmul_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorBaseChangeEquiv_tmul_tprod,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_baseChange] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
