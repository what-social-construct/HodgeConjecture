module

import HodgeConjecture.Boundary.Normalization.NormalizationIntegralFactor
import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import Mathlib.Algebra.Ring.Fin
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP80 regressions for the integral normal-closure factor.
Run with `lake env lean research/NormalizationIntegralFactorVerification.lean`.

The trace calculation works for commutative finite-dimensional algebras.
The integral construction does not assume the source is flat, a domain, or
normal; the base need not be Noetherian. Identity and both product projections
test the actual section, including its nonunital value at one. The marked
tests retain the existing integral evaluation, complementary kernel ideal,
and SP79 selector under the existing generic comparison. The scheme case
derives chart algebras from a finite étale map and normal stalks. All 28 new
public declarations have an enforced, duplicate-free standard-three audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open HodgeConjecture.CollisionFoundations
open scoped TensorProduct Classical

noncomputable section

universe u uB uK uN uS uT uA

section Trace

variable {K : Type uK} {Q : Type uA} [Field K] [CommRing Q] [Algebra K Q]
variable [FiniteDimensional K Q] (t : Q ⊗[K] Q)
variable (hc : ∀ x : Q, (1 ⊗ₜ[K] x) * t = (x ⊗ₜ[K] 1) * t)

example : traceContraction K Q t = Algebra.TensorProduct.lmul' K t := by
  fail_if_success have _ : Field Q := inferInstance
  exact traceContraction_eq_lmul_of_central t hc

example (hm : Algebra.TensorProduct.lmul' K t = 1) (x : Q) :
    traceContraction K Q ((1 ⊗ₜ[K] x) * t) = x :=
  traceContraction_one_tmul_mul t hc hm x

example (hm : Algebra.TensorProduct.lmul' K t = 1) : traceContraction K Q t = 1 :=
  traceContraction_eq_one_of_central t hc hm

example (K : Type uK) [Field K] (x : K) :
    traceContraction K K ((1 : K) ⊗ₜ[K] x) = x := by
  simp

-- The product algebra is not a field. Its two diagonal summands both
-- contribute to the trace contraction.
example : traceContraction ℚ (ℚ × ℚ)
    (((1, 0) : ℚ × ℚ) ⊗ₜ[ℚ] (1, 0) + ((0, 1) : ℚ × ℚ) ⊗ₜ[ℚ] (0, 1)) = 1 := by
  simp [Algebra.trace_prod_apply, Prod.ext_iff]

end Trace

section GenericIntegralFactor

variable {B : Type uB} {K : Type uK} {N : Type uN} {S : Type uS} {T : Type uT}
variable [CommRing B] [Field K] [Field N] [CommRing S] [CommRing T]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K N] [Algebra B N] [IsScalarTower B K N]
variable [Algebra B S] [Algebra B T] [Algebra T N] [IsScalarTower B T N]
variable [IsIntegralClosure T B N] [FiniteDimensional K N]
variable [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S]
variable (f : S →ₐ[B] T)
variable (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤)

example : Function.Surjective f := by
  fail_if_success have _ : Module.Flat B S := inferInstance
  fail_if_success have _ : IsDomain S := inferInstance
  fail_if_success have _ : IsIntegrallyClosed S := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K N := inferInstance
  exact unramifiedIntegralEvaluation_surjective K N f hspan

example (s : S) (x : T) :
    unramifiedIntegralSection K N f (f s * x) = s * unramifiedIntegralSection K N f x :=
  unramifiedIntegralSection_mul K N f s x

example (x : T) : f (unramifiedIntegralSection K N f x) = x :=
  unramifiedIntegralSection_rightInverse K N f hspan x

example : unramifiedIntegralSection K N f 1 = unramifiedIntegralIdempotent K N f := rfl

example : IsIdempotentElem (unramifiedIntegralIdempotent K N f) :=
  unramifiedIntegralIdempotent_isIdempotentElem K N f hspan

example (s : S) : unramifiedIntegralIdempotent K N f * s = 0 ↔ f s = 0 :=
  unramifiedIntegralIdempotent_mul_eq_zero_iff K N f hspan s

example : f (1 - unramifiedIntegralIdempotent K N f) = 0 := by
  simp [unramifiedIntegralIdempotent_map K N f hspan]

example : RingHom.ker f.toRingHom = Ideal.span {unramifiedIntegralIdempotent K N f - 1} := by
  rw [unramifiedIntegralEvaluation_ker_eq_span_one_sub K N f hspan,
    ← neg_sub, Ideal.span_singleton_neg]

example (x : K ⊗[B] S) :
    ((1 : K) ⊗ₜ[B] unramifiedIntegralIdempotent K N f) * x =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K)
        (unramifiedIntegralSection K N f)
        (Algebra.TensorProduct.map (AlgHom.id K K) f x) :=
  unramifiedIntegralIdempotent_baseChange_mul K N f x

end GenericIntegralFactor

private theorem fieldEvaluationSpan {K : Type uK} {S : Type uS}
    [Field K] [CommRing S] [Algebra K S] (f : S →ₐ[K] K) (hf : Function.Surjective f) :
    Submodule.span K (Set.range (fun s : S => algebraMap K K (f s))) = ⊤ := by
  change Submodule.span K (Set.range f) = ⊤
  rw [Set.range_eq_univ.mpr hf, Submodule.span_univ]

example (K : Type uK) [Field K] (x : K) :
    unramifiedIntegralSection K K (AlgHom.id K K) x = x := by
  exact unramifiedIntegralSection_rightInverse K K (AlgHom.id K K)
    (fieldEvaluationSpan _ Function.surjective_id) x

section ProductProjections

local instance : Algebra.FormallyUnramified ℚ (ℚ × ℚ) := by
  let e : (Fin 2 → ℚ) ≃ₐ[ℚ] (ℚ × ℚ) :=
    { RingEquiv.piFinTwo (fun _ => ℚ) with commutes' := fun _ => rfl }
  exact Algebra.FormallyUnramified.of_equiv e

private theorem fstIntegralSelector :
    unramifiedIntegralIdempotent ℚ ℚ (AlgHom.fst ℚ ℚ ℚ) = (1, 0) := by
  let f := AlgHom.fst ℚ ℚ ℚ
  have hs := fieldEvaluationSpan f (fun x => ⟨(x, 0), rfl⟩)
  have h₁ := unramifiedIntegralIdempotent_map ℚ ℚ f hs
  have h₂ := (unramifiedIntegralIdempotent_mul_eq_zero_iff ℚ ℚ f hs (0, 1)).mpr rfl
  apply Prod.ext
  · exact h₁
  · simpa using congrArg Prod.snd h₂

private theorem sndIntegralSelector :
    unramifiedIntegralIdempotent ℚ ℚ (AlgHom.snd ℚ ℚ ℚ) = (0, 1) := by
  let f := AlgHom.snd ℚ ℚ ℚ
  have hs := fieldEvaluationSpan f (fun x => ⟨(0, x), rfl⟩)
  have h₁ := unramifiedIntegralIdempotent_map ℚ ℚ f hs
  have h₂ := (unramifiedIntegralIdempotent_mul_eq_zero_iff ℚ ℚ f hs (1, 0)).mpr rfl
  apply Prod.ext
  · simpa using congrArg Prod.fst h₂
  · exact h₁

example (x : ℚ) : unramifiedIntegralSection ℚ ℚ (AlgHom.fst ℚ ℚ ℚ) x = (x, 0) := by
  have h := unramifiedIntegralIdempotent_mul ℚ ℚ (AlgHom.fst ℚ ℚ ℚ) (x, 0)
  simpa [fstIntegralSelector] using h.symm

example (x : ℚ) : unramifiedIntegralSection ℚ ℚ (AlgHom.snd ℚ ℚ ℚ) x = (0, x) := by
  have h := unramifiedIntegralIdempotent_mul ℚ ℚ (AlgHom.snd ℚ ℚ ℚ) (0, x)
  simpa [sndIntegralSelector] using h.symm

example : unramifiedIntegralSection ℚ ℚ (AlgHom.fst ℚ ℚ ℚ) 1 ≠ 1 := by
  change unramifiedIntegralIdempotent ℚ ℚ (AlgHom.fst ℚ ℚ ℚ) ≠ 1
  rw [fstIntegralSelector]
  intro h
  have hz : (0 : ℚ) = 1 := congrArg Prod.snd h
  exact zero_ne_one hz

example : RingHom.ker (AlgHom.fst ℚ ℚ ℚ).toRingHom = Ideal.span {((0, 1) : ℚ × ℚ)} := by
  have hc : (1 : ℚ × ℚ) - (1, 0) = (0, 1) := by ext <;> simp
  rw [unramifiedIntegralEvaluation_ker_eq_span_one_sub ℚ ℚ (AlgHom.fst ℚ ℚ ℚ)
    (fieldEvaluationSpan _ (fun x => ⟨(x, 0), rfl⟩)), fstIntegralSelector, hc]

example : RingHom.ker (AlgHom.snd ℚ ℚ ℚ).toRingHom = Ideal.span {((1, 0) : ℚ × ℚ)} := by
  have hc : (1 : ℚ × ℚ) - (0, 1) = (1, 0) := by ext <;> simp
  rw [unramifiedIntegralEvaluation_ker_eq_span_one_sub ℚ ℚ (AlgHom.snd ℚ ℚ ℚ)
    (fieldEvaluationSpan _ (fun x => ⟨(0, x), rfl⟩)), sndIntegralSelector, hc]

end ProductProjections

section ActualNormalEtaleModel

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N] [CommRing A]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [Algebra B A] [Algebra A L] [IsScalarTower B A L]
variable [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]
variable [Algebra.Etale B A] (D : NormalClosureData K L N)

example : Function.Surjective (D.normalizationTensorEvaluation (B := B)) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact D.normalizationTensorEvaluation_surjective (B := B) (A := A)

example : Submodule.span K (Set.range fun x =>
    ((D.normalizationTensorEvaluation (B := B) x : normalizedCoordinateRing B N) : N)) = ⊤ :=
  D.normalizationTensorEvaluation_span (B := B)

example (x : normalizedCoordinateRing B N) :
    D.normalizationTensorEvaluation (D.normalizationTensorSection (B := B) (A := A) x) = x :=
  D.normalizationTensorSection_rightInverse (B := B) (A := A) x

example (s : ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L)
    (x : normalizedCoordinateRing B N) :
    D.normalizationTensorSection (B := B) (A := A) (D.normalizationTensorEvaluation s * x) =
      s * D.normalizationTensorSection (B := B) (A := A) x :=
  D.normalizationTensorSection_mul (B := B) (A := A) s x

example : IsIdempotentElem (D.normalizationTensorIdempotent (B := B) (A := A)) ∧
    D.normalizationTensorEvaluation (D.normalizationTensorIdempotent (B := B) (A := A)) = 1 ∧
    (∀ x, D.normalizationTensorIdempotent (B := B) (A := A) * x = 0 ↔
      D.normalizationTensorEvaluation x = 0) ∧
    RingHom.ker (D.normalizationTensorEvaluation (B := B)).toRingHom =
      Ideal.span {1 - D.normalizationTensorIdempotent (B := B) (A := A)} :=
  D.normalizationTensorIdempotent_spec (B := B) (A := A)

example (x : ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) :
    D.normalizationTensorQuotientEquiv (B := B) (A := A) (Ideal.Quotient.mk _ x) =
      D.normalizationTensorEvaluation x :=
  D.normalizationTensorQuotientEquiv_mk (B := B) (A := A) x

example : Module.Finite B (normalizedCoordinateRing B N) ∧
    Algebra.Etale B (normalizedCoordinateRing B N) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact ⟨D.normalization_finite_of_etaleModel (B := B) (A := A),
    D.normalization_etale_of_etaleModel (B := B) (A := A)⟩

example [Algebra.IsSeparable K L] :
    D.normalizationTensorBaseChangeEquiv (B := B)
        ((1 : K) ⊗ₜ[B] D.normalizationTensorIdempotent (B := B) (A := A)) =
      D.tensorEvaluationIdempotent :=
  D.normalizationTensorIdempotent_baseChange (B := B) (A := A)

example [Algebra.IsSeparable K L] :
    D.normalizationTensorBaseChangeEquiv (B := B)
        ((1 : K) ⊗ₜ[B] (1 - D.normalizationTensorIdempotent (B := B) (A := A))) =
      1 - D.tensorEvaluationIdempotent := by
  rw [TensorProduct.tmul_sub, map_sub,
    D.normalizationTensorIdempotent_baseChange (B := B) (A := A)]
  exact congrArg (fun z => z - D.tensorEvaluationIdempotent)
    (D.normalizationTensorBaseChangeEquiv (B := B)).toRingHom.map_one

end ActualNormalEtaleModel

section ActualFiniteEtaleScheme

open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCycles

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [Etale p]
variable (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)

example
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) ∧
      Algebra.Etale Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Γ(X, U) :=
    HodgeConjecture.NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks hU hX
  letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ U) :=
    HodgeConjecture.NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks
      (hU.preimage p) hY
  letI : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_moduleFinite p U hU
  letI : Algebra.Etale Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_etale p U hU
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact ⟨(functionFieldNormalClosureData p).normalization_finite_of_etaleModel
      (B := Γ(X, U)) (A := Γ(Y, p ⁻¹ᵁ U)),
    (functionFieldNormalClosureData p).normalization_etale_of_etaleModel
      (B := Γ(X, U)) (A := Γ(Y, p ⁻¹ᵁ U))⟩

end ActualFiniteEtaleScheme

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.traceContraction,
    `HodgeConjecture.CollisionFoundations.traceContraction_tmul,
    `HodgeConjecture.CollisionFoundations.traceContraction_eq_lmul_of_central,
    `HodgeConjecture.CollisionFoundations.traceContraction_eq_one_of_central,
    `HodgeConjecture.CollisionFoundations.traceContraction_one_tmul_mul,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralSection,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralSection_mul,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralSection_rightInverse,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralEvaluation_surjective,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent_map,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent_mul,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent_baseChange_mul,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent_isIdempotentElem,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralIdempotent_mul_eq_zero_iff,
    `HodgeConjecture.CollisionFoundations.unramifiedIntegralEvaluation_ker_eq_span_one_sub,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_span,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorSection,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorSection_mul,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorSection_rightInverse,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_surjective,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorIdempotent,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorIdempotent_spec,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorIdempotent_baseChange,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorQuotientEquiv,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorQuotientEquiv_mk,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalization_finite_of_etaleModel,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalization_etale_of_etaleModel]
  unless declarations.length == 28 do
    throwError "Expected exactly 28 SP80 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP80 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
  logInfo "PASS SP80 audit registry: 28 distinct public declarations"
