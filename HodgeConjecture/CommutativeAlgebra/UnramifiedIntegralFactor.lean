module

public import HodgeConjecture.CommutativeAlgebra.SeparabilityTrace
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

@[expose] public section

/-!
# The integral factor selected by an unramified evaluation

The separability tensor of an unramified algebra and the integral field
trace construct a section of its evaluation into an integral closure.
Generic spanning proves that the section is a right inverse. Its value
at one is the integral selecting idempotent. The source need not be a
domain, and no flatness or integral-closedness of that source is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct

universe uB uK uN uS uT

variable {B : Type uB} (K : Type uK) (N : Type uN)
variable {S : Type uS} {T : Type uT}
variable [CommRing B] [Field K] [Field N] [CommRing S] [CommRing T]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K N] [Algebra B N] [IsScalarTower B K N]
variable [Algebra B S] [Algebra B T] [Algebra T N] [IsScalarTower B T N]
variable [IsIntegralClosure T B N] [FiniteDimensional K N]
variable [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S]

/-- The integral trace contracts the unramified section to the original
source algebra. No surjectivity of the evaluation is used to define it. -/
def unramifiedIntegralSection (f : S →ₐ[B] T) : T →ₗ[B] S := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact (((TensorProduct.AlgebraTensorModule.rid B S S).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor S S (Algebra.intTraceAux B K N T))).comp
      (Algebra.FormallyUnramified.sec B S T)).restrictScalars B

/-- The trace section respects the source action through its actual
evaluation into the integral closure. -/
theorem unramifiedIntegralSection_mul (f : S →ₐ[B] T) (s : S) (x : T) :
    unramifiedIntegralSection K N f (f s * x) =
      s * unramifiedIntegralSection K N f x := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact (((TensorProduct.AlgebraTensorModule.rid B S S).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor S S (Algebra.intTraceAux B K N T))).comp
      (Algebra.FormallyUnramified.sec B S T)).map_smul s x

private theorem unramifiedIntegralSection_eq_sum (f : S →ₐ[B] T)
    (a : Finset (S × S))
    (ha : Algebra.FormallyUnramified.elem B S = ∑ p ∈ a, p.1 ⊗ₜ[B] p.2)
    (x : T) :
    unramifiedIntegralSection K N f x =
      ∑ p ∈ a, Algebra.intTraceAux B K N T (f p.2 * x) • p.1 := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  simp [unramifiedIntegralSection, Algebra.FormallyUnramified.sec, ha,
    TensorProduct.AlgebraTensorModule.mapBilinear_apply, Algebra.smul_def]
  rfl

private def integralEvaluationTensorMap (f : S →ₐ[B] T) :
    S ⊗[B] S →ₐ[B] N ⊗[K] N :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : N →ₐ[K] N ⊗[K] N).restrictScalars B).comp
      ((IsScalarTower.toAlgHom B T N).comp f))
    (((Algebra.TensorProduct.includeRight : N →ₐ[K] N ⊗[K] N).restrictScalars B).comp
      ((IsScalarTower.toAlgHom B T N).comp f))
    (fun _ _ => Commute.all _ _)

omit [IsFractionRing B K] [IsIntegrallyClosed B] [IsIntegralClosure T B N]
  [FiniteDimensional K N] [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S] in
@[simp]
private theorem integralEvaluationTensorMap_tmul (f : S →ₐ[B] T) (a b : S) :
    integralEvaluationTensorMap K N f (a ⊗ₜ[B] b) =
      algebraMap T N (f a) ⊗ₜ[K] algebraMap T N (f b) := by
  simp [integralEvaluationTensorMap, Algebra.TensorProduct.tmul_mul_tmul]

omit [IsFractionRing B K] [IsIntegrallyClosed B] [IsIntegralClosure T B N]
  [FiniteDimensional K N] [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S] in
private theorem integralEvaluationTensorMap_lmul (f : S →ₐ[B] T)
    (t : S ⊗[B] S) :
    Algebra.TensorProduct.lmul' K (integralEvaluationTensorMap K N f t) =
      algebraMap T N (f (Algebra.TensorProduct.lmul' B t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp [ha, hb]

omit [IsFractionRing B K] [IsIntegrallyClosed B] [IsIntegralClosure T B N]
  [FiniteDimensional K N] in
private theorem integralEvaluationTensorMap_central (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤)
    (x : N) :
    (1 ⊗ₜ[K] x) * integralEvaluationTensorMap K N f
        (Algebra.FormallyUnramified.elem B S) =
      (x ⊗ₜ[K] 1) * integralEvaluationTensorMap K N f
        (Algebra.FormallyUnramified.elem B S) := by
  have hx : x ∈ Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      simpa using congrArg (integralEvaluationTensorMap K N f)
        (Algebra.FormallyUnramified.one_tmul_mul_elem (R := B) s)
  | zero => simp
  | add x y hx hy hxi hyi =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, add_mul, hxi, hyi]
  | smul k x hx hxi =>
      simpa only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_mul_assoc]
        using congrArg (fun t : N ⊗[K] N => k • t) hxi

omit [Algebra.FormallyUnramified B S] [Algebra.EssFiniteType B S] in
private theorem integralTrace_smul_map (f : S →ₐ[B] T) (x : T) (s : S) :
    algebraMap T N (f (Algebra.intTraceAux B K N T x • s)) =
      Algebra.trace K N (algebraMap T N x) • algebraMap T N (f s) := by
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
  rw [← IsScalarTower.algebraMap_apply B T N,
    IsScalarTower.algebraMap_apply B K N, Algebra.map_intTraceAux]

/-- Generic spanning makes the constructed integral trace section a
right inverse on the entire integral closure. -/
theorem unramifiedIntegralSection_rightInverse (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤)
    (x : T) : f (unramifiedIntegralSection K N f x) = x := by
  classical
  apply IsIntegralClosure.algebraMap_injective T B N
  obtain ⟨a, ha⟩ := TensorProduct.exists_finset (Algebra.FormallyUnramified.elem B S)
  let t := integralEvaluationTensorMap K N f (Algebra.FormallyUnramified.elem B S)
  have ht (y : N) : (1 ⊗ₜ[K] y) * t = (y ⊗ₜ[K] 1) * t :=
    integralEvaluationTensorMap_central K N f hspan y
  have hmul : Algebra.TensorProduct.lmul' K t = 1 := by
    simp [t, integralEvaluationTensorMap_lmul, Algebra.FormallyUnramified.lmul_elem]
  have hvalue : traceContraction K N ((1 ⊗ₜ[K] algebraMap T N x) * t) =
      algebraMap T N x := traceContraction_one_tmul_mul t ht hmul _
  rw [unramifiedIntegralSection_eq_sum K N f a ha]
  simp only [map_sum, integralTrace_smul_map]
  simpa [t, ha, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    mul_comm] using hvalue

/-- The actual unramified evaluation covers the full integral closure. -/
theorem unramifiedIntegralEvaluation_surjective (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤) :
    Function.Surjective f :=
  fun x => ⟨unramifiedIntegralSection K N f x,
    unramifiedIntegralSection_rightInverse K N f hspan x⟩

/-- The integral selecting element is the trace section evaluated at one. -/
def unramifiedIntegralIdempotent (f : S →ₐ[B] T) : S :=
  unramifiedIntegralSection K N f 1

/-- The selecting element evaluates to one in the integral closure. -/
@[simp]
theorem unramifiedIntegralIdempotent_map (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤) :
    f (unramifiedIntegralIdempotent K N f) = 1 :=
  unramifiedIntegralSection_rightInverse K N f hspan 1

/-- Multiplication by the integral selector is the section after evaluation. -/
theorem unramifiedIntegralIdempotent_mul (f : S →ₐ[B] T) (s : S) :
    unramifiedIntegralIdempotent K N f * s = unramifiedIntegralSection K N f (f s) := by
  simpa [unramifiedIntegralIdempotent, mul_comm] using
    (unramifiedIntegralSection_mul K N f s 1).symm

/-- After base change, multiplication by the same integral selector is
still the trace section after the actual base-changed evaluation. -/
theorem unramifiedIntegralIdempotent_baseChange_mul (f : S →ₐ[B] T)
    (x : K ⊗[B] S) :
    ((1 : K) ⊗ₜ[B] unramifiedIntegralIdempotent K N f) * x =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K)
        (unramifiedIntegralSection K N f)
        (Algebra.TensorProduct.map (AlgHom.id K K) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k s =>
      simp [Algebra.TensorProduct.tmul_mul_tmul, unramifiedIntegralIdempotent_mul]
  | add x y hx hy => simp [mul_add, hx, hy]

/-- The trace section constructs an idempotent over the whole base ring. -/
theorem unramifiedIntegralIdempotent_isIdempotentElem (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤) :
    IsIdempotentElem (unramifiedIntegralIdempotent K N f) := by
  change unramifiedIntegralIdempotent K N f * unramifiedIntegralIdempotent K N f = _
  rw [unramifiedIntegralIdempotent_mul, unramifiedIntegralIdempotent_map K N f hspan]
  rfl

/-- The integral selector annihilates exactly the actual evaluation kernel. -/
theorem unramifiedIntegralIdempotent_mul_eq_zero_iff (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤)
    (s : S) : unramifiedIntegralIdempotent K N f * s = 0 ↔ f s = 0 := by
  constructor
  · intro hs
    have := congrArg f hs
    simpa [unramifiedIntegralIdempotent_map K N f hspan] using this
  · intro hs
    rw [unramifiedIntegralIdempotent_mul, hs, map_zero]

/-- The complementary idempotent generates the integral evaluation kernel. -/
theorem unramifiedIntegralEvaluation_ker_eq_span_one_sub (f : S →ₐ[B] T)
    (hspan : Submodule.span K (Set.range (fun s : S => algebraMap T N (f s))) = ⊤) :
    RingHom.ker f.toRingHom = Ideal.span {1 - unramifiedIntegralIdempotent K N f} := by
  apply le_antisymm
  · intro s hs
    have hz := (unramifiedIntegralIdempotent_mul_eq_zero_iff K N f hspan s).mpr hs
    have heq : s = (1 - unramifiedIntegralIdempotent K N f) * s := by
      rw [sub_mul, one_mul, hz, sub_zero]
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro s hs
    have heq : s = 1 - unramifiedIntegralIdempotent K N f := by simpa using hs
    subst s
    change f (1 - unramifiedIntegralIdempotent K N f) = 0
    simp [unramifiedIntegralIdempotent_map K N f hspan]

end

end HodgeConjecture.CollisionFoundations
