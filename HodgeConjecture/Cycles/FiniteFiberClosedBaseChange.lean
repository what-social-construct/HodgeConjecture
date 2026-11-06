module

public import HodgeConjecture.Cycles.FiberMultiplicityLocal
public import HodgeConjecture.Cycles.OpenClosedLocalization
public import HodgeConjecture.CommutativeAlgebra.QuotientLengthBaseChange

@[expose] public section

/-! Actual finite-fiber multiplicities and cycle pullback in a closed
base-change square. The multiplicity comparison is proved from stalk
kernels and quotient lengths. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v

/-- Closed base change preserves the actual local scheme-fiber multiplicity. -/
theorem finiteFiberMultiplicity_pullback_closed {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i] (z : (pullback f i : Scheme.{u})) :
    finiteFiberMultiplicity (pullback.snd f i) z =
      finiteFiberMultiplicity f (pullback.fst f i z) := by
  let p := pullback.fst f i
  let q := pullback.snd f i
  let h : (p ≫ f) z = (q ≫ i) z :=
    congrArg (fun k : pullback f i ⟶ Y ↦ k z) pullback.condition
  let A := Y.presheaf.stalk ((p ≫ f) z)
  let A' := Z.presheaf.stalk (q z)
  let B := X.presheaf.stalk (p z)
  let B' := (pullback f i).presheaf.stalk z
  let α : A →+* B := (f.stalkMap (p z)).hom
  let β : A' →+* B' := (q.stalkMap z).hom
  let φ : A →+* A' := (eqToHom (congrArg Y.presheaf.stalk h) ≫ i.stalkMap (q z)).hom
  let ψ : B →+* B' := (p.stalkMap z).hom
  have hφ : Function.Surjective φ := (i.stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg Y.presheaf.stalk h))).2
  letI : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  have hψ : Function.Surjective ψ := p.stalkMap_surjective z
  have hcomm : ψ.comp α = β.comp φ := by
    have e := Scheme.Hom.stalkMap_congr_hom (p ≫ f) (q ≫ i) pullback.condition z
    rw [stalkCongr_of_eq Y.presheaf h, Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_comp] at e
    ext a
    exact congrArg (fun m : A ⟶ B' ↦ m.hom a)
      (e.trans (Category.assoc _ _ _).symm)
  have hker : RingHom.ker ψ = (RingHom.ker φ).map α :=
    pullback_fst_stalkMap_ker f i z
  have hlen := closedFiber_length_of_quotient_square α β φ ψ hφ hψ hcomm hker
  rw [finiteFiberMultiplicity_eq_length_quotient, finiteFiberMultiplicity_eq_length_quotient]
  exact (congrArg ENat.toNat hlen).symm

/-- Closed pushforward has zero coefficient away from its actual closed image. -/
theorem closedImmersionPushforward_apply_point_of_not_mem_range
    (R : Type v) [Semiring R] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (c : Cycles Z R) (x : X)
    (hx : x ∉ Set.range i.base) :
    closedImmersionPushforward R i c (pointSupport X x) = 0 := by
  have hc : closedImmersionPushforward R i c ∈
      Finsupp.supported R R {W | ambientGenericPoint W ∈ Set.range i.base} := by
    rw [← range_closedImmersionPushforward R i]
    exact LinearMap.mem_range_self _ c
  rw [Finsupp.mem_supported'] at hc
  exact hc _ (by simpa only [Set.mem_ofPred_eq, ambientGenericPoint_pointSupport] using hx)

/-- The existing finite-fiber cycle pullback commutes with the existing closed
pushforward in its actual scheme pullback square. Flatness is unnecessary for this
coefficient identity. -/
theorem finiteFiberPullback_closedImmersionPushforward
    (R : Type v) [Semiring R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (i : Z ⟶ Y) [IsClosedImmersion i] (c : Cycles Z R) :
    finiteFiberPullback f R (closedImmersionPushforward R i c) =
      closedImmersionPushforward R (pullback.fst f i)
        (finiteFiberPullback (pullback.snd f i) R c) := by
  classical
  apply Finsupp.ext
  intro W
  rw [← pointSupport_ambientGenericPoint W]
  let x := ambientGenericPoint W
  change finiteFiberPullback f R (closedImmersionPushforward R i c) (pointSupport X x) =
    closedImmersionPushforward R (pullback.fst f i)
      (finiteFiberPullback (pullback.snd f i) R c) (pointSupport X x)
  by_cases hx : x ∈ Set.range (pullback.fst f i).base
  · obtain ⟨z, hz⟩ := hx
    rw [← hz, finiteFiberPullback_apply_pointSupport,
      ← closedImage_pointSupport (pullback.fst f i) z,
      closedImmersionPushforward_apply_image, finiteFiberPullback_apply_pointSupport,
      finiteFiberMultiplicity_pullback_closed]
    have hpt : i.base (pullback.snd f i z) = f.base (pullback.fst f i z) :=
      (congrArg (fun k : pullback f i ⟶ Y ↦ k.base z) pullback.condition).symm
    rw [← hpt, ← closedImage_pointSupport i (pullback.snd f i z),
      closedImmersionPushforward_apply_image]
  · have hy : f.base x ∉ Set.range i.base := by
      intro hy
      apply hx
      rw [Scheme.Pullback.range_fst]
      exact hy
    rw [finiteFiberPullback_apply_pointSupport,
      closedImmersionPushforward_apply_point_of_not_mem_range R i c (f.base x) hy,
      zero_mul,
      closedImmersionPushforward_apply_point_of_not_mem_range R (pullback.fst f i) _ x hx]

end

end HodgeConjecture.SchemeCycles
