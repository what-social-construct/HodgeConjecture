import HodgeConjecture.Cycles.RationalChowPushforward
import HodgeConjecture.Cycles.ChowIsomorphism

/-!
# Scheme isomorphisms on rational Chow groups

Scalar extension of the existing integral Chow isomorphism agrees with
the actual rational closed pushforward. Its inverse on rational cycle
representatives is the existing geometric open restriction. No new
carrier, degree comparison, or inverse cycle operation is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TensorProduct

noncomputable section

universe u

/-- Scalar extension of the existing integral Chow isomorphism, in the
actual rational-cycle quotient models. -/
def rationalChowIsoEquiv {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    RationalChowGroup (δ.comapClosedImmersion e.hom) n ≃ₗ[ℚ] RationalChowGroup δ n :=
  (chowRationalizationEquiv (δ.comapClosedImmersion e.hom) n).symm.trans
    ((LinearEquiv.baseChange ℤ ℚ _ _ (chowIsoEquiv δ e n)).trans
      (chowRationalizationEquiv δ n))

/-- The rational isomorphism commutes with the existing tensor comparisons. -/
theorem rationalChowIsoEquiv_chowRationalizationEquiv
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (t : ℚ ⊗[ℤ] ChowGroup (δ.comapClosedImmersion e.hom) n) :
    rationalChowIsoEquiv δ e n
        (chowRationalizationEquiv (δ.comapClosedImmersion e.hom) n t) =
      chowRationalizationEquiv δ n
        (LinearEquiv.baseChange ℤ ℚ _ _ (chowIsoEquiv δ e n) t) := by
  simp only [rationalChowIsoEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- This scalar-extended isomorphism is the actual rational closed pushforward. -/
theorem rationalChowIsoEquiv_toLinearMap
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    (rationalChowIsoEquiv δ e n).toLinearMap =
      rationalChowClosedImmersionPushforward (δ.comapClosedImmersion e.hom) δ e.hom
        (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n := by
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := (chowRationalizationEquiv (δ.comapClosedImmersion e.hom) n).surjective z
  change rationalChowIsoEquiv δ e n
    (chowRationalizationEquiv (δ.comapClosedImmersion e.hom) n t) = _
  rw [rationalChowIsoEquiv_chowRationalizationEquiv]
  exact (rationalChowClosedImmersionPushforward_chowRationalizationEquiv
    (δ.comapClosedImmersion e.hom) δ e.hom
    (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n t).symm

@[simp]
theorem rationalChowIsoEquiv_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℚ (δ.comapClosedImmersion e.hom) n) :
    rationalChowIsoEquiv δ e n (rationalClassMap (δ.comapClosedImmersion e.hom) n c) =
      rationalClassMap δ n
        (gradedClosedImmersionPushforwardWithCoefficients ℚ (δ.comapClosedImmersion e.hom)
          δ e.hom (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n c) := by
  change (rationalChowIsoEquiv δ e n).toLinearMap _ = _
  rw [rationalChowIsoEquiv_toLinearMap]
  rfl

/-- The inverse on actual rational representatives is geometric open restriction. -/
@[simp]
theorem rationalChowIsoEquiv_symm_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℚ δ n) :
    (rationalChowIsoEquiv δ e n).symm (rationalClassMap δ n c) =
      rationalClassMap (δ.comapClosedImmersion e.hom) n
        ⟨openRestriction ℚ e.hom c.val,
          openRestriction_iso_mem_cyclesOfDegree ℚ δ e n c.val c.property⟩ := by
  apply (rationalChowIsoEquiv δ e n).injective
  rw [LinearEquiv.apply_symm_apply, rationalChowIsoEquiv_classMap]
  congr 1
  apply Subtype.ext
  change c.val = closedImmersionPushforward ℚ e.hom (openRestriction ℚ e.hom c.val)
  rw [openRestriction_iso_eq_pushforward_inv]
  change c.val = ((closedImmersionPushforward ℚ e.hom).comp
    (closedImmersionPushforward ℚ e.inv)) c.val
  rw [closedImmersionPushforward_comp]
  simp only [Iso.inv_hom_id, closedImmersionPushforward_id, LinearMap.id_apply]

/-- Integral-to-rational Chow classes commute with the actual scheme isomorphism. -/
theorem rationalChowIsoEquiv_chowRationalize
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (z : ChowGroup (δ.comapClosedImmersion e.hom) n) :
    rationalChowIsoEquiv δ e n (chowRationalize (δ.comapClosedImmersion e.hom) n z) =
      chowRationalize δ n (chowIsoEquiv δ e n z) := by
  change (rationalChowIsoEquiv δ e n).toLinearMap _ = _
  rw [rationalChowIsoEquiv_toLinearMap]
  exact rationalChowClosedImmersionPushforward_chowRationalize
    (δ.comapClosedImmersion e.hom) δ e.hom
    (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n z

end

end HodgeConjecture.SchemeCycles
