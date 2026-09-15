import HodgeConjecture.Cycles.PrincipalDivisor
import HodgeConjecture.Cycles.IsomorphismTransport

/-!
# Actual isomorphism transport of principal-divisor cycles

The existing closed-immersion pushforward carries the principal divisor
of the actual function-field pullback to the original principal divisor.
The proof compares coefficients at actual image supports, using the proved
codimension and local-order transport. The existing open restriction gives
the corresponding pullback identity through the inverse isomorphism.

These are identities in the existing ungraded finite-cycle module. They
do not introduce rational-equivalence relations or a Chow quotient.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Principal divisors commute with pushforward through an actual scheme
isomorphism and its contravariant map on actual function fields. -/
theorem principalDivisor_iso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (f : Y.functionFieldˣ) :
    closedImmersionPushforward ℤ e.hom
      (principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f)) =
      principalDivisor Y f := by
  apply Finsupp.ext
  intro W
  obtain ⟨Z, rfl⟩ := (closedImageSubschemeEquiv e).surjective W
  rw [closedImageSubschemeEquiv_apply, closedImmersionPushforward_iso_apply_image]
  by_cases hZ : supportCodimension Z = 1
  · rw [principalDivisor_apply_prime X _ ⟨Z, hZ⟩,
      primeDivisorOrder_iso e ⟨Z, hZ⟩ f]
    simpa only [primeDivisorEquiv_val] using
      (principalDivisor_apply_prime Y f (primeDivisorEquiv e ⟨Z, hZ⟩)).symm
  · have hW : supportCodimension (closedImageSubscheme e.hom Z) ≠ 1 := by
      simpa only [supportCodimension_iso] using hZ
    rw [principalDivisor_apply_of_not_prime X _ Z hZ,
      principalDivisor_apply_of_not_prime Y f _ hW]

/-- The existing geometric open restriction, specialized to an isomorphism,
pulls back the principal divisor by the actual function-field map. -/
theorem openRestriction_principalDivisor {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (f : Y.functionFieldˣ) :
    openRestriction ℤ e.hom (principalDivisor Y f) =
      principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f) := by
  rw [openRestriction_iso_eq_pushforward_inv, ← principalDivisor_iso e f]
  change ((closedImmersionPushforward ℤ e.inv).comp
    (closedImmersionPushforward ℤ e.hom)) _ = _
  rw [closedImmersionPushforward_comp]
  simp only [Iso.hom_inv_id, closedImmersionPushforward_id, LinearMap.id_apply]

end

end HodgeConjecture.SchemeCycles
