import HodgeConjecture.Cycles.PrincipalDivisor
import HodgeConjecture.Cycles.IsomorphismTransport
import HodgeConjecture.Cycles.OpenSupport

/-!
# Actual open restriction and isomorphism transport of principal divisors

The existing closed-immersion pushforward carries the principal divisor
of the actual function-field pullback to the original principal divisor.
The proof compares coefficients at actual image supports, using the proved
codimension and local-order transport. The existing open restriction gives
the corresponding pullback identity. More generally, restriction through
an integral open immersion commutes with principal divisors: the actual
reduced-closure coefficient formula and the local-order comparison prove
the identity. Source local Noetherianity and quasi-compactness are derived
from the corresponding target hypotheses.

These are identities in the existing ungraded finite-cycle module. They
do not introduce rational-equivalence relations or a Chow quotient.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The local-order comparison on actual prime supports uses reduced
ambient closure, not a closed-image operation on the open immersion. -/
theorem primeDivisorOrder_openImmersion {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (Z : PrimeDivisor X) (f : Y.functionFieldˣ) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
    primeDivisorOrder X Z
        (Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom f) =
      primeDivisorOrder Y
        ⟨openClosureSubscheme j Z.val,
          (supportCodimension_openClosureSubscheme j Z.val).trans Z.property⟩ f := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  have hpoint : (divisorPointEquivPrimeDivisor Y).symm
      ⟨openClosureSubscheme j Z.val,
        (supportCodimension_openClosureSubscheme j Z.val).trans Z.property⟩ =
      divisorPointEmbedding j ((divisorPointEquivPrimeDivisor X).symm Z) := by
    apply Subtype.ext
    simp only [divisorPointEquivPrimeDivisor_symm_val, divisorPointEmbedding_val,
      openClosureSubscheme_ambientGenericPoint]
  unfold primeDivisorOrder
  rw [hpoint]
  exact divisorOrder_openImmersion j ((divisorPointEquivPrimeDivisor X).symm Z) f

/-- Actual open restriction commutes with the finite principal-divisor
construction. The locally Noetherian, quasi-compact target supplies both
source finiteness instances; none is silently assumed for arbitrary opens. -/
theorem openRestriction_principalDivisor_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (f : Y.functionFieldˣ) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j
    openRestriction ℤ j (principalDivisor Y f) =
      principalDivisor X
        (Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom f) := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j
  apply Finsupp.ext
  intro W
  rw [openRestriction_apply]
  by_cases hW : supportCodimension W = 1
  · rw [principalDivisor_apply_prime X _ ⟨W, hW⟩,
      primeDivisorOrder_openImmersion j ⟨W, hW⟩ f]
    exact principalDivisor_apply_prime Y f
      ⟨openClosureSubscheme j W, (supportCodimension_openClosureSubscheme j W).trans hW⟩
  · have hC : supportCodimension (openClosureSubscheme j W) ≠ 1 := by
      simpa only [supportCodimension_openClosureSubscheme] using hW
    rw [principalDivisor_apply_of_not_prime Y f _ hC,
      principalDivisor_apply_of_not_prime X _ W hW]

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
      principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f) :=
  openRestriction_principalDivisor_of_isOpenImmersion e.hom f

end

end HodgeConjecture.SchemeCycles
