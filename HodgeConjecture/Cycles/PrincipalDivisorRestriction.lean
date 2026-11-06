module

public import HodgeConjecture.Cycles.PrincipalDivisorImage
public import HodgeConjecture.Cycles.OpenClosedBaseChange

@[expose] public section

/-!
# Open restriction of actual ambient principal divisors

The existing ambient principal divisor restricts to the ambient principal
divisor of the actual nonempty inverse-image carrier, using its actual
function-field pullback. If that carrier is empty, the restricted cycle
is zero. Only the original carrier is assumed locally Noetherian and
quasi-compact; no ambient finiteness or integrality is needed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {U X : Scheme.{u}}

/-- Restrict an ambient principal divisor through its actual nonempty
carrier inverse image. The restricted carrier's finiteness is derived. -/
theorem openRestriction_ambientPrincipalDivisor_of_nonempty
    (j : U ⟶ X) [IsOpenImmersion j] (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme]
    [Nonempty (W.val.comap j).subscheme] :
    letI := W.property
    let WU := openRestrictionSubscheme j W
    letI : IsIntegral (W.val.comap j).subscheme := WU.property
    letI : IsLocallyNoetherian WU.val.subscheme :=
      isLocallyNoetherian_of_isOpenImmersion (openRestrictionSubschemeMap j W)
    letI : CompactSpace WU.val.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (openRestrictionSubschemeMap j W)
    ∀ f : W.val.subscheme.functionFieldˣ,
      openRestriction ℤ j (ambientPrincipalDivisor W f) =
        ambientPrincipalDivisor WU
          (Units.map (functionFieldEquivOfOpenImmersion
            (openRestrictionSubschemeMap j W)).toMonoidHom f) := by
  letI := W.property
  let WU := openRestrictionSubscheme j W
  letI : IsIntegral (W.val.comap j).subscheme := WU.property
  letI : IsLocallyNoetherian WU.val.subscheme :=
    isLocallyNoetherian_of_isOpenImmersion (openRestrictionSubschemeMap j W)
  letI : CompactSpace WU.val.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (openRestrictionSubschemeMap j W)
  dsimp only
  intro f
  rw [ambientPrincipalDivisor_eq, ambientPrincipalDivisor_eq]
  change ((openRestriction ℤ j).comp
      (closedImmersionPushforward ℤ W.val.subschemeι))
        (principalDivisor W.val.subscheme f) = _
  rw [openRestriction_closedImmersionPushforward_subscheme, LinearMap.comp_apply]
  exact congrArg (closedImmersionPushforward ℤ (W.val.comap j).subschemeι)
    (openRestriction_principalDivisor_of_isOpenImmersion
      (openRestrictionSubschemeMap j W) f)

/-- An ambient principal divisor restricts to zero when its actual carrier
inverse image is empty; no function field is assigned to that empty scheme. -/
theorem openRestriction_ambientPrincipalDivisor_of_isEmpty
    (j : U ⟶ X) [IsOpenImmersion j] (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme]
    [IsEmpty (W.val.comap j).subscheme] :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ,
      openRestriction ℤ j (ambientPrincipalDivisor W f) = 0 := by
  letI := W.property
  intro f
  letI : IsEmpty (IntegralClosedSubscheme (W.val.comap j).subscheme) := ⟨fun Z ↦ by
    letI := Z.property
    exact isEmptyElim (Z.val.subschemeι.base (genericPoint Z.val.subscheme))⟩
  rw [ambientPrincipalDivisor_eq]
  change ((openRestriction ℤ j).comp
      (closedImmersionPushforward ℤ W.val.subschemeι))
        (principalDivisor W.val.subscheme f) = 0
  rw [openRestriction_closedImmersionPushforward_subscheme, LinearMap.comp_apply]
  have h : openRestriction ℤ (openRestrictionSubschemeMap j W)
      (principalDivisor W.val.subscheme f) = 0 := Subsingleton.elim _ _
  rw [h, map_zero]

end

end HodgeConjecture.SchemeCycles
