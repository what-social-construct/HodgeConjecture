module

public import HodgeConjecture.Cycles.PrincipalDivisorTransport

@[expose] public section

/-!
# Actual ambient images of carrier principal divisors

A principal divisor on an integral closed carrier is pushed into the
existing ambient finite-cycle module by its actual closed inclusion.
Closed pushforward carries this cycle to the principal divisor on the
actual image carrier, with the rational function transported through the
proved support-to-image function-field isomorphism.

Noetherianity and quasi-compactness are inherited by actual closed
subschemes, or transported through the actual support isomorphism. These
are proved properties, not relation or norm assumptions. No relation
subgroup or quotient is defined in this module.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- An actual closed subscheme of a locally Noetherian scheme is locally
Noetherian, as proved on its affine quotient cover. -/
theorem idealSubscheme_isLocallyNoetherian [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsLocallyNoetherian I.subscheme := by
  apply (isLocallyNoetherian_iff_openCover I.subschemeCover.openCover).mpr
  intro U
  let V : X.affineOpens := U
  letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  change IsLocallyNoetherian (Spec (CommRingCat.of (Γ(X, V) ⧸ I.ideal V)))
  infer_instance

/-- An actual closed subscheme of a quasi-compact scheme is quasi-compact. -/
theorem idealSubscheme_compactSpace [CompactSpace X]
    (I : X.IdealSheafData) : CompactSpace I.subscheme :=
  I.subschemeι.isClosedEmbedding.compactSpace

/-- The actual image carrier inherits local Noetherianity from the source
carrier through the existing support-to-image isomorphism. -/
theorem closedImageSubscheme_isLocallyNoetherian (i : X ⟶ Y)
    (W : IntegralClosedSubscheme X) [IsClosedImmersion (W.val.subschemeι ≫ i)]
    [IsLocallyNoetherian W.val.subscheme] :
    IsLocallyNoetherian (closedImageSubscheme i W).val.subscheme :=
  isLocallyNoetherian_of_isOpenImmersion (closedImageSubschemeIso i W).inv

/-- The actual image carrier inherits quasi-compactness through that same
scheme isomorphism; no ambient properness assumption is used. -/
theorem closedImageSubscheme_compactSpace (i : X ⟶ Y)
    (W : IntegralClosedSubscheme X) [IsClosedImmersion (W.val.subschemeι ≫ i)]
    [CompactSpace W.val.subscheme] :
    CompactSpace (closedImageSubscheme i W).val.subscheme :=
  (Scheme.homeoOfIso (closedImageSubschemeIso i W)).compactSpace

/-- The existing principal divisor on an actual integral closed carrier,
pushed into the existing ambient finite-cycle module. -/
def ambientPrincipalDivisor (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    W.val.subscheme.functionFieldˣ → Cycles X ℤ := by
  letI := W.property
  exact fun f ↦ closedImmersionPushforward ℤ W.val.subschemeι
    (principalDivisor W.val.subscheme f)

/-- The ambient helper is literally the existing closed pushforward. -/
theorem ambientPrincipalDivisor_eq (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ,
      ambientPrincipalDivisor W f =
        closedImmersionPushforward ℤ W.val.subschemeι
          (principalDivisor W.val.subscheme f) := by
  letI := W.property
  intro f
  rfl

@[simp]
theorem ambientPrincipalDivisor_one (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ambientPrincipalDivisor W (1 : W.val.subscheme.functionFieldˣ) = 0 := by
  letI := W.property
  simp only [ambientPrincipalDivisor, principalDivisor_one, map_zero]

/-- The ambient carrier image retains the multiplicative-to-additive law. -/
theorem ambientPrincipalDivisor_mul (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f g : W.val.subscheme.functionFieldˣ,
      ambientPrincipalDivisor W (f * g) =
        ambientPrincipalDivisor W f + ambientPrincipalDivisor W g := by
  letI := W.property
  intro f g
  simp only [ambientPrincipalDivisor, principalDivisor_mul, map_add]

@[simp]
theorem ambientPrincipalDivisor_inv (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ,
      ambientPrincipalDivisor W f⁻¹ = -ambientPrincipalDivisor W f := by
  letI := W.property
  intro f
  simp only [ambientPrincipalDivisor, principalDivisor_inv, map_neg]

/-- Closed pushforward sends an ambient carrier principal divisor to the
principal divisor on its actual image carrier. The rational function is
transported by the inverse of the actual contravariant function-field map.
Only the source carrier's finiteness properties are hypotheses. -/
theorem closedImmersionPushforward_ambientPrincipalDivisor
    (i : X ⟶ Y) [IsClosedImmersion i] (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    letI := closedImageSubscheme_isIntegral i W
    letI := closedImageSubscheme_isLocallyNoetherian i W
    letI := closedImageSubscheme_compactSpace i W
    ∀ f : W.val.subscheme.functionFieldˣ,
      closedImmersionPushforward ℤ i (ambientPrincipalDivisor W f) =
        ambientPrincipalDivisor (closedImageSubscheme i W)
          (Units.map (functionFieldEquiv (closedImageSubschemeIso i W)).symm.toMonoidHom f) := by
  letI := W.property
  letI := closedImageSubscheme_isIntegral i W
  letI := closedImageSubscheme_isLocallyNoetherian i W
  letI := closedImageSubscheme_compactSpace i W
  letI : IsLocallyNoetherian (W.val.map i).subscheme :=
    closedImageSubscheme_isLocallyNoetherian i W
  letI : CompactSpace (W.val.map i).subscheme :=
    closedImageSubscheme_compactSpace i W
  intro f
  let e := closedImageSubschemeIso i W
  let g := Units.map (functionFieldEquiv e).symm.toMonoidHom f
  have hg : Units.map (functionFieldEquiv e).toMonoidHom g = f := by
    apply Units.ext
    change functionFieldEquiv e ((functionFieldEquiv e).symm (f : W.val.subscheme.functionField)) = _
    exact (functionFieldEquiv e).apply_symm_apply _
  have hp := principalDivisor_iso e g
  rw [hg] at hp
  rw [ambientPrincipalDivisor_eq, ambientPrincipalDivisor_eq]
  change closedImmersionPushforward ℤ i
      (closedImmersionPushforward ℤ W.val.subschemeι (principalDivisor W.val.subscheme f)) =
    closedImmersionPushforward ℤ (W.val.map i).subschemeι
      (principalDivisor (W.val.map i).subscheme g)
  rw [← hp]
  change ((closedImmersionPushforward ℤ i).comp
      (closedImmersionPushforward ℤ W.val.subschemeι)) _ =
    ((closedImmersionPushforward ℤ (closedImageSubscheme i W).val.subschemeι).comp
      (closedImmersionPushforward ℤ e.hom)) _
  rw [closedImmersionPushforward_comp, closedImmersionPushforward_comp]
  simp only [show e.hom ≫ (closedImageSubscheme i W).val.subschemeι = W.val.subschemeι ≫ i from
    closedImageSubschemeIso_hom_subschemeι i W]

/-- The relation-generator form of the explicit actual function-field
transport. The target function is constructed, not assumed to exist. -/
theorem exists_ambientPrincipalDivisor_image
    (i : X ⟶ Y) [IsClosedImmersion i] (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    letI := closedImageSubscheme_isIntegral i W
    letI := (closedImageSubscheme i W).property
    letI := closedImageSubscheme_isLocallyNoetherian i W
    letI := closedImageSubscheme_compactSpace i W
    ∀ f : W.val.subscheme.functionFieldˣ,
      ∃ g : (closedImageSubscheme i W).val.subscheme.functionFieldˣ,
        closedImmersionPushforward ℤ i (ambientPrincipalDivisor W f) =
          ambientPrincipalDivisor (closedImageSubscheme i W) g := by
  letI := W.property
  letI := closedImageSubscheme_isIntegral i W
  letI := (closedImageSubscheme i W).property
  letI := closedImageSubscheme_isLocallyNoetherian i W
  letI := closedImageSubscheme_compactSpace i W
  intro f
  exact ⟨_, closedImmersionPushforward_ambientPrincipalDivisor i W f⟩

end

end HodgeConjecture.SchemeCycles
