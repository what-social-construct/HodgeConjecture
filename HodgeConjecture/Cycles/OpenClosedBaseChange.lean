module

public import HodgeConjecture.Cycles.OpenSupport

@[expose] public section

/-!
# Open restriction and closed carrier pushforward

The actual inverse-image carrier and its map to the original carrier form
the existing Cartesian square. Open restriction commutes with closed
pushforward around this square on the finite-cycle modules. The proof
compares actual integral generators through their generic points and
retains the empty inverse-image case. No finiteness or nonemptiness
assumption on the ambient schemes or inverse-image carrier is used.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Z : IntegralClosedSubscheme X)

omit [IsOpenImmersion j] in
private theorem range_openRestrictionSubschemeMap :
    Set.range (openRestrictionSubschemeMap j Z).base =
      Z.val.subschemeι.base ⁻¹' Set.range j.base := by
  have hs : Function.Surjective (Z.val.comapIso j).hom.base :=
    (Scheme.homeoOfIso (Z.val.comapIso j)).surjective
  rw [openRestrictionSubschemeMap, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ,
    Scheme.Pullback.range_snd]

private theorem nonempty_carrier_baseChange (W : IntegralClosedSubscheme Z.val.subscheme) :
    Nonempty ((closedImageSubscheme Z.val.subschemeι W).val.comap j).subscheme ↔
      Nonempty (W.val.comap (openRestrictionSubschemeMap j Z)).subscheme := by
  rw [nonempty_openRestrictionSubscheme_iff, nonempty_openRestrictionSubscheme_iff,
    ambientGenericPoint_closedImageSubscheme, range_openRestrictionSubschemeMap]
  rfl

private theorem integralSupport_carrier_baseChange
    (W : IntegralClosedSubscheme Z.val.subscheme)
    [Nonempty ((closedImageSubscheme Z.val.subschemeι W).val.comap j).subscheme]
    [Nonempty (W.val.comap (openRestrictionSubschemeMap j Z)).subscheme] :
    openRestrictionSubscheme j (closedImageSubscheme Z.val.subschemeι W) =
      closedImageSubscheme (Z.val.comap j).subschemeι
        (openRestrictionSubscheme (openRestrictionSubschemeMap j Z) W) := by
  apply (pointEquivIntegralClosedSubscheme U).symm.injective
  apply j.isOpenEmbedding.injective
  calc
    j.base (ambientGenericPoint
        (openRestrictionSubscheme j (closedImageSubscheme Z.val.subschemeι W))) =
        Z.val.subschemeι.base (ambientGenericPoint W) := by
      rw [ambientGenericPoint_openRestrictionSubscheme,
        ambientGenericPoint_closedImageSubscheme]
    _ = Z.val.subschemeι.base ((openRestrictionSubschemeMap j Z).base
        (ambientGenericPoint (openRestrictionSubscheme (openRestrictionSubschemeMap j Z) W))) := by
      rw [ambientGenericPoint_openRestrictionSubscheme]
    _ = j.base ((Z.val.comap j).subschemeι.base
        (ambientGenericPoint (openRestrictionSubscheme (openRestrictionSubschemeMap j Z) W))) :=
      congrArg (fun f : (Z.val.comap j).subscheme ⟶ X ↦
        f.base (ambientGenericPoint
          (openRestrictionSubscheme (openRestrictionSubschemeMap j Z) W)))
        (openRestrictionSubschemeMap_subschemeι j Z)
    _ = j.base (ambientGenericPoint
        (closedImageSubscheme (Z.val.comap j).subschemeι
          (openRestrictionSubscheme (openRestrictionSubschemeMap j Z) W))) := by
      rw [ambientGenericPoint_closedImageSubscheme]

/-- The existing open restriction commutes with closed pushforward through
the actual inverse-image carrier square, including empty inverse images. -/
theorem openRestriction_closedImmersionPushforward_subscheme
    (R : Type v) [Semiring R] (Z : IntegralClosedSubscheme X) :
    (openRestriction R j).comp (closedImmersionPushforward R Z.val.subschemeι) =
      (closedImmersionPushforward R (Z.val.comap j).subschemeι).comp
        (openRestriction R (openRestrictionSubschemeMap j Z)) := by
  classical
  apply Finsupp.lhom_ext
  intro W r
  simp only [LinearMap.comp_apply, closedImmersionPushforward_single,
    openRestriction_single, map_smul]
  congr 1
  change openRestriction R j
      (fundamentalCycle R (closedImageSubscheme Z.val.subschemeι W)) =
    closedImmersionPushforward R (Z.val.comap j).subschemeι
      (openRestrictionGenerator (openRestrictionSubschemeMap j Z) R W)
  by_cases h : Nonempty (W.val.comap (openRestrictionSubschemeMap j Z)).subscheme
  · letI := h
    letI := (nonempty_carrier_baseChange j Z W).mpr h
    rw [openRestriction_fundamentalCycle_of_nonempty,
      openRestrictionGenerator_of_nonempty,
      closedImmersionPushforward_fundamentalCycle]
    exact congrArg (fundamentalCycle R) (integralSupport_carrier_baseChange j Z W)
  · letI : IsEmpty (W.val.comap (openRestrictionSubschemeMap j Z)).subscheme :=
      not_nonempty_iff.mp h
    letI : IsEmpty ((closedImageSubscheme Z.val.subschemeι W).val.comap j).subscheme :=
      not_nonempty_iff.mp (fun hc ↦ h ((nonempty_carrier_baseChange j Z W).mp hc))
    rw [openRestriction_fundamentalCycle_of_isEmpty,
      openRestrictionGenerator_of_isEmpty, map_zero]

end

end HodgeConjecture.SchemeCycles
