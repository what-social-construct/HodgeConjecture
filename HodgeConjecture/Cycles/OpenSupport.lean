import HodgeConjecture.Cycles.OpenRestriction
import HodgeConjecture.Cycles.DivisorSupport

/-!
# Actual open support restriction and reduced closure

Nonempty inverse image of an integral closed subscheme has the same
ambient generic point under an open immersion. Reduced point closure
therefore supplies the inverse support construction. The same comparison
preserves codimension and gives the coefficient formula for the existing
finite-cycle restriction. No ambient integrality or finiteness is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Ambient reduced closure of an integral support in the open subscheme. -/
def openClosureSubscheme (W : IntegralClosedSubscheme U) : IntegralClosedSubscheme X :=
  pointSupport X (j.base (ambientGenericPoint W))

omit [IsOpenImmersion j] in
@[simp]
theorem openClosureSubscheme_ambientGenericPoint (W : IntegralClosedSubscheme U) :
    ambientGenericPoint (openClosureSubscheme j W) = j.base (ambientGenericPoint W) :=
  ambientGenericPoint_pointSupport X _

omit [IsOpenImmersion j] in
private theorem openRestrictionSubschemeMap_subschemeι
    (Z : IntegralClosedSubscheme X) :
    openRestrictionSubschemeMap j Z ≫ Z.val.subschemeι =
      (Z.val.comap j).subschemeι ≫ j := by
  simp only [openRestrictionSubschemeMap, Category.assoc, ← pullback.condition]
  rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]

/-- The actual nonempty restricted support has the original ambient generic
point under the open inclusion. -/
theorem ambientGenericPoint_openRestrictionSubscheme (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    j.base (ambientGenericPoint (openRestrictionSubscheme j Z)) =
      ambientGenericPoint Z := by
  letI := Z.property
  letI := openRestrictionSubscheme_isIntegral j Z
  have h := congrArg (fun f : (Z.val.comap j).subscheme ⟶ X ↦
    f.base (genericPoint (Z.val.comap j).subscheme))
      (openRestrictionSubschemeMap_subschemeι j Z)
  change Z.val.subschemeι.base
      ((openRestrictionSubschemeMap j Z).base (genericPoint (Z.val.comap j).subscheme)) =
    j.base (ambientGenericPoint (openRestrictionSubscheme j Z)) at h
  rw [genericPoint_eq_of_isOpenImmersion (openRestrictionSubschemeMap j Z)] at h
  exact h.symm

/-- An integral support meets the open exactly when its generic point lies
in the actual open image. -/
theorem nonempty_openRestrictionSubscheme_iff (Z : IntegralClosedSubscheme X) :
    Nonempty (Z.val.comap j).subscheme ↔
      ambientGenericPoint Z ∈ Set.range j.base := by
  constructor
  · intro h
    letI := h
    exact ⟨ambientGenericPoint (openRestrictionSubscheme j Z),
      ambientGenericPoint_openRestrictionSubscheme j Z⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩⟩
    change x ∈ (Z.val.comap j).support
    rw [Scheme.IdealSheafData.support_comap]
    change j.base x ∈ Z.val.support
    rw [hx]
    exact (ambientGenericPoint_isGenericPoint Z).mem

private theorem openClosureSubscheme_comap_nonempty (W : IntegralClosedSubscheme U) :
    Nonempty ((openClosureSubscheme j W).val.comap j).subscheme := by
  apply (nonempty_openRestrictionSubscheme_iff j _).mpr
  exact ⟨ambientGenericPoint W, (openClosureSubscheme_ambientGenericPoint j W).symm⟩

/-- Restricting the ambient reduced closure recovers the literal ideal sheaf
of the original integral closed support. -/
theorem openClosureSubscheme_comap (W : IntegralClosedSubscheme U) :
    (openClosureSubscheme j W).val.comap j = W.val := by
  letI := openClosureSubscheme_comap_nonempty j W
  have h : ambientGenericPoint (openRestrictionSubscheme j (openClosureSubscheme j W)) =
      ambientGenericPoint W := by
    apply j.isOpenEmbedding.injective
    rw [ambientGenericPoint_openRestrictionSubscheme,
      openClosureSubscheme_ambientGenericPoint]
  have hW : openRestrictionSubscheme j (openClosureSubscheme j W) = W :=
    (pointEquivIntegralClosedSubscheme U).symm.injective h
  exact congrArg Subtype.val hW

/-- Reduced closure in the ambient scheme recovers every integral support
whose restriction is nonempty. -/
theorem openClosureSubscheme_openRestrictionSubscheme (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    openClosureSubscheme j (openRestrictionSubscheme j Z) = Z := by
  rw [openClosureSubscheme, ambientGenericPoint_openRestrictionSubscheme,
    pointSupport_ambientGenericPoint]

/-- Ambient reduced closure preserves the existing chain codimension, since
the generic-point local rings are actually isomorphic. -/
theorem supportCodimension_openClosureSubscheme (W : IntegralClosedSubscheme U) :
    supportCodimension (openClosureSubscheme j W) = supportCodimension W := by
  apply WithBot.coe_injective
  rw [supportCodimension_eq_stalkDim, openClosureSubscheme_ambientGenericPoint,
    stalkDimension_openImmersion, supportCodimension_eq_stalkDim]

/-- Nonempty actual open restriction preserves support codimension. -/
theorem supportCodimension_openRestrictionSubscheme (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    supportCodimension (openRestrictionSubscheme j Z) = supportCodimension Z := by
  rw [← supportCodimension_openClosureSubscheme j,
    openClosureSubscheme_openRestrictionSubscheme]

/-- On prime supports the reduced-closure construction is the existing
divisor-point embedding, expressed through the point/support equivalence. -/
theorem openClosureSubscheme_divisorPoint (x : DivisorPoint U) :
    openClosureSubscheme j (divisorPointEquivPrimeDivisor U x).val =
      (divisorPointEquivPrimeDivisor X (divisorPointEmbedding j x)).val := by
  simp [openClosureSubscheme, divisorPointEquivPrimeDivisor_val]

/-- Open restriction reads exactly the coefficient of the corresponding
ambient reduced closure, in the already defined finite-cycle map. -/
theorem openRestriction_apply (R : Type v) [Semiring R]
    (c : Cycles X R) (W : IntegralClosedSubscheme U) :
    (openRestriction R j c) W = c (openClosureSubscheme j W) := by
  classical
  have h : (Finsupp.lapply W).comp (openRestriction R j) =
      (Finsupp.lapply (openClosureSubscheme j W) : Cycles X R →ₗ[R] R) := by
    apply Finsupp.lhom_ext
    intro Z r
    change (openRestriction R j (Finsupp.single Z r)) W =
      Finsupp.single Z r (openClosureSubscheme j W)
    rw [openRestriction_single]
    by_cases hZ : Nonempty (Z.val.comap j).subscheme
    · letI := hZ
      rw [openRestrictionGenerator_of_nonempty]
      by_cases hW : openRestrictionSubscheme j Z = W
      · subst W
        simp [fundamentalCycle, openClosureSubscheme_openRestrictionSubscheme]
      · have hZW : Z ≠ openClosureSubscheme j W := by
          intro hZW
          apply hW
          apply Subtype.ext
          change Z.val.comap j = W.val
          rw [hZW, openClosureSubscheme_comap]
        simp [fundamentalCycle, hW, hZW]
    · letI : IsEmpty (Z.val.comap j).subscheme := not_nonempty_iff.mp hZ
      rw [openRestrictionGenerator_of_isEmpty]
      have hZW : Z ≠ openClosureSubscheme j W := by
        intro hZW
        apply hZ
        rw [hZW]
        exact openClosureSubscheme_comap_nonempty j W
      simp [hZW]
  exact LinearMap.congr_fun h c

end

end HodgeConjecture.SchemeCycles
