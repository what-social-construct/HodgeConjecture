module

public import HodgeConjecture.Cycles.RationalChowOpenRestriction

@[expose] public section

/-!
# Lift actual principal relations from an open subscheme

Take the reduced closure of a relation carrier and extend its unit by the
inverse of the actual open function-field equivalence. Restriction recovers
the original relation datum, including the degree-one-higher carrier. Thus
open restriction maps the integral and rational principal-relation spans
onto their counterparts on the open.

This is the relation-lifting step of Stacks Lemma 42.19.3 (02RX):
https://stacks.math.columbia.edu/tag/02RX. The ambient divisor may acquire
boundary terms. No relation-preserving closure map on Chow groups is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Every actual open relation datum lifts on its reduced closure, by the
inverse of the induced function-field equivalence. No finiteness is needed
to lift the carrier and its function. -/
theorem exists_openRestriction_principalRelationData
    {U X : Scheme.{u}} (δ : DimensionFunction X) (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℤ)
    (d : PrincipalRelationData (δ.comapOpenImmersion j) n) :
    ∃ e : PrincipalRelationData δ n,
      ∃ h : Nonempty (e.1.val.val.comap j).subscheme,
        letI := h
        e.openRestriction δ j n = d := by
  let W : {W : IntegralClosedSubscheme X // supportDegree δ W = n + 1} :=
    ⟨openClosureSubscheme j d.1.val,
      (supportDegree_openClosureSubscheme δ j d.1.val).trans d.1.property⟩
  haveI hW : Nonempty (W.val.val.comap j).subscheme := by
    apply (nonempty_openRestrictionSubscheme_iff j W.val).mpr
    exact ⟨ambientGenericPoint d.1.val,
      (openClosureSubscheme_ambientGenericPoint j d.1.val).symm⟩
  let T : {V : IntegralClosedSubscheme U //
      supportDegree (δ.comapOpenImmersion j) V = n + 1} :=
    ⟨openRestrictionSubscheme j W.val,
      (supportDegree_openRestrictionSubscheme δ j W.val).trans W.property⟩
  have hT : T = d.1 := Subtype.ext (Subtype.ext (openClosureSubscheme_comap j d.1.val))
  have h : ∀ f : (letI := T.val.property; T.val.val.subscheme.functionFieldˣ),
      ∃ e : PrincipalRelationData δ n,
        ∃ he : Nonempty (e.1.val.val.comap j).subscheme,
          letI := he
          e.openRestriction δ j n = ⟨T, f⟩ := by
    letI := W.val.property
    letI : IsIntegral (W.val.val.comap j).subscheme :=
      (openRestrictionSubscheme j W.val).property
    intro f
    let e := functionFieldEquivOfOpenImmersion (openRestrictionSubschemeMap j W.val)
    refine ⟨⟨W, Units.map e.symm.toMonoidHom f⟩, hW, ?_⟩
    have hf : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom f) = f := by
      apply Units.ext
      exact e.apply_symm_apply _
    change (⟨T, Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom f)⟩ :
      PrincipalRelationData (δ.comapOpenImmersion j) n) = ⟨T, f⟩
    rw [hf]
  rw [hT] at h
  exact h d.2

/-- The existing graded restriction recovers each actual principal generator. -/
theorem exists_principalRelation_openLift
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    ∀ d : PrincipalRelationData (δ.comapOpenImmersion j) n,
      ∃ e : PrincipalRelationData δ n,
        gradedOpenRestriction ℤ δ j n (principalRelation δ n e) =
          principalRelation (δ.comapOpenImmersion j) n d := by
  letI := openImmersion_isNoetherian j
  intro d
  obtain ⟨e, he, hd⟩ := exists_openRestriction_principalRelationData δ j n d
  letI := he
  exact ⟨e, (gradedOpenRestriction_principalRelation_of_nonempty δ j n e).trans
    (congrArg (principalRelation (δ.comapOpenImmersion j) n) hd)⟩

/-- Integral relation-span image equality follows from actual generator lifts. -/
theorem principalRelations_map_openRestriction
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    (principalRelations δ n).map (gradedOpenRestriction ℤ δ j n) =
      principalRelations (δ.comapOpenImmersion j) n := by
  letI := openImmersion_isNoetherian j
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr (principalRelations_le_comap_openRestriction δ j n)
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    obtain ⟨e, he⟩ := exists_principalRelation_openLift δ j n d
    exact ⟨principalRelation δ n e, principalRelation_mem δ n e, he⟩

/-- Rational relations lift by the same integer principal generators, with
coefficient compatibility. No injectivity of rationalization is used. -/
theorem rationalPrincipalRelations_map_openRestriction
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    (rationalPrincipalRelations δ n).map (gradedOpenRestriction ℚ δ j n) =
      rationalPrincipalRelations (δ.comapOpenImmersion j) n := by
  letI := openImmersion_isNoetherian j
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr
      (rationalPrincipalRelations_le_comap_openRestriction δ j n)
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    obtain ⟨e, he⟩ := exists_principalRelation_openLift δ j n d
    refine ⟨cyclesOfDegreeRationalize δ n (principalRelation δ n e),
      Submodule.subset_span (Set.mem_range_self e), ?_⟩
    rw [gradedOpenRestriction_rationalize, he]

end

end HodgeConjecture.SchemeCycles
