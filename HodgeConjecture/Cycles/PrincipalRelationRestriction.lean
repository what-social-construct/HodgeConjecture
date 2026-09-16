import HodgeConjecture.Cycles.PrincipalDivisorRestriction
import HodgeConjecture.Cycles.PrincipalRelations
import HodgeConjecture.Cycles.OpenGrading

/-!
# Actual open restriction of principal relations

A nonempty restricted carrier retains its degree-one-higher index and
receives its rational function through the actual open function-field map.
The ambient principal-divisor identities identify the restricted generator
with this genuine principal relation, or with zero for an empty carrier.
Thus the existing graded open map preserves the actual relation span and
rational-equivalence predicate. No quotient map is defined here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The source of an open immersion into a Noetherian scheme is Noetherian.
Local Noetherianity makes the open map quasi-compact; source compactness
does not follow merely from target compactness for an arbitrary open. -/
theorem openImmersion_isNoetherian {U X : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] : IsNoetherian U where
  toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace j

/-- Restrict genuine relation data only when its actual inverse-image
carrier is nonempty. The index construction needs no finiteness premise. -/
def PrincipalRelationData.openRestriction {U X : Scheme.{u}}
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (d : PrincipalRelationData δ n)
    [Nonempty (d.1.val.val.comap j).subscheme] :
    PrincipalRelationData (δ.comapOpenImmersion j) n := by
  letI := d.1.val.property
  letI : IsIntegral (d.1.val.val.comap j).subscheme :=
    (openRestrictionSubscheme j d.1.val).property
  refine ⟨⟨openRestrictionSubscheme j d.1.val,
    (supportDegree_openRestrictionSubscheme δ j d.1.val).trans d.1.property⟩, ?_⟩
  exact Units.map
    (functionFieldEquivOfOpenImmersion (openRestrictionSubschemeMap j d.1.val)).toMonoidHom d.2

@[simp]
theorem PrincipalRelationData.openRestriction_carrier {U X : Scheme.{u}}
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (d : PrincipalRelationData δ n)
    [Nonempty (d.1.val.val.comap j).subscheme] :
    (d.openRestriction δ j n).1.val = openRestrictionSubscheme j d.1.val := rfl

/-- The unit is pulled back in the contravariant direction by the actual
support map, with no choice of a replacement rational function. -/
@[simp]
theorem PrincipalRelationData.openRestriction_function {U X : Scheme.{u}}
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (d : PrincipalRelationData δ n)
    [Nonempty (d.1.val.val.comap j).subscheme] :
    letI := d.1.val.property
    letI : IsIntegral (d.1.val.val.comap j).subscheme :=
      (openRestrictionSubscheme j d.1.val).property
    (d.openRestriction δ j n).2 = Units.map
      (functionFieldEquivOfOpenImmersion (openRestrictionSubschemeMap j d.1.val)).toMonoidHom
      d.2 := rfl

/-- The nonempty branch is the genuine principal generator on the actual
restricted carrier, with source Noetherianity derived from the target. -/
theorem gradedOpenRestriction_principalRelation_of_nonempty
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (d : PrincipalRelationData δ n)
    [Nonempty (d.1.val.val.comap j).subscheme] :
    letI := openImmersion_isNoetherian j
    gradedOpenRestriction ℤ δ j n (principalRelation δ n d) =
      principalRelation (δ.comapOpenImmersion j) n (d.openRestriction δ j n) := by
  letI := openImmersion_isNoetherian j
  apply Subtype.ext
  exact openRestriction_ambientPrincipalDivisor_of_nonempty j d.1.val d.2

/-- An empty restricted carrier contributes zero, not artificial relation
data on an empty scheme. -/
theorem gradedOpenRestriction_principalRelation_of_isEmpty
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (d : PrincipalRelationData δ n)
    [IsEmpty (d.1.val.val.comap j).subscheme] :
    gradedOpenRestriction ℤ δ j n (principalRelation δ n d) = 0 := by
  apply Subtype.ext
  exact openRestriction_ambientPrincipalDivisor_of_isEmpty j d.1.val d.2

/-- Preservation of the existing generated relation submodule follows
from the two geometric generator identities, without a descent hypothesis. -/
theorem principalRelations_le_comap_openRestriction
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    principalRelations δ n ≤ (principalRelations (δ.comapOpenImmersion j) n).comap
      (gradedOpenRestriction ℤ δ j n) := by
  classical
  letI := openImmersion_isNoetherian j
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedOpenRestriction ℤ δ j n (principalRelation δ n d) ∈
    principalRelations (δ.comapOpenImmersion j) n
  by_cases h : Nonempty (d.1.val.val.comap j).subscheme
  · letI := h
    rw [gradedOpenRestriction_principalRelation_of_nonempty]
    exact principalRelation_mem _ _ _
  · letI := not_nonempty_iff.mp h
    rw [gradedOpenRestriction_principalRelation_of_isEmpty]
    exact (principalRelations (δ.comapOpenImmersion j) n).zero_mem

/-- Actual rational equivalence is preserved by the same graded open map. -/
theorem rationallyEquivalent_openRestriction
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ)
    {c e : cyclesOfDegree ℤ δ n} (h : RationallyEquivalent δ n c e) :
    letI := openImmersion_isNoetherian j
    RationallyEquivalent (δ.comapOpenImmersion j) n
      (gradedOpenRestriction ℤ δ j n c) (gradedOpenRestriction ℤ δ j n e) := by
  letI := openImmersion_isNoetherian j
  change c - e ∈ principalRelations δ n at h
  have hmem := principalRelations_le_comap_openRestriction δ j n h
  change gradedOpenRestriction ℤ δ j n (c - e) ∈
    principalRelations (δ.comapOpenImmersion j) n at hmem
  simpa only [RationallyEquivalent, map_sub] using hmem

end

end HodgeConjecture.SchemeCycles
