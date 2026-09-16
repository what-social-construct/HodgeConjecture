import HodgeConjecture.Cycles.PrincipalRelationRestriction

/-!
# Actual open restriction on the integral Chow quotient

The existing graded open cycle map preserves actual principal relations.
It therefore descends to the existing quotient, with the same cycle
representatives. Identity and contravariant composition are inherited
from the proved cycle laws. Only the target scheme is assumed Noetherian;
the open source and intermediate schemes inherit that property.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Open restriction on the quotient by the existing actual principal
relations, using the proved relation-span inclusion. -/
def chowOpenRestriction {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    ChowGroup δ n →ₗ[ℤ] ChowGroup (δ.comapOpenImmersion j) n := by
  letI := openImmersion_isNoetherian j
  exact (principalRelations δ n).mapQ (principalRelations (δ.comapOpenImmersion j) n)
    (gradedOpenRestriction ℤ δ j n)
    (principalRelations_le_comap_openRestriction δ j n)

/-- The quotient map retains the literal restricted cycle representative. -/
@[simp]
theorem chowOpenRestriction_classMap {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    letI := openImmersion_isNoetherian j
    chowOpenRestriction δ j n (classMap δ n c) =
      classMap (δ.comapOpenImmersion j) n (gradedOpenRestriction ℤ δ j n c) := rfl

/-- Identity on the quotient follows from identity on the actual cycles. -/
theorem chowOpenRestriction_id (X : Scheme.{u}) [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ) :
    chowOpenRestriction δ (𝟙 X) n = LinearMap.id := by
  apply (principalRelations δ n).quot_hom_ext
  intro c
  change classMap δ n (gradedOpenRestriction ℤ δ (𝟙 X) n c) = classMap δ n c
  rw [gradedOpenRestriction_id]
  rfl

/-- Contravariant composition on the quotient is inherited on unchanged
cycle representatives, with the same restricted dimension function. -/
theorem chowOpenRestriction_comp {V U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    letI := openImmersion_isNoetherian i
    (chowOpenRestriction (δ.comapOpenImmersion j) i n).comp
        (chowOpenRestriction δ j n) =
      chowOpenRestriction δ (i ≫ j) n := by
  letI := openImmersion_isNoetherian j
  letI := openImmersion_isNoetherian i
  apply (principalRelations δ n).quot_hom_ext
  intro c
  change classMap (δ.comapOpenImmersion (i ≫ j)) n
      (((gradedOpenRestriction ℤ (δ.comapOpenImmersion j) i n).comp
        (gradedOpenRestriction ℤ δ j n)) c) =
    classMap (δ.comapOpenImmersion (i ≫ j)) n
      (gradedOpenRestriction ℤ δ (i ≫ j) n c)
  rw [gradedOpenRestriction_comp]
  rfl

end

end HodgeConjecture.SchemeCycles
