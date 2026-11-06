module

public import HodgeConjecture.Cycles.RationalChow
public import HodgeConjecture.Cycles.CoefficientRestriction
public import HodgeConjecture.Cycles.ChowOpenRestriction

@[expose] public section

/-!
# Actual open restriction on rational Chow groups

Coefficient compatibility and the proved nonempty/empty principal-generator
identities preserve the rational relation span. The descended map retains
the actual cycle representatives, identity and contravariant composition.
It agrees with scalar extension of the integral Chow restriction through
the representative-preserving tensor equivalences. Only the target is
assumed Noetherian; source Noetherianity is derived from the open immersion.
Every rational class on the open lifts through a homogeneous cycle representative.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TensorProduct

noncomputable section

universe u

/-- The actual open restriction preserves the rational span of the same
principal generators, including the empty restricted-carrier branch. -/
theorem rationalPrincipalRelations_le_comap_openRestriction
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    rationalPrincipalRelations δ n ≤
      (rationalPrincipalRelations (δ.comapOpenImmersion j) n).comap
        (gradedOpenRestriction ℚ δ j n) := by
  classical
  letI := openImmersion_isNoetherian j
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedOpenRestriction ℚ δ j n
    (cyclesOfDegreeRationalize δ n (principalRelation δ n d)) ∈
      rationalPrincipalRelations (δ.comapOpenImmersion j) n
  rw [gradedOpenRestriction_rationalize]
  by_cases h : Nonempty (d.1.val.val.comap j).subscheme
  · letI := h
    rw [gradedOpenRestriction_principalRelation_of_nonempty]
    exact Submodule.subset_span ⟨d.openRestriction δ j n, rfl⟩
  · letI := not_nonempty_iff.mp h
    rw [gradedOpenRestriction_principalRelation_of_isEmpty, map_zero]
    exact (rationalPrincipalRelations (δ.comapOpenImmersion j) n).zero_mem

/-- Open restriction on the existing quotient of actual rational homogeneous
cycles, with the actual composed dimension function. -/
def rationalChowOpenRestriction {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    RationalChowGroup δ n →ₗ[ℚ] RationalChowGroup (δ.comapOpenImmersion j) n := by
  letI := openImmersion_isNoetherian j
  exact (rationalPrincipalRelations δ n).mapQ
    (rationalPrincipalRelations (δ.comapOpenImmersion j) n)
    (gradedOpenRestriction ℚ δ j n)
    (rationalPrincipalRelations_le_comap_openRestriction δ j n)

@[simp]
theorem rationalChowOpenRestriction_classMap
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (c : cyclesOfDegree ℚ δ n) :
    letI := openImmersion_isNoetherian j
    rationalChowOpenRestriction δ j n (rationalClassMap δ n c) =
      rationalClassMap (δ.comapOpenImmersion j) n
        (gradedOpenRestriction ℚ δ j n c) := rfl

/-- Every rational Chow class on the open lifts through an actual homogeneous
rational cycle and its reduced ambient support closures. -/
theorem rationalChowOpenRestriction_surjective
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    Function.Surjective (rationalChowOpenRestriction δ j n) := by
  letI := openImmersion_isNoetherian j
  intro z
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective (δ.comapOpenImmersion j) n z
  obtain ⟨b, rfl⟩ := gradedOpenRestriction_surjective ℚ δ j n c
  exact ⟨rationalClassMap δ n b, rationalChowOpenRestriction_classMap δ j n b⟩

/-- The quotient map for the actual identity immersion is the identity. -/
theorem rationalChowOpenRestriction_id (X : Scheme.{u}) [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ) :
    rationalChowOpenRestriction δ (𝟙 X) n = LinearMap.id := by
  apply (rationalPrincipalRelations δ n).quot_hom_ext
  intro c
  change rationalClassMap δ n (gradedOpenRestriction ℚ δ (𝟙 X) n c) =
    rationalClassMap δ n c
  rw [gradedOpenRestriction_id]
  rfl

/-- Actual open restriction is contravariantly functorial on the rational
quotient, with all intermediate Noetherianity derived from the target. -/
theorem rationalChowOpenRestriction_comp {U V X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    letI := openImmersion_isNoetherian i
    (rationalChowOpenRestriction (δ.comapOpenImmersion j) i n).comp
        (rationalChowOpenRestriction δ j n) =
      rationalChowOpenRestriction δ (i ≫ j) n := by
  letI := openImmersion_isNoetherian j
  letI := openImmersion_isNoetherian i
  apply (rationalPrincipalRelations δ n).quot_hom_ext
  intro c
  change rationalClassMap (δ.comapOpenImmersion (i ≫ j)) n
      (((gradedOpenRestriction ℚ (δ.comapOpenImmersion j) i n).comp
        (gradedOpenRestriction ℚ δ j n)) c) =
    rationalClassMap (δ.comapOpenImmersion (i ≫ j)) n
      (gradedOpenRestriction ℚ δ (i ≫ j) n c)
  rw [gradedOpenRestriction_comp]
  rfl

/-- Rationalization of integral Chow classes commutes with the actual
open restriction, without asserting injectivity of rationalization. -/
theorem rationalChowOpenRestriction_chowRationalize
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (z : ChowGroup δ n) :
    letI := openImmersion_isNoetherian j
    rationalChowOpenRestriction δ j n (chowRationalize δ n z) =
      chowRationalize (δ.comapOpenImmersion j) n (chowOpenRestriction δ j n z) := by
  letI := openImmersion_isNoetherian j
  obtain ⟨c, rfl⟩ := classMap_surjective δ n z
  simp only [chowRationalize_classMap, rationalChowOpenRestriction_classMap,
    chowOpenRestriction_classMap, gradedOpenRestriction_rationalize]

/-- Under the tensor comparisons, rational open restriction is exactly
scalar extension of integral open restriction on every tensor element. -/
theorem rationalChowOpenRestriction_chowRationalizationEquiv
    {U X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (t : ℚ ⊗[ℤ] ChowGroup δ n) :
    letI := openImmersion_isNoetherian j
    rationalChowOpenRestriction δ j n (chowRationalizationEquiv δ n t) =
      chowRationalizationEquiv (δ.comapOpenImmersion j) n
        ((chowOpenRestriction δ j n).baseChange ℚ t) := by
  letI := openImmersion_isNoetherian j
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul q z =>
      obtain ⟨c, rfl⟩ := classMap_surjective δ n z
      simp only [chowRationalizationEquiv_tmul_classMap,
        rationalChowOpenRestriction_classMap, map_smul,
        LinearMap.baseChange_tmul, chowOpenRestriction_classMap,
        gradedOpenRestriction_rationalize]
  | add t s ht hs => simp only [map_add, ht, hs]

end

end HodgeConjecture.SchemeCycles
