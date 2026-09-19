import HodgeConjecture.Boundary.Normalization.AffineNormalizationCoherence
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersion of actual affine normalization restrictions

Common principal neighborhoods compare the normalization models on arbitrary
nested nonempty affine opens. The restriction morphism identifies the smaller
model with the inverse image of the smaller open in the larger model. The
ambient field remains fixed throughout these comparisons.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (N : Type u) [Field N] [Algebra X.functionField N]

/-- Restriction to an arbitrary affine subopen is injective on points. -/
theorem affineNormalizationRestriction_injective
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    Function.Injective (affineNormalizationRestriction U V N hVU).base := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  let μU := normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec
  let μV := normalizedModelToBase Γ(X, V) N ≫ hV.fromSpec
  have hcomm : affineNormalizationRestriction U V N hVU ≫ μU = μV :=
    affineNormalizationRestriction_comp_toX U V N hVU hU hV
  intro a b hab
  have hxV : μV.base a ∈ V := by
    change μV.base a ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  have hxEq : μV.base a = μV.base b := by
    simpa only [← Scheme.comp_base_apply, hcomm] using congrArg μU.base hab
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter hU hV (μV.base a) ⟨hVU hxV, hxV⟩
  let W := X.basicOpen f
  letI : Nonempty W := ⟨⟨μV.base a, hxf⟩⟩
  letI : Algebra Γ(X, W) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
  have hWU : W ≤ U := X.basicOpen_le f
  have hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
  have hWVrange := affineNormalizationRestriction_range_of_eq_basicOpen
    V W N hWV hV g hfg
  have ha : a ∈ Set.range (affineNormalizationRestriction V W N hWV).base := by
    rw [hWVrange]
    exact hxf
  have hb : b ∈ Set.range (affineNormalizationRestriction V W N hWV).base := by
    rw [hWVrange]
    change μV.base b ∈ W
    rwa [← hxEq]
  obtain ⟨a', haa⟩ := ha
  obtain ⟨b', hbb⟩ := hb
  letI : IsOpenImmersion (affineNormalizationRestriction U W N hWU) :=
    affineNormalizationRestriction_basicOpen_isOpenImmersion U N hU f
  have hab' : (affineNormalizationRestriction U W N hWU).base a' =
      (affineNormalizationRestriction U W N hWU).base b' := by
    rw [← haa, ← hbb] at hab
    simpa only [← Scheme.comp_base_apply, affineNormalizationRestriction_trans] using hab
  have : a' = b' :=
    (affineNormalizationRestriction U W N hWU).isOpenEmbedding.injective hab'
  exact haa.symm.trans ((congrArg (affineNormalizationRestriction V W N hWV).base this).trans hbb)

/-- Restriction to an arbitrary nonempty affine subopen is an open immersion. -/
theorem affineNormalizationRestriction_isOpenImmersion
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    IsOpenImmersion (affineNormalizationRestriction U V N hVU) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  let μV := normalizedModelToBase Γ(X, V) N ≫ hV.fromSpec
  apply IsOpenImmersion.of_forall_source_exists _
    (affineNormalizationRestriction_injective U V N hVU hU hV)
  intro a
  have hxV : μV.base a ∈ V := by
    change μV.base a ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter hU hV (μV.base a) ⟨hVU hxV, hxV⟩
  let W := X.basicOpen f
  letI : Nonempty W := ⟨⟨μV.base a, hxf⟩⟩
  letI : Algebra Γ(X, W) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
  have hWU : W ≤ U := X.basicOpen_le f
  have hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
  letI : IsOpenImmersion (affineNormalizationRestriction V W N hWV) :=
    affineNormalizationRestriction_isOpenImmersion_of_eq_basicOpen V W N hWV hV g hfg
  refine ⟨normalizedAffineModel Γ(X, W) N,
    affineNormalizationRestriction V W N hWV, inferInstance, ?_, ?_⟩
  · change a ∈ Set.range (affineNormalizationRestriction V W N hWV).base
    rw [affineNormalizationRestriction_range_of_eq_basicOpen V W N hWV hV g hfg]
    exact hxf
  · rw [affineNormalizationRestriction_trans]
    exact affineNormalizationRestriction_basicOpen_isOpenImmersion U N hU f

/-- The image of an affine restriction is exactly the original base inverse image. -/
theorem affineNormalizationRestriction_range
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    Set.range (affineNormalizationRestriction U V N hVU).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹' (V : Set X) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  let μU := normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec
  let μV := normalizedModelToBase Γ(X, V) N ≫ hV.fromSpec
  have hcomm : affineNormalizationRestriction U V N hVU ≫ μU = μV :=
    affineNormalizationRestriction_comp_toX U V N hVU hU hV
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    change μU.base ((affineNormalizationRestriction U V N hVU).base a) ∈ V
    rw [← Scheme.comp_base_apply, hcomm]
    change μV.base a ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  · intro a ha
    change μU.base a ∈ V at ha
    have hxU : μU.base a ∈ U := by
      change μU.base a ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨_, rfl⟩
    obtain ⟨f, g, hfg, hxf⟩ :=
      exists_basicOpen_le_affine_inter hU hV (μU.base a) ⟨hxU, ha⟩
    let W := X.basicOpen f
    letI : Nonempty W := ⟨⟨μU.base a, hxf⟩⟩
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    have hWU : W ≤ U := X.basicOpen_le f
    have hWV : W ≤ V := hfg.trans_le (X.basicOpen_le g)
    have haW : a ∈ Set.range (affineNormalizationRestriction U W N hWU).base := by
      rw [affineNormalizationRestriction_basicOpen_range U N hU f]
      exact hxf
    obtain ⟨b, hba⟩ := haW
    refine ⟨(affineNormalizationRestriction V W N hWV).base b, ?_⟩
    rw [← Scheme.comp_base_apply, affineNormalizationRestriction_trans]
    exact hba

end

end HodgeConjecture.CollisionFoundations
