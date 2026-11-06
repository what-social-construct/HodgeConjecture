module

public import HodgeConjecture.Boundary.Normalization.AffineNormalizationRestriction

@[expose] public section

/-!
# Coherence of the actual normalization restrictions

The same ambient field defines identity and composition on actual nonempty
opens. Principal restrictions have exactly the inverse-image range under
the original structural morphism to the scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V W : X.Opens) [Nonempty U] [Nonempty V] [Nonempty W]
variable (N : Type u) [Field N] [Algebra X.functionField N]

/-- Restriction from an actual open to itself is the identity. -/
theorem affineNormalizationRestriction_self :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    affineNormalizationRestriction U U N le_rfl = 𝟙 _ := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  unfold affineNormalizationRestriction
  change Spec.map _ = 𝟙 (Spec _)
  rw [← Spec.map_id]
  congr 1

/-- Successive actual restrictions equal direct restriction in the same field. -/
theorem affineNormalizationRestriction_trans (hVU : V ≤ U) (hWV : W ≤ V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    affineNormalizationRestriction V W N hWV ≫
        affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction U W N (hWV.trans hVU) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, W) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
  unfold affineNormalizationRestriction
  rw [← Spec.map_comp]
  congr 1

/-- Two actual chains through a common smaller open give the same morphism. -/
theorem affineNormalizationRestriction_diamond
    (T : X.Opens) [Nonempty T]
    (hVU : V ≤ U) (hWU : W ≤ U) (hTV : T ≤ V) (hTW : T ≤ W) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, W) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField W).hom).toAlgebra
    letI : Algebra Γ(X, T) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField T).hom).toAlgebra
    affineNormalizationRestriction V T N hTV ≫ affineNormalizationRestriction U V N hVU =
      affineNormalizationRestriction W T N hTW ≫ affineNormalizationRestriction U W N hWU := by
  rw [affineNormalizationRestriction_trans, affineNormalizationRestriction_trans]

/-- The actual affine normalization restrictions commute over the original X. -/
theorem affineNormalizationRestriction_comp_toX
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫
        (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec) =
      normalizedModelToBase Γ(X, V) N ≫ hV.fromSpec := by
  rw [← Category.assoc, affineNormalizationRestriction_comp_toBase,
    Category.assoc, IsAffineOpen.map_fromSpec]

/-- A principal restriction has exactly the expected image over the original X. -/
theorem affineNormalizationRestriction_basicOpen_range
    (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, X.basicOpen f) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
    Set.range (affineNormalizationRestriction U (X.basicOpen f) N (X.basicOpen_le f)).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹'
        (X.basicOpen f : Set X) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, X.basicOpen f) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) N :=
    sectionRestriction_ambientScalarTower U (X.basicOpen f) N (X.basicOpen_le f)
  letI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  change Set.range (normalizationBaseChange
    (B := Γ(X, U)) (C := Γ(X, X.basicOpen f)) (E := N)).base = _
  rw [normalizationBaseChange_range f]
  change (normalizedModelToBase Γ(X, U) N).base ⁻¹'
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, U))) =
    (normalizedModelToBase Γ(X, U) N).base ⁻¹'
      (hU.fromSpec.base ⁻¹' (X.basicOpen f : Set X))
  rw [← hU.fromSpec_preimage_basicOpen f]
  rfl

/-- A chosen presentation of the same open as principal gives the same range. -/
theorem affineNormalizationRestriction_range_of_eq_basicOpen
    (hVU : V ≤ U) (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : V = X.basicOpen f) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    Set.range (affineNormalizationRestriction U V N hVU).base =
      (normalizedModelToBase Γ(X, U) N ≫ hU.fromSpec).base ⁻¹' (V : Set X) := by
  subst V
  exact affineNormalizationRestriction_basicOpen_range U N hU f

/-- A chosen principal presentation yields an open immersion of the actual models. -/
theorem affineNormalizationRestriction_isOpenImmersion_of_eq_basicOpen
    (hVU : V ≤ U) (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : V = X.basicOpen f) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    IsOpenImmersion (affineNormalizationRestriction U V N hVU) := by
  subst V
  exact affineNormalizationRestriction_basicOpen_isOpenImmersion U N hU f

end

end HodgeConjecture.CollisionFoundations
