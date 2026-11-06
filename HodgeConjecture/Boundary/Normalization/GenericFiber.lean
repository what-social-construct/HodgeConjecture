module

public import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

/-!
# The actual generic fiber of a finite dominant morphism

The generic-stalk square is a pullback for a finite dominant morphism of
integral schemes. The proof uses the actual affine section-ring pushout,
the original affine inverse-image chart, and the canonical generic germs.
No replacement field or separately supplied geometric-fiber model is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles

noncomputable section

universe u

private theorem genericGerm_fromSpec {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    Spec.map (X.germToFunctionField U) ≫ hU.fromSpec =
      X.fromSpecStalk (genericPoint X) := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  change hU.fromSpecStalk hη = X.fromSpecStalk (genericPoint X)
  exact hU.fromSpecStalk_eq_fromSpecStalk hη

private theorem affinePreimage_isPullback {X Y : Scheme.{u}}
    (p : Y ⟶ X) [IsAffineHom p] (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback (Spec.map (p.app U)) (hU.preimage p).fromSpec hU.fromSpec p := by
  have hp : Spec.map (p.app U) ≫ hU.fromSpec = (hU.preimage p).fromSpec ≫ p := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.SpecMap_appLE_fromSpec p hU (hU.preimage p) le_rfl
  refine (isPullback_morphismRestrict p U).of_iso (hU.preimage p).isoSpec
    hU.isoSpec (Iso.refl Y) (Iso.refl X) ?_ ?_ ?_ ?_
  · apply (cancel_mono hU.fromSpec).mp
    simp only [Category.assoc, hp, IsAffineOpen.isoSpec_hom,
      IsAffineOpen.toSpecΓ_fromSpec, IsAffineOpen.toSpecΓ_fromSpec_assoc,
      morphismRestrict_ι]
  · simp [IsAffineOpen.isoSpec_hom]
  · simp [IsAffineOpen.isoSpec_hom]
  · simp

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

/-- The actual generic-stalk square is a pullback. Consequently its canonical
pullback isomorphism identifies `Spec K(Y)` with the generic fiber of `p`. -/
theorem functionFieldMapOfDominant_isPullback :
    IsPullback (Y.fromSpecStalk (genericPoint Y))
      (Spec.map (functionFieldMapOfDominant p)) p
      (X.fromSpecStalk (genericPoint X)) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : Algebra.IsPushout Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_isPushout_of_affine p U hU
  have hfields : IsPullback
      (Spec.map (Y.germToFunctionField (p ⁻¹ᵁ U)))
      (Spec.map (functionFieldMapOfDominant p))
      (Spec.map (p.app U)) (Spec.map (X.germToFunctionField U)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout Γ(X, U) Γ(Y, p ⁻¹ᵁ U)
        X.functionField Y.functionField)
  have h := hfields.flip.paste_vert (affinePreimage_isPullback p U hU)
  rw [genericGerm_fromSpec, genericGerm_fromSpec] at h
  exact h.flip

end

end HodgeConjecture.CollisionFoundations
