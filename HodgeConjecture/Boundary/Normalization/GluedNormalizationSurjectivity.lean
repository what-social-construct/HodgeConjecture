module

public import HodgeConjecture.Boundary.Normalization.GluedNormalizationProperties
public import HodgeConjecture.Boundary.Normalization.GluedNormalClosureRefinement

@[expose] public section

/-!
# Surjectivity of the original global normalization maps

Lying-over makes the original normalization charts surjective over their
base opens, and target locality gives surjectivity of the glued structural
map for any fixed field extension. The original marked refinement is
surjective by lifting a point through its actual affine refinement and
then its original chart inclusion into the glued scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles NormalizationInertia

noncomputable section

universe u

/-- The original glued normalization map is onto for any fixed extension
of the function field of an integral scheme. -/
theorem gluedNormalizationToBase_surjective (X : Scheme.{u}) [IsIntegral X]
    (N : Type u) [Field N] [Algebra X.functionField N] :
    Surjective (gluedNormalizationToBase X N) := by
  apply (gluedNormalizationToBase_property_iff X N (@Surjective)).mpr
  intro U
  letI : Algebra Γ(X, U.val) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
  let i : Γ(X, U.val) →+* normalizedCoordinateRing Γ(X, U.val) N := algebraMap _ _
  have hi : i.IsIntegral := fun x => integralClosure.isIntegral x
  have hinj : Function.Injective i := by
    intro b c h
    apply X.germToFunctionField_injective U.val
    apply (algebraMap X.functionField N).injective
    exact congrArg (fun z : normalizedCoordinateRing Γ(X, U.val) N => (z : N)) h
  haveI : Surjective (normalizedModelToBase Γ(X, U.val) N) :=
    ⟨hi.comap_surjective hinj⟩
  infer_instance

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

/-- Every point of the original cover lifts through its actual marked
affine refinement and hence through the same global marked map. -/
theorem gluedNormalClosureToCover_surjective
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    Surjective (gluedNormalClosureToCover p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  constructor
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := p.base y) (by trivial)
  let A : NonemptyAffineChart X := ⟨U, hU, ⟨⟨p.base y, hy⟩⟩⟩
  letI : Nonempty A.val := A.property.2
  let q := finiteEtaleAffineNormalClosureToPreimage p A.val A.property.1
    (fun y => hY y.val)
  haveI : Surjective q := finiteEtaleAffineNormalClosureToPreimage_surjective
    p A.val A.property.1 (fun y => hY y.val)
  obtain ⟨z, hz⟩ := q.surjective ⟨y, hy⟩
  refine ⟨(normalizationChartToGlued X N A).base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, normalizationChartToGlued_comp_toCover]
  rw [Scheme.Hom.comp_apply]
  change (p ⁻¹ᵁ A.val).ι.base (q.base z) = y
  rw [hz]
  rfl

end

end HodgeConjecture.CollisionFoundations
