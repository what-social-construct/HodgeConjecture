module

public import HodgeConjecture.Correspondence.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

/-!
# Étale scheme correspondences

Finite étale correspondences are the first concrete admissible class for the
cover-generated branch of the project.

Both conditions are useful:

* étaleness is stable under base change and composition, so the ordinary
  fiber product used to compose spans remains étale over either endpoint;
* finiteness makes the legs proper and keeps the carrier in the expected
  dimension.

This module packages those properties for both legs of a scheme
correspondence and proves closure under isomorphism, the diagonal identity,
transpose, and fiber-product composition.  Collision-specific applications
are kept in `Correspondence.CollisionEtale`.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X Y Z : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}

/-- Both legs of a scheme correspondence are étale. -/
structure HasEtaleLegs
    (P : SchemeCorrespondence pX pY) : Prop where
  left_etale : Etale P.left
  right_etale : Etale P.right

/-- Both legs of a scheme correspondence are finite étale. -/
structure HasFiniteEtaleLegs
    (P : SchemeCorrespondence pX pY) : Prop
    extends HasEtaleLegs P where
  left_finite : IsFinite P.left
  right_finite : IsFinite P.right

namespace HasEtaleLegs

/-- Étaleness of both legs is invariant under correspondence isomorphism. -/
theorem of_isom
    {P Q : SchemeCorrespondence pX pY}
    (e : SchemeCorrespondence.Isom P Q)
    (hP : HasEtaleLegs P) :
    HasEtaleLegs Q := by
  constructor
  · apply
      (MorphismProperty.cancel_left_of_respectsIso
        @Etale e.carrierIso.hom Q.left).mp
    rw [e.hom_left]
    exact hP.left_etale
  · apply
      (MorphismProperty.cancel_left_of_respectsIso
        @Etale e.carrierIso.hom Q.right).mp
    rw [e.hom_right]
    exact hP.right_etale

/-- Isomorphic correspondences have étale legs simultaneously. -/
theorem isom_iff
    {P Q : SchemeCorrespondence pX pY}
    (e : SchemeCorrespondence.Isom P Q) :
    HasEtaleLegs P ↔ HasEtaleLegs Q :=
  ⟨of_isom e, of_isom e.symm⟩

/-- The diagonal identity correspondence has étale legs. -/
theorem identity (pX : X ⟶ S) :
    HasEtaleLegs (SchemeCorrespondence.identity pX) := by
  constructor <;>
    exact MorphismProperty.id_mem @Etale X

/-- Reversing an étale correspondence preserves étaleness of its legs. -/
theorem transpose
    {P : SchemeCorrespondence pX pY}
    (hP : HasEtaleLegs P) :
    HasEtaleLegs P.transpose :=
  ⟨hP.right_etale, hP.left_etale⟩

/--
Fiber-product composition preserves étaleness of both legs.

The new left projection is the base change of `Q.left` followed by
`P.left`; the new right projection is the base change of `P.right` followed
by `Q.right`.
-/
theorem comp
    {P : SchemeCorrespondence pX pY}
    {Q : SchemeCorrespondence pY pZ}
    (hQ : HasEtaleLegs Q)
    (hP : HasEtaleLegs P) :
    HasEtaleLegs (Q.comp P) := by
  exact
    ⟨MorphismProperty.comp_mem @Etale
        (pullback.fst P.right Q.left) P.left
        (MorphismProperty.pullback_fst
          P.right Q.left hQ.left_etale)
        hP.left_etale,
      MorphismProperty.comp_mem @Etale
        (pullback.snd P.right Q.left) Q.right
        (MorphismProperty.pullback_snd
          P.right Q.left hP.right_etale)
        hQ.right_etale⟩

end HasEtaleLegs

namespace HasFiniteEtaleLegs

/--
Finiteness and étaleness of both legs are invariant under correspondence
isomorphism.
-/
theorem of_isom
    {P Q : SchemeCorrespondence pX pY}
    (e : SchemeCorrespondence.Isom P Q)
    (hP : HasFiniteEtaleLegs P) :
    HasFiniteEtaleLegs Q := by
  refine
    ⟨hP.toHasEtaleLegs.of_isom e, ?_, ?_⟩
  · apply
      (MorphismProperty.cancel_left_of_respectsIso
        @IsFinite e.carrierIso.hom Q.left).mp
    rw [e.hom_left]
    exact hP.left_finite
  · apply
      (MorphismProperty.cancel_left_of_respectsIso
        @IsFinite e.carrierIso.hom Q.right).mp
    rw [e.hom_right]
    exact hP.right_finite

/-- Isomorphic correspondences have finite étale legs simultaneously. -/
theorem isom_iff
    {P Q : SchemeCorrespondence pX pY}
    (e : SchemeCorrespondence.Isom P Q) :
    HasFiniteEtaleLegs P ↔ HasFiniteEtaleLegs Q :=
  ⟨of_isom e, of_isom e.symm⟩

/-- The diagonal identity correspondence has finite étale legs. -/
theorem identity (pX : X ⟶ S) :
    HasFiniteEtaleLegs (SchemeCorrespondence.identity pX) := by
  refine ⟨HasEtaleLegs.identity pX, ?_, ?_⟩ <;>
    exact MorphismProperty.id_mem @IsFinite X

/-- Reversing a finite étale correspondence preserves both conditions. -/
theorem transpose
    {P : SchemeCorrespondence pX pY}
    (hP : HasFiniteEtaleLegs P) :
    HasFiniteEtaleLegs P.transpose :=
  ⟨hP.toHasEtaleLegs.transpose,
    hP.right_finite, hP.left_finite⟩

/-- Fiber-product composition preserves finite étale legs. -/
theorem comp
    {P : SchemeCorrespondence pX pY}
    {Q : SchemeCorrespondence pY pZ}
    (hQ : HasFiniteEtaleLegs Q)
    (hP : HasFiniteEtaleLegs P) :
    HasFiniteEtaleLegs (Q.comp P) := by
  refine ⟨hQ.toHasEtaleLegs.comp hP.toHasEtaleLegs, ?_, ?_⟩
  · exact
      MorphismProperty.comp_mem @IsFinite
        (pullback.fst P.right Q.left) P.left
        (MorphismProperty.pullback_fst
          P.right Q.left hQ.left_finite)
        hP.left_finite
  · exact
      MorphismProperty.comp_mem @IsFinite
        (pullback.snd P.right Q.left) Q.right
        (MorphismProperty.pullback_snd
          P.right Q.left hP.right_finite)
        hQ.right_finite

/--
A correspondence with finite left leg has proper support whenever the target
is separated over the base.
-/
theorem isProperSupport
    {P : SchemeCorrespondence pX pY}
    (hP : HasFiniteEtaleLegs P)
    [IsSeparated pY] :
    P.IsProperSupport := by
  letI : IsFinite P.left := hP.left_finite
  letI : IsProper
      (P.toAmbientProduct ≫ pullback.fst pX pY) := by
    rw [P.toAmbientProduct_fst]
    infer_instance
  letI : IsSeparated (pullback.fst pX pY) :=
    MorphismProperty.pullback_fst
      pX pY (inferInstance : IsSeparated pY)
  exact
    IsProper.of_comp
      P.toAmbientProduct (pullback.fst pX pY)

end HasFiniteEtaleLegs

end SchemeCorrespondence

end

end HodgeConjecture
