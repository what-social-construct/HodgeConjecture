module

public import HodgeConjecture.Boundary.Normalization.InertiaDiagram

@[expose] public section

/-!
# Conjugate normalization legs

Let `B` be an affine base with fraction field `K`, let `L / K` be a
marked finite extension, and let `N / K` be a supplied normal closure.
Every element of `Gal(N / K)` conjugates the marked embedding `L → N`.
Restricting that conjugate embedding to integral closures gives a canonical
map

`Norm_N(Spec B) ⟶ Norm_L(Spec B)`.

These maps are the presentation-independent form of the conjugate
normalization legs used in the Jacobian-collision development.  They depend
only on the corresponding right coset modulo the subgroup fixing the marked
copy of `L`, and every leg lies over `Spec B`.

The existing `NormalizationInertia.Diagram` deliberately records centers by
double-coset classes without asserting that they arise from these canonical
legs.  `Diagram.ConjugateCenterRealization` is the separate geometric input
which makes that identification.  Keeping it separate avoids building an
unproved center-classification theorem into the diagram itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace NormalizationInertia

section ConjugateLegs

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- The conjugate of the marked embedding `L → N`, regarded as a
`B`-algebra homomorphism. -/
def conjugateNormalClosureEmbeddingOverBase
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup) :
    L →ₐ[B] N :=
  (g.restrictScalars B).toAlgHom.comp
    (normalClosureEmbeddingOverBase (B := B) D)

/-- Right multiplication by the subgroup fixing the marked copy of `L`
does not change the conjugate embedding. -/
theorem conjugateNormalClosureEmbeddingOverBase_right_mul
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    conjugateNormalClosureEmbeddingOverBase (B := B) D
        (g * (h : D.galoisGroup)) =
      conjugateNormalClosureEmbeddingOverBase (B := B) D g := by
  apply AlgHom.ext
  intro x
  change g ((h : D.galoisGroup) (D.embedding x)) = g (D.embedding x)
  congr 1
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      D.intermediateField (h : D.galoisGroup)).mp h.property
      (D.embedding x) ⟨x, rfl⟩

/-- The map between integral closures induced by a conjugate marked
embedding. -/
def conjugateNormalizationRingMap
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup) :
    IntermediateNormalizationRing (B := B) (L := L) →ₐ[B]
      NormalClosureNormalizationRing (B := B) (N := N) :=
  CollisionFoundations.normalizationMap N
    (conjugateNormalClosureEmbeddingOverBase (B := B) D g)

/-- The conjugate normalization ring map depends only on the right coset
modulo the subgroup fixing the marked intermediate field. -/
theorem conjugateNormalizationRingMap_right_mul
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    conjugateNormalizationRingMap (B := B) D
        (g * (h : D.galoisGroup)) =
      conjugateNormalizationRingMap (B := B) D g := by
  unfold conjugateNormalizationRingMap
  rw [conjugateNormalClosureEmbeddingOverBase_right_mul
    (B := B) D g h]

/-- The canonical conjugate leg from the normal-closure normalization to
the marked intermediate normalization. -/
def conjugateNormalClosureToIntermediateNormalization
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup) :
    normalClosureNormalization (B := B) (N := N) ⟶
      intermediateNormalization (B := B) (L := L) :=
  Spec.map
    (CommRingCat.ofHom
      (conjugateNormalizationRingMap (B := B) D g).toRingHom)

/-- The conjugate normalization leg depends only on the right coset modulo
the subgroup fixing the marked intermediate field. -/
theorem conjugateNormalClosureToIntermediateNormalization_right_mul
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    conjugateNormalClosureToIntermediateNormalization (B := B) D
        (g * (h : D.galoisGroup)) =
      conjugateNormalClosureToIntermediateNormalization (B := B) D g := by
  unfold conjugateNormalClosureToIntermediateNormalization
  rw [conjugateNormalizationRingMap_right_mul (B := B) D g h]

/-- The identity conjugate leg is the marked normalization leg already
present in the normalization triangle. -/
theorem conjugateNormalClosureToIntermediateNormalization_one
    (D : CollisionFoundations.NormalClosureData K L N) :
    conjugateNormalClosureToIntermediateNormalization (B := B) D 1 =
      normalClosureToIntermediateNormalization (B := B) D := by
  unfold conjugateNormalClosureToIntermediateNormalization
    normalClosureToIntermediateNormalization
    conjugateNormalizationRingMap
    conjugateNormalClosureEmbeddingOverBase
    CollisionFoundations.normalizationDomination
  rfl

/-- Every conjugate normalization leg lies over the same affine base. -/
theorem conjugateNormalClosureToIntermediateNormalization_comp_toBase
    (D : CollisionFoundations.NormalClosureData K L N)
    (g : D.galoisGroup) :
    conjugateNormalClosureToIntermediateNormalization (B := B) D g ≫
        intermediateNormalizationToBase (B := B) (L := L) =
      normalClosureNormalizationToBase (B := B) (N := N) :=
  CollisionFoundations.normalizationDomination_comp_toBase N
    (conjugateNormalClosureEmbeddingOverBase (B := B) D g)

end ConjugateLegs

section CenterRealization

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

/--
The geometric identification of the center indexed by a representative
`g` with contraction along the canonical conjugate normalization leg.

This is intentionally separate from `Diagram`: the diagram supplies a
double-coset-indexed family of centers, while this proposition asserts that
the supplied family is the one produced by conjugating the marked embedding.
-/
structure ConjugateCenterRealization
    (D : Diagram C) : Prop where
  centerAtRepresentative :
    ∀ E g,
      D.centerAtClass E
          (DoubleCoset.mk
            (CollisionFoundations.decompositionGroupAt K
              (D.valuationAt E).valuationRing)
            C.normalClosure.intermediateFixingSubgroup
            g) =
        (conjugateNormalClosureToIntermediateNormalization
          (B := B) C.normalClosure g).base E.1

end Diagram

end CenterRealization

end NormalizationInertia

end

end HodgeConjecture
