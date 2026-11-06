module

public import HodgeConjecture.Boundary.Normalization.ConjugateNormalization
public import HodgeConjecture.Boundary.Normalization.PrimeInertia
public import Mathlib.Algebra.Group.Subgroup.Pointwise

@[expose] public section

/-!
# Conjugate boundaries and codimension-one separation

This module constructs the boundary ideals attached to all conjugate copies
of a marked open sheet on a common normal-closure normalization.  For a
nontrivial subgroup `I` of the normal-closure Galois group, the
`fixedMovingBoundaryIdeal` combines

* the ideal of the `I`-fixed locus, and
* the boundary ideals of every conjugate sheet moved by `I`.

`ConjugateBoundarySeparation` says that this combined ideal is contained in
no height-one prime.  The final theorem proves that this supplied geometric
separation condition implies `NoCodimensionOneRamification`.

The proof is conditional on exactly the geometric bridges it uses:

* `Diagram.ConjugateCenterRealization` identifies the packaged centers with
  the canonical conjugate normalization legs;
* `Diagram.ConjugateRamificationRealization` identifies the group-theoretic
  inertia index with the geometric ramification index; and
* the marked visible morphism is formally unramified over the affine base.

No compactification, purity, Chow correspondence, or projector-defect claim
is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

noncomputable section

universe u

namespace NormalizationInertia

section ConjugateGeometry

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}

/-- The Galois group indexing conjugate sheets of a normalized cover. -/
abbrev NormalizedCover.GaloisGroup
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j) :=
  C.normalClosure.galoisGroup

variable
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j)

/-- The canonical conjugate normalization leg attached to a Galois
element. -/
def conjugateToIntermediate
    (g : C.GaloisGroup) :
    normalClosureNormalization (B := B) (N := N) ⟶
      intermediateNormalization (B := B) (L := L) :=
  conjugateNormalClosureToIntermediateNormalization
    (B := B) C.normalClosure g

omit [IsFractionRing B K] in
/-- The conjugate normalization leg depends only on the right coset modulo
the marked intermediate fixing subgroup. -/
theorem conjugateToIntermediate_right_mul
    (g : C.GaloisGroup)
    (h : C.normalClosure.intermediateFixingSubgroup) :
    conjugateToIntermediate C
        (g * (h : C.GaloisGroup)) =
      conjugateToIntermediate C g :=
  conjugateNormalClosureToIntermediateNormalization_right_mul
    (B := B) C.normalClosure g h

/-- The inverse image on the common normal-closure normalization of one
conjugate copy of the marked visible open. -/
def pulledBackConjugateVisibleOpen
    (g : C.GaloisGroup) :
    Set (normalClosureNormalization (B := B) (N := N)) :=
  (conjugateToIntermediate C g).base ⁻¹'
    Set.range j.base

omit [IsFractionRing B K] in
/-- The pulled-back visible open depends only on the right coset of its
representative. -/
theorem pulledBackConjugateVisibleOpen_right_mul
    (g : C.GaloisGroup)
    (h : C.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateVisibleOpen C
        (g * (h : C.GaloisGroup)) =
      pulledBackConjugateVisibleOpen C g := by
  unfold pulledBackConjugateVisibleOpen
  rw [conjugateToIntermediate_right_mul C g h]

/-- The closed complement of a pulled-back conjugate visible sheet. -/
def pulledBackConjugateBoundary
    (g : C.GaloisGroup) :
    Set (PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))) :=
  (pulledBackConjugateVisibleOpen C g)ᶜ

omit [IsFractionRing B K] in
/-- The pulled-back boundary depends only on the right coset of its
representative. -/
theorem pulledBackConjugateBoundary_right_mul
    (g : C.GaloisGroup)
    (h : C.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateBoundary C
        (g * (h : C.GaloisGroup)) =
      pulledBackConjugateBoundary C g := by
  unfold pulledBackConjugateBoundary
  rw [pulledBackConjugateVisibleOpen_right_mul C g h]

/-- The radical ideal cutting out one pulled-back conjugate boundary. -/
def pulledBackConjugateBoundaryIdeal
    (g : C.GaloisGroup) :
    Ideal (NormalClosureNormalizationRing (B := B) (N := N)) :=
  PrimeSpectrum.vanishingIdeal (pulledBackConjugateBoundary C g)

omit [IsFractionRing B K] in
/-- The pulled-back boundary ideal is indexed by the right coset of the
conjugate sheet. -/
theorem pulledBackConjugateBoundaryIdeal_right_mul
    (g : C.GaloisGroup)
    (h : C.normalClosure.intermediateFixingSubgroup) :
    pulledBackConjugateBoundaryIdeal C
        (g * (h : C.GaloisGroup)) =
      pulledBackConjugateBoundaryIdeal C g := by
  unfold pulledBackConjugateBoundaryIdeal
  rw [pulledBackConjugateBoundary_right_mul C g h]

omit [IsFractionRing B K] in
/-- A pulled-back conjugate boundary is closed. -/
theorem pulledBackConjugateBoundary_isClosed
    (g : C.GaloisGroup) :
    IsClosed (pulledBackConjugateBoundary C g) := by
  letI : IsOpenImmersion j := C.visibleOpen
  apply IsOpen.isClosed_compl
  exact
    (IsOpenImmersion.isOpen_range j).preimage
      (conjugateToIntermediate C g).base.hom.continuous_toFun

omit [IsFractionRing B K] in
/-- The canonical ideal cuts out exactly the pulled-back boundary. -/
theorem zeroLocus_pulledBackConjugateBoundaryIdeal
    (g : C.GaloisGroup) :
    PrimeSpectrum.zeroLocus (pulledBackConjugateBoundaryIdeal C g) =
      pulledBackConjugateBoundary C g := by
  rw [pulledBackConjugateBoundaryIdeal,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (pulledBackConjugateBoundary_isClosed C g).closure_eq]

omit [IsFractionRing B K] in
/-- Boundary membership is membership of the conjugate center in the
deleted boundary of the marked open. -/
theorem mem_pulledBackConjugateBoundary_iff
    (g : C.GaloisGroup)
    (p : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))) :
    p ∈ pulledBackConjugateBoundary C g ↔
      (conjugateToIntermediate C g).base p ∈
        (Set.range j.base)ᶜ :=
  Iff.rfl

omit [IsFractionRing B K] in
/-- Membership in a pulled-back boundary gives containment of its
canonical ideal in the point prime. -/
theorem pulledBackConjugateBoundaryIdeal_le
    (g : C.GaloisGroup)
    (p : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N)))
    (hp : p ∈ pulledBackConjugateBoundary C g) :
    pulledBackConjugateBoundaryIdeal C g ≤ p.asIdeal := by
  intro t ht
  exact
    (PrimeSpectrum.mem_vanishingIdeal
      (pulledBackConjugateBoundary C g) t).mp ht p hp

end ConjugateGeometry

section FixedMovingIdeals

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

/-- The scheme-theoretic fixed-locus ideal generated by all differences
`σ(t) - t` for elements of a subgroup. -/
noncomputable def fixedLocusIdeal
    (I : Subgroup C.GaloisGroup) :
    Ideal (NormalClosureNormalizationRing (B := B) (N := N)) :=
  Ideal.span
    {z | ∃ (σ : I)
        (t : NormalClosureNormalizationRing (B := B) (N := N)),
      z = normalClosureNormalizationRingEquiv (B := B) σ.1 t - t}

omit [IsFractionRing B K] [IsScalarTower B K L] in
/-- Containment of the fixed-locus ideal is checked on its generating
differences. -/
theorem fixedLocusIdeal_le_iff
    (I : Subgroup C.GaloisGroup)
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N))) :
    fixedLocusIdeal I ≤ Q ↔
      ∀ (σ : I)
        (t : NormalClosureNormalizationRing (B := B) (N := N)),
        normalClosureNormalizationRingEquiv (B := B) σ.1 t - t ∈ Q := by
  rw [fixedLocusIdeal, Ideal.span_le]
  constructor
  · intro h σ t
    exact h ⟨σ, t, rfl⟩
  · rintro h z ⟨σ, t, rfl⟩
    exact h σ t

/-- The sum of boundary ideals over all conjugate sheets moved by `I`.
The condition `I ≤ gHg⁻¹` is precisely the condition that `I` fixes the
sheet represented by `gH`. -/
def movingBoundaryIdeal
    (boundaryIdeal : C.GaloisGroup →
      Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    (I : Subgroup C.GaloisGroup) :
    Ideal (NormalClosureNormalizationRing (B := B) (N := N)) :=
  ⨆ (g : C.GaloisGroup)
      (_ : ¬ I ≤ C.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom),
    boundaryIdeal g

/-- The canonical ideal combining the fixed locus of `I` with the
boundaries of every conjugate sheet moved by `I`. -/
def fixedMovingBoundaryIdeal
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j)
    (I : Subgroup C.GaloisGroup) :
    Ideal (NormalClosureNormalizationRing (B := B) (N := N)) :=
  fixedLocusIdeal I +
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I

omit [Algebra B K] [IsFractionRing B K]
  [IsScalarTower B K L] [IsScalarTower B K N] in
/-- Membership in the moving-boundary sum is tested sheet by sheet. -/
theorem movingBoundaryIdeal_le_iff
    (boundaryIdeal : C.GaloisGroup →
      Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    (I : Subgroup C.GaloisGroup)
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N))) :
    movingBoundaryIdeal boundaryIdeal I ≤ Q ↔
      ∀ g, ¬ I ≤ C.normalClosure.intermediateFixingSubgroup.map
          (MulAut.conj g).toMonoidHom →
        boundaryIdeal g ≤ Q := by
  simp [movingBoundaryIdeal]

omit [IsFractionRing B K] in
/-- Containment of the fixed--moving ideal is containment of both of its
summands. -/
@[simp]
theorem fixedMovingBoundaryIdeal_le_iff
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j)
    (I : Subgroup C.GaloisGroup)
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N))) :
    fixedMovingBoundaryIdeal C I ≤ Q ↔
      fixedLocusIdeal I ≤ Q ∧
        movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I ≤ Q := by
  simp [fixedMovingBoundaryIdeal]

omit [IsFractionRing B K] [IsScalarTower B K L] in
/-- Fixed-locus ideals grow with the acting subgroup. -/
theorem fixedLocusIdeal_mono
    {I I' : Subgroup C.GaloisGroup}
    (h : I ≤ I') :
    fixedLocusIdeal I ≤ fixedLocusIdeal I' := by
  rw [fixedLocusIdeal_le_iff]
  intro σ t
  apply Ideal.subset_span
  exact ⟨⟨σ.1, h σ.2⟩, t, rfl⟩

/-- The height-one-prime form of conjugate-boundary separation.  It is the
geometric input consumed by the codimension-one endgame below. -/
def ConjugateBoundarySeparation
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j) : Prop :=
  ∀ (I : Subgroup C.GaloisGroup),
    I ≠ ⊥ →
      ∀ p : PrimeSpectrum
          (NormalClosureNormalizationRing (B := B) (N := N)),
        p.asIdeal.height = 1 →
          ¬ fixedMovingBoundaryIdeal C I ≤ p.asIdeal

end FixedMovingIdeals

section SeparationEndgame

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [IsNoetherianRing B]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

variable (D : Diagram C)

/-- The two independent center-identification inputs needed to relate the
canonical boundary ideals to the double-coset ramification data. -/
structure ConjugateBoundaryData : Prop where
  centerRealization : D.ConjugateCenterRealization
  ramificationRealization : D.ConjugateRamificationRealization

variable {D}

omit [IsFractionRing B K] in
/-- A conjugate center with nontrivial relative inertia lies in the
corresponding pulled-back boundary on the common normalization. -/
theorem ramifiedPoint_mem_pulledBackConjugateBoundary
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (g : C.GaloisGroup)
    (hIndex :
      D.inertiaIndex E
        (DoubleCoset.mk
          (CollisionFoundations.decompositionGroupAt K
            (D.valuationAt E).valuationRing)
          C.normalClosure.intermediateFixingSubgroup
          g) ≠ 1) :
    E.1 ∈ pulledBackConjugateBoundary C g := by
  rw [mem_pulledBackConjugateBoundary_iff]
  change
    (conjugateNormalClosureToIntermediateNormalization
      (B := B) C.normalClosure g).base E.1 ∈ D.boundary
  rw [← R.centerRealization.centerAtRepresentative E g]
  exact
    D.ramifiedCenter_mem_boundary
      R.ramificationRealization hFormal E _ hIndex

omit [IsFractionRing B K] in
/-- Boundary membership at a ramified center yields containment of the
canonical conjugate boundary ideal in its height-one prime. -/
theorem pulledBackConjugateBoundaryIdeal_le_ramifiedPrime
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (g : C.GaloisGroup)
    (hIndex :
      D.inertiaIndex E
        (DoubleCoset.mk
          (CollisionFoundations.decompositionGroupAt K
            (D.valuationAt E).valuationRing)
          C.normalClosure.intermediateFixingSubgroup
          g) ≠ 1) :
    pulledBackConjugateBoundaryIdeal C g ≤ E.1.asIdeal :=
  pulledBackConjugateBoundaryIdeal_le C g E.1
    (D.ramifiedPoint_mem_pulledBackConjugateBoundary
      R hFormal E g hIndex)

omit [IsFractionRing B K] in
/-- Every boundary ideal for a sheet moved by a subgroup of the actual
valuation inertia group is contained in the ramified center prime. -/
theorem movingBoundaryIdeal_le_ramifiedPrime
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (I : Subgroup C.GaloisGroup)
    (hI :
      I ≤ CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing) :
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I ≤
      E.1.asIdeal := by
  rw [movingBoundaryIdeal_le_iff]
  intro g hg
  apply D.pulledBackConjugateBoundaryIdeal_le_ramifiedPrime
    R hFormal E g
  change
    CollisionFoundations.inertiaQuotientIndex
      (CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing)
      (C.normalClosure.intermediateFixingSubgroup.map
        (MulAut.conj g).toMonoidHom) ≠ 1
  exact
    CollisionFoundations.inertiaQuotientIndex_ne_one _ _
      (fun hInertia ↦ hg (hI.trans hInertia))

omit [IsFractionRing B K] [IsNoetherianRing B] in
/-- Valuation inertia fixes the residue field, so its fixed-locus ideal is
contained in the center prime. -/
theorem actualInertiaFixedLocusIdeal_le_ramifiedPrime
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    fixedLocusIdeal
        (C := C)
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing) ≤ E.1.asIdeal := by
  rw [fixedLocusIdeal_le_iff]
  intro σ t
  exact D.valuationInertia_sub_centerPrime E σ t

omit [IsFractionRing B K] in
/-- The fixed--moving ideal for the actual inertia group is contained in
the corresponding ramified height-one prime. -/
theorem actualInertiaFixedMovingBoundaryIdeal_le
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    fixedMovingBoundaryIdeal C
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing) ≤ E.1.asIdeal := by
  rw [fixedMovingBoundaryIdeal_le_iff]
  exact ⟨
    D.actualInertiaFixedLocusIdeal_le_ramifiedPrime E,
    D.movingBoundaryIdeal_le_ramifiedPrime R hFormal E _ le_rfl⟩

omit [IsFractionRing B K] in
/-- Conjugate-boundary separation excludes every ramified height-one
point. -/
theorem ramifiedCodimensionOnePoint_isEmpty_of_conjugateBoundarySeparation
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C) :
    IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N)) := by
  constructor
  intro E
  exact hSeparation
    (CollisionFoundations.inertiaGroupAt K
      (D.valuationAt E).valuationRing)
    (D.inertia_nontrivial E) E.1 E.2.1
    (D.actualInertiaFixedMovingBoundaryIdeal_le R hFormal E)

omit [IsFractionRing B K] in
/-- A supplied conjugate-boundary separation theorem gives the exact local
input consumed by purity: every height-one point of the normal-closure
normalization is unramified over the affine base. -/
theorem noCodimensionOneRamification_of_conjugateBoundarySeparation
    (R : D.ConjugateBoundaryData)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C) :
    NoCodimensionOneRamification (B := B) (N := N) :=
  noCodimensionOneRamification_of_ramifiedCodimensionOnePoint_isEmpty
    (D.ramifiedCodimensionOnePoint_isEmpty_of_conjugateBoundarySeparation
      R hFormal hSeparation)

end Diagram

end SeparationEndgame

end NormalizationInertia

end

end HodgeConjecture
