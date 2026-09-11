import HodgeConjecture.Boundary.Normalization.Model
import HodgeConjecture.Boundary.Normalization.NormalClosure
import HodgeConjecture.Boundary.Normalization.ValuationInertia
import HodgeConjecture.Boundary.Normalization.VisibleRamification
import HodgeConjecture.Boundary.Sheets.DecompositionSheets
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Unramified.Locus

/-!
# Abstract normalization–inertia diagrams

This module extracts the presentation-independent content of the polynomial
normalization diagram.

For an affine domain `B` with fraction field `K`, a marked finite extension
`L / K`, and a finite normal closure `N / K`, it constructs the canonical
affine normalization triangle

`Norm_N(B) ⟶ Norm_L(B) ⟶ Spec B`.

A `NormalizationInertia.Diagram` adds, at every ramified height-one point of
`Norm_N(B)`,

* a centered discrete valuation of `N`;
* its nontrivial inertia subgroup;
* centers on `Norm_L(B)` indexed by the double-coset sheets `D \ G / H`;
* compatibility of those centers with the normalization triangle.

An arbitrary open scheme `U ⟶ Norm_L(B)` marks the visible locus.  Formal
unramifiedness on `U` forces every visible center to have ramification index
one.  Consequently every center with nontrivial relative inertia lies in the
deleted boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace NormalizationInertia

section Models

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- The integral closure of `B` in the marked intermediate field `L`. -/
abbrev IntermediateNormalizationRing :=
  CollisionFoundations.normalizedCoordinateRing B L

/-- The intermediate normalization `Norm_L(Spec B)`. -/
def intermediateNormalization : Scheme :=
  CollisionFoundations.normalizedAffineModel B L

/-- The intermediate normalization mapped to the affine base. -/
def intermediateNormalizationToBase :
    intermediateNormalization (B := B) (L := L) ⟶
      Spec (.of B) :=
  CollisionFoundations.normalizedModelToBase B L

/--
The marked embedding `L ↪ N`, regarded as an algebra homomorphism over the
affine base ring `B`.
-/
def normalClosureEmbeddingOverBase
    (D : CollisionFoundations.NormalClosureData K L N) :
    L →ₐ[B] N :=
  { D.embedding.toRingHom with
    commutes' := fun b ↦ by
      change D.embedding (algebraMap B L b) = algebraMap B N b
      calc
        D.embedding (algebraMap B L b) =
            D.embedding (algebraMap K L (algebraMap B K b)) := by
              rw [IsScalarTower.algebraMap_apply B K L]
        _ = algebraMap K N (algebraMap B K b) :=
          D.embedding.commutes (algebraMap B K b)
        _ = algebraMap B N b :=
          (IsScalarTower.algebraMap_apply B K N b).symm }

/-- The integral closure of `B` in the normal closure field `N`. -/
abbrev NormalClosureNormalizationRing :=
  CollisionFoundations.normalizedCoordinateRing B N

/-- The normal-closure normalization `Norm_N(Spec B)`. -/
def normalClosureNormalization : Scheme :=
  CollisionFoundations.normalizedAffineModel B N

/-- The normal-closure normalization mapped to the affine base. -/
def normalClosureNormalizationToBase :
    normalClosureNormalization (B := B) (N := N) ⟶
      Spec (.of B) :=
  CollisionFoundations.normalizedModelToBase B N

/-- The normal-closure model dominates the marked intermediate normalization. -/
def normalClosureToIntermediateNormalization
    (D : CollisionFoundations.NormalClosureData K L N) :
    normalClosureNormalization (B := B) (N := N) ⟶
      intermediateNormalization (B := B) (L := L) :=
  CollisionFoundations.normalizationDomination N
    (normalClosureEmbeddingOverBase (B := B) D)

omit [IsFractionRing B K] in
/-- The canonical affine normalization triangle commutes. -/
theorem normalClosureToIntermediateNormalization_comp_toBase
    (D : CollisionFoundations.NormalClosureData K L N) :
    normalClosureToIntermediateNormalization (B := B) D ≫
        intermediateNormalizationToBase (B := B) (L := L) =
      normalClosureNormalizationToBase (B := B) (N := N) :=
  CollisionFoundations.normalizationDomination_comp_toBase N
    (normalClosureEmbeddingOverBase (B := B) D)

/--
The reusable finite normalized cover, with an arbitrary marked open scheme
`U`.  Finiteness and openness are explicit because they depend on the
geometric application.
-/
structure NormalizedCover
    (U : Scheme.{u})
    (j : U ⟶ intermediateNormalization (B := B) (L := L)) where
  normalClosure : CollisionFoundations.NormalClosureData K L N
  finiteIntermediateModel :
    Module.Finite B (IntermediateNormalizationRing (B := B) (L := L))
  finiteNormalClosureModel :
    Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N))
  visibleOpen : IsOpenImmersion j

end Models

section RamifiedPoints

variable {B K N : Type u}
variable [CommRing B] [Field K] [Field N]
variable [Algebra B N] [Algebra K N]

/-- Absence of ramification at every height-one point of `Norm_N(Spec B)`. -/
def NoCodimensionOneRamification : Prop :=
  ∀ q :
      PrimeSpectrum
        (NormalClosureNormalizationRing (B := B) (N := N)),
    q.asIdeal.primeHeight = 1 →
      Algebra.IsUnramifiedAt B q.asIdeal

/-- A ramified height-one point of the normal-closure normalization. -/
def RamifiedCodimensionOnePoint :=
  { q :
      PrimeSpectrum
        (NormalClosureNormalizationRing (B := B) (N := N)) //
      q.asIdeal.primeHeight = 1 ∧
        ¬ Algebra.IsUnramifiedAt B q.asIdeal }

/-- Universal codimension-one unramifiedness rules out ramified height-one
points. -/
theorem ramifiedCodimensionOnePoint_isEmpty_of_noCodimensionOneRamification
    (h : NoCodimensionOneRamification (B := B) (N := N)) :
    IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N)) := by
  constructor
  rintro ⟨q, hq, hRamified⟩
  exact hRamified (h q hq)

/-- If there are no ramified height-one points, then the normalization is
unramified at every height-one point. -/
theorem noCodimensionOneRamification_of_ramifiedCodimensionOnePoint_isEmpty
    (h : IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N))) :
    NoCodimensionOneRamification (B := B) (N := N) := by
  intro q hq
  by_contra hRamified
  exact h.false ⟨q, hq, hRamified⟩

/-- Absence of codimension-one ramification is equivalently emptiness of the
type of ramified height-one points. -/
theorem noCodimensionOneRamification_iff_isEmpty :
    NoCodimensionOneRamification (B := B) (N := N) ↔
      IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N)) :=
  ⟨ramifiedCodimensionOnePoint_isEmpty_of_noCodimensionOneRamification,
    noCodimensionOneRamification_of_ramifiedCodimensionOnePoint_isEmpty⟩

/--
A discrete valuation tower is centered at a point of the normal-closure
normalization when its valuation ring contains the normalization ring and
its maximal ideal contracts to the chosen prime.
-/
def ValuationCenteredAt
    (V : CollisionFoundations.DiscreteValuationTower K (N := N))
    (q :
      PrimeSpectrum
        (NormalClosureNormalizationRing (B := B) (N := N))) : Prop :=
  ∃ centerMap :
      NormalClosureNormalizationRing (B := B) (N := N) →+*
        V.valuationRing,
    (∀ x,
      ((centerMap x : V.valuationRing) : N) = (x : N)) ∧
      (IsLocalRing.maximalIdeal V.valuationRing).comap centerMap =
        q.asIdeal

end RamifiedPoints

section Diagram

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}

/--
The normalization triangle together with the valuation-theoretic realization
of all conjugate Galois sheets over each ramified height-one point.
-/
structure Diagram
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j) where
  valuationAt :
    RamifiedCodimensionOnePoint (B := B) (N := N) →
      CollisionFoundations.DiscreteValuationTower K (N := N)
  valuation_centered :
    ∀ E, ValuationCenteredAt (B := B) (valuationAt E) E.1
  inertia_nontrivial :
    ∀ E,
      CollisionFoundations.inertiaGroupAt K
        (valuationAt E).valuationRing ≠ ⊥
  centerAtClass :
    ∀ E,
      CollisionFoundations.DecompositionSheetClasses
          (CollisionFoundations.decompositionGroupAt K
            (valuationAt E).valuationRing)
          C.normalClosure.intermediateFixingSubgroup →
        intermediateNormalization (B := B) (L := L)
  centerAtClass_mapsToBase :
    ∀ E q,
      (intermediateNormalizationToBase (B := B) (L := L)).base
          (centerAtClass E q) =
        (normalClosureNormalizationToBase (B := B) (N := N)).base E.1
  baseClass_center :
    ∀ E,
      centerAtClass E
          (DoubleCoset.mk
            (CollisionFoundations.decompositionGroupAt K
              (valuationAt E).valuationRing)
            C.normalClosure.intermediateFixingSubgroup
            1) =
        (normalClosureToIntermediateNormalization
          (B := B) C.normalClosure).base E.1

namespace Diagram

variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}
    (D : Diagram C)

/-- The double-coset classes indexing conjugate centers over one point. -/
abbrev sheetClasses
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :=
  CollisionFoundations.DecompositionSheetClasses
    (CollisionFoundations.decompositionGroupAt K
      (D.valuationAt E).valuationRing)
    C.normalClosure.intermediateFixingSubgroup

/-- The relative inertia index of a conjugate center. -/
noncomputable def inertiaIndex
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    D.sheetClasses E → ℕ :=
  CollisionFoundations.inertiaIndexAtDoubleCoset
    (CollisionFoundations.decompositionGroupAt K
      (D.valuationAt E).valuationRing)
    (CollisionFoundations.inertiaWithinDecomposition K
      (D.valuationAt E).valuationRing)
    C.normalClosure.intermediateFixingSubgroup

/-- The identity double-coset class corresponding to the marked base sheet. -/
def baseClass
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    D.sheetClasses E :=
  DoubleCoset.mk
    (CollisionFoundations.decompositionGroupAt K
      (D.valuationAt E).valuationRing)
    C.normalClosure.intermediateFixingSubgroup
    1

omit [IsFractionRing B K] in
/--
The double-coset inertia index at the identity class agrees with the
stabilizer index of the distinguished `G/H` sheet for the full valuation
inertia subgroup.
-/
theorem inertiaIndex_baseClass_eq_inertiaIndexAtSheet
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    D.inertiaIndex E (D.baseClass E) =
      CollisionFoundations.inertiaIndexAtSheet
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        ((1 : C.normalClosure.galoisGroup) :
          CollisionFoundations.GaloisSheets
            C.normalClosure.intermediateFixingSubgroup) := by
  rw [inertiaIndex, baseClass,
    CollisionFoundations.inertiaIndexAtDoubleCoset_mk,
    CollisionFoundations.inertiaIndexAtRepresentative_eq_inertiaIndexAtSheet]
  rfl

/-- A conjugate center is visible when it belongs to the marked open scheme. -/
def ConjugateCenterVisible
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E) : Prop :=
  D.centerAtClass E q ∈ Set.range j.base

/-- The deleted boundary of the marked open scheme in the normalization. -/
def boundary
    (_D : Diagram C) :
    Set (intermediateNormalization (B := B) (L := L)) :=
  (Set.range j.base)ᶜ

/-- Every nontrivially ramified conjugate center lies in the deleted boundary. -/
def RamifiedConjugateCentersInBoundaryAt
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    Prop :=
  ∀ q : D.sheetClasses E,
    D.inertiaIndex E q ≠ 1 →
      D.centerAtClass E q ∈ D.boundary

/-- The boundary condition at every ramified height-one point. -/
def RamifiedConjugateCentersInBoundary : Prop :=
  ∀ E, D.RamifiedConjugateCentersInBoundaryAt E

/-- A ramified divisor whose full positive-index orbit is hidden in the boundary. -/
def HasHiddenInertiaOrbit : Prop :=
  ∃ E,
    (∃ q : D.sheetClasses E, 1 < D.inertiaIndex E q) ∧
      D.RamifiedConjugateCentersInBoundaryAt E

/-- The boundary cannot support a complete hidden-inertia orbit. -/
def NoHiddenInertia : Prop :=
  ¬ D.HasHiddenInertiaOrbit

omit [IsFractionRing B K] in
/-- The identity double-coset center is contraction along the normalization leg. -/
theorem centerAtBaseClass
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    D.centerAtClass E
        (DoubleCoset.mk
          (CollisionFoundations.decompositionGroupAt K
            (D.valuationAt E).valuationRing)
          C.normalClosure.intermediateFixingSubgroup
          1) =
      (normalClosureToIntermediateNormalization
        (B := B) C.normalClosure).base E.1 :=
  D.baseClass_center E

omit [IsFractionRing B K] in
/-- Every packaged conjugate center lies over the same point of the base. -/
theorem conjugateCenter_mapsToBase
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E) :
    (intermediateNormalizationToBase (B := B) (L := L)).base
        (D.centerAtClass E q) =
      (normalClosureNormalizationToBase
        (B := B) (N := N)).base E.1 :=
  D.centerAtClass_mapsToBase E q

omit [IsFractionRing B K] in
/-- Nontrivial valuation inertia produces a sheet of relative index greater than one. -/
theorem exists_one_lt_inertiaIndex
    [PerfectField K]
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    ∃ q : D.sheetClasses E,
      1 < D.inertiaIndex E q := by
  let V := (D.valuationAt E).valuationRing
  letI : Finite C.normalClosure.galoisGroup :=
    C.normalClosure.finiteGaloisGroup
  have hWithin :
      CollisionFoundations.inertiaWithinDecomposition K V ≠ ⊥ := by
    intro hbot
    apply D.inertia_nontrivial E
    change
      (V.inertiaSubgroup K).map
          (V.decompositionSubgroup K).subtype = ⊥
    change V.inertiaSubgroup K = ⊥ at hbot
    rw [hbot, Subgroup.map_bot]
  exact
    CollisionFoundations.exists_doubleCoset_one_lt_inertiaIndex
      (CollisionFoundations.decompositionGroupAt K V)
      (CollisionFoundations.inertiaWithinDecomposition K V)
      C.normalClosure.intermediateFixingSubgroup
      C.normalClosure.intermediateFixingSubgroup_normalCore_eq_bot
      hWithin

omit [IsFractionRing B K] in
/-- Boundary containment and no hidden inertia exclude all ramified height-one points. -/
theorem ramifiedCodimensionOnePoint_isEmpty
    [PerfectField K]
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    IsEmpty (RamifiedCodimensionOnePoint (B := B) (N := N)) := by
  constructor
  intro E
  exact
    hNoHidden
      ⟨E, D.exists_one_lt_inertiaIndex E, hBoundary E⟩

omit [IsFractionRing B K] in
/-- The local conclusion consumed by purity: every height-one point is unramified. -/
theorem noCodimensionOneRamification
    [PerfectField K]
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    NoCodimensionOneRamification (B := B) (N := N) :=
  noCodimensionOneRamification_of_ramifiedCodimensionOnePoint_isEmpty
    (D.ramifiedCodimensionOnePoint_isEmpty hBoundary hNoHidden)

/-- The prime of the intermediate normalization represented by a sheet center. -/
def centerPrime
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E) :
    Ideal (IntermediateNormalizationRing (B := B) (L := L)) :=
  (D.centerAtClass E q).asIdeal

instance centerPrime_isPrime
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E) :
    (D.centerPrime E q).IsPrime :=
  (D.centerAtClass E q).isPrime

/-- The geometric ramification index at a selected conjugate center. -/
noncomputable def geometricRamificationIndex
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E) : ℕ :=
  Ideal.ramificationIdx
    (R := B)
    (S := IntermediateNormalizationRing (B := B) (L := L))
    ((algebraMap B
      (IntermediateNormalizationRing (B := B) (L := L))) :
        B →+* IntermediateNormalizationRing (B := B) (L := L))
    (Ideal.under
      (B := IntermediateNormalizationRing (B := B) (L := L))
      B (D.centerPrime E q))
    (D.centerPrime E q)

/--
The valuation-theoretic bridge between double-coset inertia and the
geometric ramification index of each selected center.
-/
structure ConjugateRamificationRealization : Prop where
  center_ne_bot :
    ∀ E q, D.centerPrime E q ≠ ⊥
  inertiaIndex_eq_geometricRamificationIndex :
    ∀ E q,
      D.inertiaIndex E q =
        D.geometricRamificationIndex E q

omit [IsFractionRing B K] in
/-- A visible conjugate center is unramified over the affine base. -/
theorem centerPrime_isUnramifiedAt_of_visible
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hVisible : D.ConjugateCenterVisible E q) :
    Algebra.IsUnramifiedAt B (D.centerPrime E q) := by
  letI : IsOpenImmersion j := C.visibleOpen
  letI :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ Spec.map
          (CommRingCat.ofHom
            (algebraMap B
              (IntermediateNormalizationRing (B := B) (L := L))))) := by
    change
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L))
    exact hFormal
  rcases hVisible with ⟨x, hx⟩
  change Algebra.IsUnramifiedAt B (D.centerAtClass E q).asIdeal
  rw [← hx]
  exact
    CollisionFoundations.isUnramifiedAt_of_openImmersion_comp_formallyUnramified
      j x

omit [IsFractionRing B K] in
/-- At a visible center, the geometric ramification index is one. -/
theorem geometricRamificationIndex_eq_one_of_visible
    [IsNoetherianRing B]
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hVisible : D.ConjugateCenterVisible E q) :
    D.geometricRamificationIndex E q = 1 := by
  letI :
      Module.Finite B
        (IntermediateNormalizationRing (B := B) (L := L)) :=
    C.finiteIntermediateModel
  letI :
      IsNoetherianRing
        (IntermediateNormalizationRing (B := B) (L := L)) :=
    IsNoetherianRing.of_finite B
      (IntermediateNormalizationRing (B := B) (L := L))
  letI :
      Algebra.IsUnramifiedAt B (D.centerPrime E q) :=
    D.centerPrime_isUnramifiedAt_of_visible E q hFormal hVisible
  exact
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R.center_ne_bot E q)

omit [IsFractionRing B K] in
/-- Formal unramifiedness sends every positive-inertia center to the boundary. -/
theorem ramifiedCenter_mem_boundary
    [IsNoetherianRing B]
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (q : D.sheetClasses E)
    (hq : D.inertiaIndex E q ≠ 1) :
    D.centerAtClass E q ∈ D.boundary := by
  change D.centerAtClass E q ∉ Set.range j.base
  intro hVisible
  apply hq
  rw [R.inertiaIndex_eq_geometricRamificationIndex]
  exact
    D.geometricRamificationIndex_eq_one_of_visible
      R E q hFormal hVisible

omit [IsFractionRing B K] in
/-- Every positive-inertia conjugate center lies in the deleted boundary. -/
theorem ramifiedConjugateCentersInBoundary
    [IsNoetherianRing B]
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      AlgebraicGeometry.FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L))) :
    D.RamifiedConjugateCentersInBoundary := by
  intro E
  unfold RamifiedConjugateCentersInBoundaryAt
  intro q hq
  exact D.ramifiedCenter_mem_boundary R hFormal E q hq

end Diagram

end Diagram

end NormalizationInertia

end

end HodgeConjecture
