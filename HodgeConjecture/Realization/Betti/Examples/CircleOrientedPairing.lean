module

public import HodgeConjecture.Realization.Betti.Examples.CircleCohomology
public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedCycle
public import HodgeConjecture.Realization.Betti.SingularCyclePairing
public import HodgeConjecture.Realization.Betti.SubcomplexConnectingRepresentative
public import HodgeConjecture.Realization.Betti.SubcomplexDegreeZeroRepresentative

@[expose] public section

/-!
# The actual circle boundary and positive loop pairing

The genuine native connecting map is evaluated on the actual two-arc
counterclockwise singular cycle. Its lift-and-differentiate representative
has pairing equal to the upper overlap value minus the lower value.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CircleOrientedPairing

open CategoryTheory HomologicalComplex Opposite Simplicial CircleTopology CircleOrientedCycle

abbrev first := SingularSubcomplexes.subsetSingular space firstOpen
abbrev second := SingularSubcomplexes.subsetSingular space secondOpen
abbrev intersection : SSet := (first ⊓ second).toSSet

/-- The actual Kronecker functional of the original counterclockwise circle cycle. -/
def loopPairing : SingularCochains.Cohomology space 1 →ₗ[ℚ] ℚ :=
  (SingularCyclePairing.pairing singular 0 cycle cycle_boundary).hom

/-- The same original cycle evaluated in the actual small cochain complex. -/
def smallLoopPairing : (SubcomplexCochains.complex small.toSSet).homology 1 →ₗ[ℚ] ℚ :=
  (SingularCyclePairing.pairing small.toSSet 0 smallCycle smallCycle_boundary).hom

def firstEndpoint (i : Bool) : first.toSSet.obj (op ⦋0⦌) :=
  ⟨(intersectionEndpoint i).val, (intersectionEndpoint i).property.1⟩

def secondEndpoint (i : Bool) : second.toSSet.obj (op ⦋0⦌) :=
  ⟨(intersectionEndpoint i).val, (intersectionEndpoint i).property.2⟩

@[simp]
theorem firstContained_face_zero : first.toSSet.δ (0 : Fin 2) firstContainedSimplex =
    firstEndpoint true := Subtype.ext firstSimplex_face_zero

@[simp]
theorem firstContained_face_one : first.toSSet.δ (1 : Fin 2) firstContainedSimplex =
    firstEndpoint false := Subtype.ext firstSimplex_face_one

@[simp]
theorem secondContained_face_zero : second.toSSet.δ (0 : Fin 2) secondContainedSimplex =
    secondEndpoint false := Subtype.ext secondSimplex_face_zero

@[simp]
theorem secondContained_face_one : second.toSSet.δ (1 : Fin 2) secondContainedSimplex =
    secondEndpoint true := Subtype.ext secondSimplex_face_one

theorem evaluation_smallCycle (φ : SubcomplexCochains.Cochain small.toSSet 1) :
    SingularCyclePairing.evaluation small.toSSet 1 smallCycle φ =
      φ firstSmallSimplex + φ secondSmallSimplex := by
  rw [smallCycle, SingularCyclePairing.evaluation_coordinates, smallCycleCoordinates, map_add]
  simp [Finsupp.llift_apply, Finsupp.lift_apply]

/-- The native positive connecting sign is fixed by literal endpoint evaluation. -/
theorem smallLoopPairing_connecting
    (u : SubcomplexConnectingRepresentative.Cocycle intersection 0) :
    smallLoopPairing
      (SubcomplexCochains.connecting first second 0
        (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u)) =
      u.val (intersectionEndpoint true) - u.val (intersectionEndpoint false) := by
  obtain ⟨v, w, hv, hw, hclass⟩ :=
    SubcomplexConnectingRepresentative.exists_connecting_representative first second 0 u
  rw [hclass]
  change SingularCyclePairing.pairing small.toSSet 0 smallCycle smallCycle_boundary
    (SubcomplexConnectingRepresentative.cocycleClass small.toSSet 1 w) = _
  have hp : SingularCyclePairing.pairing small.toSSet 0 smallCycle smallCycle_boundary
      (SubcomplexConnectingRepresentative.cocycleClass small.toSSet 1 w) =
        SingularCyclePairing.evaluation small.toSSet 1 smallCycle w.val :=
    SingularCyclePairing.pairing_cocycleClass small.toSSet 0 smallCycle smallCycle_boundary
      w.val w.property
  rw [hp, evaluation_smallCycle]
  have ha := congrArg (fun p ↦ p.1 firstContainedSimplex) hw
  have hb := congrArg (fun p ↦ p.2 secondContainedSimplex) hw
  change w.val firstSmallSimplex = SubcomplexCochains.differential first.toSSet 0 v.1
    firstContainedSimplex at ha
  change w.val secondSmallSimplex = SubcomplexCochains.differential second.toSSet 0 v.2
    secondContainedSimplex at hb
  rw [ha, hb, CochainDualCoordinates.differential_apply,
    CochainDualCoordinates.differential_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, firstContained_face_zero, firstContained_face_one,
    secondContained_face_zero, secondContained_face_one]
  have ht := congrFun hv (intersectionEndpoint true)
  have hf := congrFun hv (intersectionEndpoint false)
  change v.1 (firstEndpoint true) - v.2 (secondEndpoint true) =
    u.val (intersectionEndpoint true) at ht
  change v.1 (firstEndpoint false) - v.2 (secondEndpoint false) =
    u.val (intersectionEndpoint false) at hf
  rw [← ht, ← hf]
  ring

/-- The actual map taking an overlap simplex to its original contained-circle simplex. -/
def overlapToIntersection : TopCat.toSSet.obj (TopCat.of overlap) ⟶ intersection :=
  SingularSubcomplexes.subtypeToSubset space (firstOpen ∩ secondOpen) ≫
    (SSet.Subcomplex.eqToIso
      (SingularSubcomplexes.subsetSingular_inter space firstOpen secondOpen)).hom

/-- The original subtype comparison uses precisely this original simplex map. -/
theorem intersectionIso_hom :
    (SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom =
      homologyMap (SubcomplexCochains.pullback overlapToIntersection) 0 := by
  change homologyMap (SubcomplexCochains.pullback
    (SSet.Subcomplex.eqToIso
      (SingularSubcomplexes.subsetSingular_inter space firstOpen secondOpen)).hom) 0 ≫
      homologyMap (SubcomplexCochains.pullback
        (SingularSubcomplexes.subtypeToSubset space (firstOpen ∩ secondOpen))) 0 = _
  rw [← homologyMap_comp, ← SubcomplexCochains.pullback_comp]
  rfl

/-- The overlap cohomology coordinate reads the same original endpoint zero-simplex. -/
theorem overlapCoordinate_cocycleClass
    (u : SubcomplexConnectingRepresentative.Cocycle intersection 0) (i : Bool) :
    CircleCohomology.overlapZeroEquiv
      ((SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom
        (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u)) i =
      u.val (intersectionEndpoint i) := by
  rw [intersectionIso_hom]
  change SingularDegreeZero.eval overlap
    ((SingularCochains.cohomologyZeroIso overlap).hom
      (homologyMap (SubcomplexCochains.pullback overlapToIntersection) 0
        (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u))) (overlapPoint i) = _
  rw [SubcomplexConnectingRepresentative.cocycleClass_pullback,
    SubcomplexDegreeZeroRepresentative.eval_cocycleClass]
  change u.val (overlapToIntersection.app (op ⦋0⦌)
    (SingularDegreeZero.simplexEquivSingularSet overlap 0
      (SingularDegreeZero.pointSimplex overlap (overlapPoint i)))) = _
  congr 1

/-- Actual restriction to small cochains preserves evaluation on this same original cycle. -/
theorem smallLoopPairing_restriction (z : SingularCochains.Cohomology space 1) :
    smallLoopPairing
      ((CochainDualComparison.smallCohomologyIso space firstOpen secondOpen
        firstOpen_isOpen secondOpen_isOpen opens_cover 1).hom z) = loopPairing z := by
  have h := SingularCyclePairing.pairing_pullback small.ι 0 smallCycle smallCycle_boundary
    (SingularCyclePairing.chainMap_closed small.ι 0 smallCycle smallCycle_boundary)
  change homologyMap (CochainDualComparison.smallRestriction space firstOpen secondOpen) 1 ≫
    SingularCyclePairing.pairing small.toSSet 0 smallCycle smallCycle_boundary =
      SingularCyclePairing.pairing singular 0
        ((SubcomplexChainCoordinates.inclusion small).f 1 smallCycle) _ at h
  have he : SingularCyclePairing.pairing singular 0
      ((SubcomplexChainCoordinates.inclusion small).f 1 smallCycle)
      (SingularCyclePairing.chainMap_closed small.ι 0 smallCycle smallCycle_boundary) =
        SingularCyclePairing.pairing singular 0 cycle cycle_boundary := by
    congr 1
    exact inclusion_smallCycle
  rw [he] at h
  exact congrArg (fun f ↦ f z) h

/-- The original full connecting class restricts to the original small connecting class. -/
theorem restriction_connecting (z : (SubcomplexCochains.complex intersection).homology 0) :
    (CochainDualComparison.smallCohomologyIso space firstOpen secondOpen
      firstOpen_isOpen secondOpen_isOpen opens_cover 1).hom
      (CircleCohomology.connecting
        ((SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom z)) =
      SubcomplexCochains.connecting first second 0 z := by
  change ((SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom ≫
    CircleCohomology.connecting ≫
      (CochainDualComparison.smallCohomologyIso space firstOpen secondOpen
        firstOpen_isOpen secondOpen_isOpen opens_cover 1).hom) z = _
  simp only [CircleCohomology.connecting, SingularMayerVietoris.connecting,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rfl

/-- The actual native connecting boundary pairs with the positive loop by upper minus lower. -/
theorem loopPairing_connecting (z : SingularCochains.Cohomology (TopCat.of overlap) 0) :
    loopPairing (CircleCohomology.connecting z) =
      TwoComponentBoundary.jump (CircleCohomology.overlapZeroEquiv z) := by
  obtain ⟨x, rfl⟩ :=
    (SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).toLinearEquiv.surjective z
  obtain ⟨u, rfl⟩ := SubcomplexConnectingRepresentative.cocycleClass_surjective intersection 0 x
  change loopPairing (CircleCohomology.connecting
    ((SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom
      (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u))) =
    TwoComponentBoundary.jump (CircleCohomology.overlapZeroEquiv
      ((SingularMayerVietoris.intersectionCohomologyIso space firstOpen secondOpen 0).hom
        (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u)))
  rw [← smallLoopPairing_restriction, restriction_connecting, smallLoopPairing_connecting]
  change _ = CircleCohomology.overlapZeroEquiv _ true -
    CircleCohomology.overlapZeroEquiv _ false
  rw [overlapCoordinate_cocycleClass, overlapCoordinate_cocycleClass]

/-- The previously computed rational coordinate is the actual positive-loop pairing. -/
theorem loopPairing_eq_coordinate (z : SingularCochains.Cohomology space 1) :
    loopPairing z = CircleCohomology.h1Equiv z := by
  obtain ⟨x, rfl⟩ := CircleCohomology.connecting_surjective z
  rw [loopPairing_connecting, CircleCohomology.h1Equiv_connecting]

/-- The cover generator has positive pairing one with the actual counterclockwise loop. -/
@[simp]
theorem loopPairing_coverGenerator : loopPairing CircleCohomology.coverGenerator = 1 := by
  rw [loopPairing_eq_coordinate, CircleCohomology.h1Equiv_coverGenerator]

end HodgeConjecture.CircleOrientedPairing
