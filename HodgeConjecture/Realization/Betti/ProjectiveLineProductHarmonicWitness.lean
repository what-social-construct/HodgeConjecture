module

public import HodgeConjecture.LinearAlgebra.Harmonic.Cohomology
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductChowFiberRealization

@[expose] public section

/-!
# Harmonic coordinate witnesses for the actual product Betti classes

The independently proved fiber coordinates on actual rational singular H²
give a faithful map to a two-dimensional real harmonic space. This finite
zero-differential presentation uses the chosen coordinate metric. It is a
coordinate control, not a triangulation or a geometric Hodge-Laplacian
comparison for the variety. The original Chow map and fiber-cycle recipe
are retained unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductHarmonicWitness

open Harmonic ProjectiveLineProductBetti ProjectiveLineProductSpanning
open ProjectiveLineProductChowFiberRealization ProjectiveLineProductChow

/-- A three-term cochain window with a two-dimensional middle term. -/
def coordinateComplex : OrientedTwoComplex Empty Unit Empty where
  incidence01 v := nomatch v
  incidence12 _ f := nomatch f
  boundarySqZero v := nomatch v

def coordinateSheaf : CellularSheaf coordinateComplex where
  vertexDim v := nomatch v
  edgeDim _ := 2
  faceDim f := nomatch f
  restrict01 v := nomatch v
  restrict12 _ f := nomatch f
  restrict02 v := nomatch v
  restrictionComp v := nomatch v

theorem coordinate_delta0 : coordinateSheaf.delta0 = 0 := by
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  simp [ha]

theorem coordinate_delta1 : coordinateSheaf.delta1 = 0 := by
  apply LinearMap.ext
  intro a
  apply PiLp.ext
  rintro ⟨f, i⟩
  exact nomatch f

theorem coordinate_isHarmonic (b : coordinateSheaf.C1) :
    coordinateSheaf.IsHarmonicOneCochain b := by
  apply (coordinateSheaf.degreeOneLaplacian_apply_eq_zero_iff b).mpr
  simp [coordinate_delta0, coordinate_delta1]

def realPairCoordinates : (ℝ × ℝ) →ₗ[ℝ] coordinateSheaf.C1 :=
  (WithLp.linearEquiv 2 ℝ ((Σ _ : Unit, Fin 2) → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i => if i.2 = 0 then LinearMap.fst ℝ ℝ ℝ else LinearMap.snd ℝ ℝ ℝ)

/-- The original rational Betti coordinates, embedded faithfully into real cochains. -/
def witnessCoordinates : ProductH2 →ₗ[ℚ] coordinateSheaf.C1 :=
  ((realPairCoordinates.restrictScalars ℚ).comp
    (LinearMap.prodMap (Algebra.linearMap ℚ ℝ) (Algebra.linearMap ℚ ℝ))).comp
      coordinateEquiv.toLinearMap

/-- A proved harmonic realization of the existing product coordinates. -/
def witness : ProductH2 →ₗ[ℚ] coordinateSheaf.harmonicOneSubspace :=
  witnessCoordinates.codRestrict (coordinateSheaf.harmonicOneSubspace.restrictScalars ℚ)
    (fun z => coordinate_isHarmonic (witnessCoordinates z))

theorem witness_injective : Function.Injective witness := by
  intro x y h
  apply coordinateEquiv.injective
  apply Prod.ext
  · have h0 := congrArg
      (fun v : coordinateSheaf.harmonicOneSubspace => v.1 ⟨(), (0 : Fin 2)⟩) h
    change ((coordinateEquiv x).1 : ℝ) = ((coordinateEquiv y).1 : ℝ) at h0
    exact_mod_cast h0
  · have h1 := congrArg
      (fun v : coordinateSheaf.harmonicOneSubspace => v.1 ⟨(), (1 : Fin 2)⟩) h
    change ((coordinateEquiv x).2 : ℝ) = ((coordinateEquiv y).2 : ℝ) at h1
    exact_mod_cast h1

/-- The finite harmonic test detects equality under the original product Chow map. -/
theorem ordinaryChowCycleClass_eq_iff_exact_witness_sub
    (z : SchemeCycles.RationalChowGroup (dimensionFunction ℂ) 1) (α : ProductH2) :
    ordinaryChowCycleClass z = α ↔
      coordinateSheaf.IsExactOneCochain
        ((witness (ordinaryChowCycleClass z) : coordinateSheaf.C1) -
          (witness α : coordinateSheaf.C1)) := by
  constructor
  · intro h
    exact ⟨0, by simp [h]⟩
  · exact coordinateSheaf.eq_of_exact_harmonicWitness_sub witness witness_injective

/-- The already constructed fiber recipe passes the harmonic class certificate. -/
theorem fiberChowClass_harmonic_certificate (α : ProductH2) :
    coordinateSheaf.IsExactOneCochain
      ((witness (ordinaryChowCycleClass (ProjectiveLineProductFiberPairedWitness.fiberChowClass α)) :
          coordinateSheaf.C1) - (witness α : coordinateSheaf.C1)) :=
  (ordinaryChowCycleClass_eq_iff_exact_witness_sub _ α).mp
    (ordinaryChowCycleClass_fiberChowClass α)

end HodgeConjecture.ProjectiveLineProductHarmonicWitness

end
