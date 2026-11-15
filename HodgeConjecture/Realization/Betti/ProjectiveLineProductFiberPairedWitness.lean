module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberChowBettiData
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanning

/-!
# A paired algebraic-cycle and supported-Betti witness in product H²

Every rational degree-two Betti class has coordinates in the two proved
fiber classes. The same coordinates determine an actual rational homogeneous
cycle and its ordinary Chow class, and a linear combination of the two
supported Thom images whose absolute Betti class is the requested class.
This is paired geometric data. It does not identify the Chow class with the
Betti class under a general cycle-class map; that compatibility remains to
be proved independently.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductFiberPairedWitness

open HodgeConjecture.SchemeCycles
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLineProductSpanning
open HodgeConjecture.ProjectiveLineProductFiberSupportedClass
open HodgeConjecture.ProjectiveLineProductFiberChowBettiData

/-- The geometric first-fiber Gysin class: the actual pulled-back supported
Thom class after forgetting support. -/
def firstFiberGysinClass : ProductH2 :=
  RelativeCochains.forget firstComplement 2 firstSupportedClass

/-- The geometric second-fiber Gysin class, with the same construction. -/
def secondFiberGysinClass : ProductH2 :=
  RelativeCochains.forget secondComplement 2 secondSupportedClass

theorem firstFiberGysinClass_eq_firstClass : firstFiberGysinClass = firstClass :=
  forget_firstSupportedClass

theorem secondFiberGysinClass_eq_secondClass : secondFiberGysinClass = secondClass :=
  forget_secondSupportedClass

/-- The finite rational algebraic cycle with the two Betti coordinates as
its coefficients. Both carriers are actual codimension-one fibers. -/
def fiberCycle (z : ProductH2) : cyclesOfDegree ℚ δ 1 :=
  (coordinateEquiv z).1 •
      cyclesOfDegreeRationalize δ 1 (ProjectiveLineProductChow.firstZeroCycle ℂ) +
    (coordinateEquiv z).2 •
      cyclesOfDegreeRationalize δ 1 (ProjectiveLineProductChow.secondZeroCycle ℂ)

/-- The ordinary rational Chow class of that actual cycle. -/
def fiberChowClass (z : ProductH2) : RationalChow :=
  rationalClassMap δ 1 (fiberCycle z)

theorem fiberChowClass_eq (z : ProductH2) :
    fiberChowClass z =
      (coordinateEquiv z).1 • ProjectiveLineProductChow.firstZeroRationalChowClass ℂ +
        (coordinateEquiv z).2 • ProjectiveLineProductChow.secondZeroRationalChowClass ℂ := by
  unfold fiberChowClass fiberCycle
  rw [map_add, map_smul, map_smul]
  rw [← chowRationalize_classMap δ 1 (ProjectiveLineProductChow.firstZeroCycle ℂ),
    ← chowRationalize_classMap δ 1 (ProjectiveLineProductChow.secondZeroCycle ℂ)]
  rfl

/-- The matching linear combination of the two proven supported Thom
images, after the original maps that forget support. -/
def supportedBettiCombination (z : ProductH2) : ProductH2 :=
  (coordinateEquiv z).1 • firstFiberGysinClass +
    (coordinateEquiv z).2 • secondFiberGysinClass

/-- Every product H² class is the indicated combination of the actual
supported fiber Gysin images. -/
theorem supportedBettiCombination_eq (z : ProductH2) :
    supportedBettiCombination z = z := by
  rw [supportedBettiCombination, firstFiberGysinClass_eq_firstClass,
    secondFiberGysinClass_eq_secondClass]
  change coordinateSection (coordinateEquiv z) = z
  obtain ⟨ab, hab⟩ := coordinateSection_surjective z
  rw [← hab]
  have hcoord : coordinateEquiv (coordinateSection ab) = ab := by
    change coordinateProbe (coordinateSection ab) = ab
    exact coordinateProbe_section ab
  rw [hcoord]

/-- A single paired witness records an actual rational codimension-one
cycle, its ordinary Chow class, and its normalized supported Betti image. -/
theorem exists_paired_witness (z : ProductH2) :
    ∃ c : cyclesOfDegree ℚ δ 1,
      rationalClassMap δ 1 c =
          (coordinateEquiv z).1 • ProjectiveLineProductChow.firstZeroRationalChowClass ℂ +
            (coordinateEquiv z).2 • ProjectiveLineProductChow.secondZeroRationalChowClass ℂ ∧
        z = supportedBettiCombination z := by
  exact ⟨fiberCycle z, fiberChowClass_eq z, (supportedBettiCombination_eq z).symm⟩

end HodgeConjecture.ProjectiveLineProductFiberPairedWitness

end
