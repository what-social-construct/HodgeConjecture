import HodgeConjecture.Realization.Betti.Examples.SplitComplexPoints
import HodgeConjecture.Realization.Betti.FiniteTransfer
import HodgeConjecture.Realization.Chow.Examples.SplitChowAction

/-!
# The cycle-class comparison for finite split complex schemes

The target is singular degree-zero cohomology of the actual complex-algebra
point space, with the regular-function evaluation topology. The class of a
reduced point is its characteristic singular zero-cocycle. Point classification
and the discrete-space cohomology calculation prove that this map is an
isomorphism, compatible with geometric pushforward, pullback, and intersection.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitBetti

noncomputable section

open Classical SplitComplexPoints
open scoped BigOperators

variable (I : Type) [Finite I]

/-- Genuine singular degree-zero cohomology of the complex point space. -/
abbrev Cohomology := SingularDegreeZero.H0 (Point I)

/-- Evaluate singular cocycles on the classified complex points. -/
def coordinates : Cohomology I ≃ₗ[ℚ] (I → ℚ) where
  toFun h i := SingularDegreeZero.eval (Point I) h (labelEquiv I i)
  invFun a := (SingularDegreeZero.equivFunctions (Point I)).symm
    (fun p ↦ a ((labelEquiv I).symm p))
  left_inv h := by
    apply (SingularDegreeZero.equivFunctions (Point I)).injective
    ext p
    simp
  right_inv a := by
    funext i
    simp
  map_add' h g := by
    funext i
    exact congrFun (map_add (SingularDegreeZero.eval (Point I)) h g) _
  map_smul' r h := by
    funext i
    exact congrFun (map_smul (SingularDegreeZero.eval (Point I)) r h) _

@[simp]
theorem coordinates_apply (h : Cohomology I) (i : I) :
    coordinates I h i = SingularDegreeZero.eval (Point I) h (evalPoint I i) := rfl

@[simp]
theorem coordinates_mul (h g : Cohomology I) :
    coordinates I (h * g) = coordinates I h * coordinates I g := by
  ext i
  exact congrFun (map_mul (SingularDegreeZero.eval (Point I)) h g) _

/-- The rational cycle-class map, with its proved bijectivity. -/
def cycleClass : SplitZeroCycles.Chow ℂ I ℚ ≃ₗ[ℚ] Cohomology I :=
  (SplitZeroCycles.chowCoordinates ℂ I ℚ).trans (coordinates I).symm

@[simp]
theorem coordinates_cycleClass (z : SplitZeroCycles.Chow ℂ I ℚ) :
    coordinates I (cycleClass I z) = SplitZeroCycles.chowCoordinates ℂ I ℚ z := by
  simp [cycleClass]

/-- A reduced rational point has its normalized characteristic Betti class. -/
theorem cycleClass_pointCycle (i j : I) :
    SingularDegreeZero.eval (Point I)
      (cycleClass I (SplitZeroCycles.classMap ℂ I ℚ
        (SplitZeroCycles.pointCycle ℂ I ℚ i))) (evalPoint I j) =
      if i = j then 1 else 0 := by
  rw [← coordinates_apply, coordinates_cycleClass]
  simp [-SplitZeroCycles.coordinates_apply, Pi.single_apply, eq_comm]

variable {I} {S J : Type} [Finite S] [Finite J]

/-- Pullback comes from the actual continuous map on complex points. -/
def pullback (f : S → I) : Cohomology I →ₐ[ℚ] Cohomology S :=
  SingularDegreeZero.pullback (mapContinuous f)

@[simp]
theorem coordinates_pullback (f : S → I) (h : Cohomology I) (s : S) :
    coordinates S (pullback f h) s = coordinates I h (f s) := by
  simp only [coordinates_apply, pullback, SingularDegreeZero.eval_pullback,
    mapContinuous_apply, map_evalPoint]

/-- Proper degree-zero transfer sums over the actual complex-point fibers. -/
def pushforward [Fintype S] (f : S → I) : Cohomology S →ₗ[ℚ] Cohomology I :=
  SingularDegreeZero.transfer (mapContinuous f)

theorem coordinates_pushforward [Fintype S] (f : S → I)
    (h : Cohomology S) (i : I) :
    coordinates I (pushforward f h) i =
      ∑ s, if f s = i then coordinates S h s else 0 := by
  change SingularDegreeZero.eval (Point I)
    (SingularDegreeZero.transfer (mapContinuous f) h) (labelEquiv I i) = _
  rw [SingularDegreeZero.eval_transfer]
  rw [← (labelEquiv S).sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mapContinuous_apply, map_labelEquiv, Equiv.apply_eq_iff_eq]
  rfl

/-- Cycle classes commute with flat pullback. -/
theorem cycleClass_pullback (f : S → I) (z : SplitZeroCycles.Chow ℂ I ℚ) :
    cycleClass S (SplitZeroCycles.chowPullback ℂ ℚ f z) = pullback f (cycleClass I z) := by
  apply (coordinates S).injective
  ext s
  simp only [coordinates_cycleClass, coordinates_pullback,
    SplitZeroCycles.chowCoordinates_pullback]

/-- Cycle classes commute with proper pushforward, including empty fibers. -/
theorem cycleClass_pushforward [Fintype S] (f : S → I)
    (z : SplitZeroCycles.Chow ℂ S ℚ) :
    cycleClass I (SplitZeroCycles.chowPushforward ℂ ℚ f z) =
      pushforward f (cycleClass S z) := by
  apply (coordinates I).injective
  ext i
  simp only [coordinates_cycleClass, coordinates_pushforward,
    SplitZeroCycles.chowCoordinates_pushforward]

/-- Geometric intersection realizes as the degree-zero singular cup product. -/
theorem cycleClass_intersection (z w : SplitZeroCycles.Chow ℂ I ℚ) :
    cycleClass I (SplitZeroCycles.chowIntersection ℂ ℚ z w) =
      cycleClass I z * cycleClass I w := by
  apply (coordinates I).injective
  ext i
  simp only [coordinates_cycleClass, coordinates_mul, Pi.mul_apply,
    SplitZeroCycles.chowCoordinates_intersection]

end

end HodgeConjecture.SplitBetti
