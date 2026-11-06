module

public import HodgeConjecture.Realization.Chow.Examples.SplitRationalEquivalence
public import HodgeConjecture.Correspondence.Examples.SplitCycleGeometry

@[expose] public section

/-!
# Pushforward, pullback, and diagonal intersection on split zero-cycles

Pushforward uses actual scheme-theoretic images of integral subschemes.
Pullback copies the coefficient to each reduced point in the actual fiber;
the geometric fiber and multiplicity comparisons are recorded separately.
Exterior products use the point-pair presentation of the actual product.
Intersection is defined by pulling that exterior product back along the
diagonal, before computing its coefficient formula.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

namespace SplitZeroCycles

open SplitPointGeometry Classical
open scoped BigOperators

variable (K : Type u) [Field K] (R : Type v) [CommRing R]
variable {S I J : Type u} [Finite S] [Finite I] [Finite J]

/-- Proper pushforward sends an actual integral point subscheme to its
scheme-theoretic image. The induced map to that image is an isomorphism. -/
def pushforward (f : S → I) : Cycles K S R →ₗ[R] Cycles K I R :=
  Finsupp.lmapDomain R R (imageIntegralSubscheme K f)

omit [Finite I] in
@[simp]
theorem pushforward_pointCycle (f : S → I) (s : S) :
    pushforward K R f (pointCycle K S R s) = pointCycle K I R (f s) := by
  simp [pushforward, pointCycle]

/-- Every cycle is the finite sum of its actual fundamental point cycles. -/
theorem sum_pointCycles [Fintype I] (z : Cycles K I R) :
    (∑ i, coordinates K I R z i • pointCycle K I R i) = z := by
  classical
  apply (coordinates K I R).injective
  ext i
  simp [-coordinates_apply, Pi.single_apply]

/-- Pushforward sums the coefficients over a fiber. -/
theorem coordinates_pushforward [Fintype S] (f : S → I)
    (z : Cycles K S R) (i : I) :
    coordinates K I R (pushforward K R f z) i =
      ∑ s, if f s = i then coordinates K S R z s else 0 := by
  classical
  nth_rw 1 [← sum_pointCycles K R z]
  simp [-coordinates_apply, Pi.single_apply, eq_comm]

/-- Flat pullback on reduced split fibers, each of whose points has
multiplicity one. -/
def pullback (f : S → I) : Cycles K I R →ₗ[R] Cycles K S R where
  toFun z := (coordinates K S R).symm (fun s ↦ coordinates K I R z (f s))
  map_add' z w := by
    apply (coordinates K S R).injective
    ext s
    simp [-coordinates_apply]
  map_smul' r z := by
    apply (coordinates K S R).injective
    ext s
    simp [-coordinates_apply]

@[simp]
theorem coordinates_pullback (f : S → I) (z : Cycles K I R) (s : S) :
    coordinates K S R (pullback K R f z) s = coordinates K I R z (f s) := by
  simp [pullback, -coordinates_apply]

/-- Pulling back a point gives the sum of the reduced points in its fiber. -/
theorem pullback_pointCycle [Fintype S] (f : S → I) (i : I) :
    pullback K R f (pointCycle K I R i) =
      ∑ s, if f s = i then pointCycle K S R s else 0 := by
  classical
  apply (coordinates K S R).injective
  ext s
  simp only [coordinates_pullback, coordinates_pointCycle, map_sum, Finset.sum_apply]
  have ht (c : S) :
      coordinates K S R (if f c = i then pointCycle K S R c else 0) s =
        if c = s then (if f s = i then 1 else 0) else 0 := by
    by_cases hc : c = s
    · subst c
      split_ifs <;> simp_all [-coordinates_apply]
    · split_ifs <;> simp_all [-coordinates_apply, eq_comm]
  simp_rw [ht]
  simp [Pi.single_apply, eq_comm]

/-- The exterior product, on the actual point-pair cycle generators. -/
def externalProduct (z : Cycles K I R) (w : Cycles K J R) :
    Cycles K (I × J) R :=
  (coordinates K (I × J) R).symm
    (fun p ↦ coordinates K I R z p.1 * coordinates K J R w p.2)

@[simp]
theorem coordinates_externalProduct (z : Cycles K I R) (w : Cycles K J R)
    (i : I) (j : J) :
    coordinates K (I × J) R (externalProduct K R z w) (i, j) =
      coordinates K I R z i * coordinates K J R w j := by
  simp [externalProduct, -coordinates_apply]

@[simp]
theorem externalProduct_pointCycle (i : I) (j : J) :
    externalProduct K R (pointCycle K I R i) (pointCycle K J R j) =
      pointCycle K (I × J) R (i, j) := by
  classical
  apply (coordinates K (I × J) R).injective
  ext p
  rcases p with ⟨a, b⟩
  by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [externalProduct, -coordinates_apply, Pi.single_apply, ha, hb]

/-- Intersection is exterior product followed by flat pullback along the
actual split diagonal, which is étale of relative dimension zero. -/
def intersection (z w : Cycles K I R) : Cycles K I R :=
  pullback K R (fun i : I ↦ (i, i)) (externalProduct K R z w)

@[simp]
theorem coordinates_intersection (z w : Cycles K I R) (i : I) :
    coordinates K I R (intersection K R z w) i =
      coordinates K I R z i * coordinates K I R w i := by
  simp [intersection, -coordinates_apply]

/-- Pushforward on the quotient by rational equivalence. -/
def chowPushforward (f : S → I) : Chow K S R →ₗ[R] Chow K I R :=
  (classMap K I R).comp
    ((pushforward K R f).comp (chowEquivCycles K S R).toLinearMap)

/-- Flat pullback on the quotient by rational equivalence. -/
def chowPullback (f : S → I) : Chow K I R →ₗ[R] Chow K S R :=
  (classMap K S R).comp
    ((pullback K R f).comp (chowEquivCycles K I R).toLinearMap)

/-- Exterior product descended through the zero rational-equivalence relations. -/
def chowExternalProduct (z : Chow K I R) (w : Chow K J R) : Chow K (I × J) R :=
  classMap K (I × J) R
    (externalProduct K R (chowEquivCycles K I R z) (chowEquivCycles K J R w))

/-- Chow intersection is still defined by diagonal pullback of exterior product. -/
def chowIntersection (z w : Chow K I R) : Chow K I R :=
  chowPullback K R (fun i : I ↦ (i, i)) (chowExternalProduct K R z w)

@[simp]
theorem chowPushforward_classMap (f : S → I) (z : Cycles K S R) :
    chowPushforward K R f (classMap K S R z) =
      classMap K I R (pushforward K R f z) := rfl

@[simp]
theorem chowPullback_classMap (f : S → I) (z : Cycles K I R) :
    chowPullback K R f (classMap K I R z) =
      classMap K S R (pullback K R f z) := rfl

theorem chowCoordinates_pushforward [Fintype S] (f : S → I)
    (z : Chow K S R) (i : I) :
    chowCoordinates K I R (chowPushforward K R f z) i =
      ∑ s, if f s = i then chowCoordinates K S R z s else 0 := by
  exact coordinates_pushforward K R f (chowEquivCycles K S R z) i

@[simp]
theorem chowCoordinates_pullback (f : S → I) (z : Chow K I R) (s : S) :
    chowCoordinates K S R (chowPullback K R f z) s =
      chowCoordinates K I R z (f s) := by
  exact coordinates_pullback K R f (chowEquivCycles K I R z) s

@[simp]
theorem chowCoordinates_externalProduct (z : Chow K I R) (w : Chow K J R)
    (i : I) (j : J) :
    chowCoordinates K (I × J) R (chowExternalProduct K R z w) (i, j) =
      chowCoordinates K I R z i * chowCoordinates K J R w j := by
  exact coordinates_externalProduct K R
    (chowEquivCycles K I R z) (chowEquivCycles K J R w) i j

@[simp]
theorem chowCoordinates_intersection (z w : Chow K I R) (i : I) :
    chowCoordinates K I R (chowIntersection K R z w) i =
      chowCoordinates K I R z i * chowCoordinates K I R w i := by
  simp [chowIntersection]

end SplitZeroCycles

end

end HodgeConjecture
