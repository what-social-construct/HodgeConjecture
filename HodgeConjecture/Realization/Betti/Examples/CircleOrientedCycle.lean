module

public import HodgeConjecture.Realization.Betti.Examples.CircleTopology
public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import HodgeConjecture.Realization.Betti.SingularSubcomplexes
public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates

@[expose] public section

/-!
# The positively oriented actual circle cycle

Two actual singular one-simplices follow increasing angular coordinates
from −π/2 to π/2 and then from π/2 to 3π/2. They lie in the original
punctured-circle charts. Their endpoint boundaries cancel in both the
original singular complex and its actual small subcomplex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CircleOrientedCycle

open CategoryTheory Opposite Simplicial CircleTopology

abbrev space : TopCat := TopCat.of Circle
abbrev singular : SSet := TopCat.toSSet.obj space
abbrev small := SingularSubcomplexes.smallSingular space firstOpen secondOpen

/-- The increasing real angular coordinate on the right semicircle. -/
def firstAngle (t : unitInterval) : ℝ := -Real.pi / 2 + Real.pi * t.val

theorem firstAngle_mem_arc (t : unitInterval) : firstAngle t ∈ Arc := by
  have h0 := t.property.1
  have h1 := t.property.2
  have hp := Real.pi_pos
  dsimp [firstAngle]
  constructor <;> nlinarith

theorem exp_add_pi (x : ℝ) : Circle.exp (x + Real.pi) = -Circle.exp x := by
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

theorem neg_exp_negative_half : -Circle.exp (-Real.pi / 2) = Circle.exp (Real.pi / 2) := by
  rw [← exp_add_pi]
  congr 1
  ring

theorem neg_exp_positive_half : -Circle.exp (Real.pi / 2) = Circle.exp (-Real.pi / 2) := by
  rw [← neg_exp_negative_half, neg_neg]

/-- The first actual path goes counterclockwise through 1. -/
def firstPath : Path (overlapPoint false : Circle) (overlapPoint true : Circle) where
  toFun t := Circle.exp (firstAngle t)
  continuous_toFun := Circle.exp.continuous.comp (by unfold firstAngle; fun_prop)
  source' := by simp [firstAngle, overlapPoint_false_coe]
  target' := by
    rw [overlapPoint_true_coe]
    change Circle.exp (-Real.pi / 2 + Real.pi * 1) = _
    congr 1
    ring

/-- The second actual path continues counterclockwise through −1. -/
def secondPath : Path (overlapPoint true : Circle) (overlapPoint false : Circle) where
  toFun t := -Circle.exp (firstAngle t)
  continuous_toFun := (Circle.exp.continuous.comp (by unfold firstAngle; fun_prop)).neg
  source' := by simpa [firstAngle] using neg_exp_negative_half
  target' := by
    rw [overlapPoint_false_coe]
    change -Circle.exp (-Real.pi / 2 + Real.pi * 1) = _
    have h : -Real.pi / 2 + Real.pi * 1 = Real.pi / 2 := by ring
    rw [h]
    exact neg_exp_positive_half

theorem firstPath_mem_first (t : unitInterval) : firstPath t ∈ firstOpen :=
  exp_ne_neg_one ⟨firstAngle t, firstAngle_mem_arc t⟩

theorem secondPath_mem_second (t : unitInterval) : secondPath t ∈ secondOpen := by
  intro h
  apply firstPath_mem_first t
  have he := congrArg Neg.neg h
  simpa [firstPath, secondPath] using he

/-- The second path has the literal increasing angular coordinate π/2+πt. -/
theorem secondPath_angle (t : unitInterval) :
    secondPath t = Circle.exp (Real.pi / 2 + Real.pi * t.val) := by
  change -Circle.exp (firstAngle t) = _
  rw [← exp_add_pi]
  congr 1
  dsimp [firstAngle]
  ring

/-- The right semicircle as an original continuous singular one-simplex. -/
def firstContinuousSimplex := SingularDegreeZero.pathSimplex firstPath

/-- The left semicircle as an original continuous singular one-simplex. -/
def secondContinuousSimplex := SingularDegreeZero.pathSimplex secondPath

/-- The first original singular simplex, including Mathlib's native universe lift. -/
def firstSimplex : singular.obj (op ⦋1⦌) :=
  SingularDegreeZero.simplexEquivSingularSet Circle 1 firstContinuousSimplex

/-- The second original singular simplex. -/
def secondSimplex : singular.obj (op ⦋1⦌) :=
  SingularDegreeZero.simplexEquivSingularSet Circle 1 secondContinuousSimplex

/-- Original singular point simplices at the two actual overlap samples. -/
def endpoint (i : Bool) : singular.obj (op ⦋0⦌) :=
  SingularDegreeZero.simplexEquivSingularSet Circle 0
    (SingularDegreeZero.pointSimplex Circle (overlapPoint i : Circle))

@[simp]
theorem firstSimplex_face_zero : singular.δ (0 : Fin 2) firstSimplex = endpoint true := by
  change (TopCat.toSSet.obj (TopCat.of Circle)).map (SimplexCategory.δ (0 : Fin 2)).op
    (SingularDegreeZero.simplexEquivSingularSet Circle 1
      (SingularDegreeZero.pathSimplex firstPath)) = _
  rw [← SingularDegreeZero.simplexEquivSingularSet_face]
  rw [SingularDegreeZero.face_pathSimplex_zero]
  rfl

@[simp]
theorem firstSimplex_face_one : singular.δ (1 : Fin 2) firstSimplex = endpoint false := by
  change (TopCat.toSSet.obj (TopCat.of Circle)).map (SimplexCategory.δ (1 : Fin 2)).op
    (SingularDegreeZero.simplexEquivSingularSet Circle 1
      (SingularDegreeZero.pathSimplex firstPath)) = _
  rw [← SingularDegreeZero.simplexEquivSingularSet_face]
  rw [SingularDegreeZero.face_pathSimplex_one]
  rfl

@[simp]
theorem secondSimplex_face_zero : singular.δ (0 : Fin 2) secondSimplex = endpoint false := by
  change (TopCat.toSSet.obj (TopCat.of Circle)).map (SimplexCategory.δ (0 : Fin 2)).op
    (SingularDegreeZero.simplexEquivSingularSet Circle 1
      (SingularDegreeZero.pathSimplex secondPath)) = _
  rw [← SingularDegreeZero.simplexEquivSingularSet_face]
  rw [SingularDegreeZero.face_pathSimplex_zero]
  rfl

@[simp]
theorem secondSimplex_face_one : singular.δ (1 : Fin 2) secondSimplex = endpoint true := by
  change (TopCat.toSSet.obj (TopCat.of Circle)).map (SimplexCategory.δ (1 : Fin 2)).op
    (SingularDegreeZero.simplexEquivSingularSet Circle 1
      (SingularDegreeZero.pathSimplex secondPath)) = _
  rw [← SingularDegreeZero.simplexEquivSingularSet_face]
  rw [SingularDegreeZero.face_pathSimplex_one]
  rfl

theorem firstSimplex_mem_first : firstSimplex ∈
    (SingularSubcomplexes.subsetSingular space firstOpen).obj (op ⦋1⦌) := by
  intro t
  exact firstPath_mem_first (Convexity.StdSimplex.homeomorphI t.down)

theorem secondSimplex_mem_second : secondSimplex ∈
    (SingularSubcomplexes.subsetSingular space secondOpen).obj (op ⦋1⦌) := by
  intro t
  exact secondPath_mem_second (Convexity.StdSimplex.homeomorphI t.down)

/-- The actual finite-support chain traversing the two positive semicircles. -/
def cycleCoordinates : singular.obj (op ⦋1⦌) →₀ ℚ :=
  Finsupp.single firstSimplex 1 + Finsupp.single secondSimplex 1

/-- The literal alternating boundary cancels at the two original endpoint simplices. -/
theorem cycleCoordinates_boundary : SingularChainCoordinates.boundary singular 0 cycleCoordinates = 0 := by
  simp [cycleCoordinates, SingularChainCoordinates.boundary_single, Fin.sum_univ_two,
    add_left_comm]

/-- The chain in Mathlib's original singular-chain object. -/
def cycle : (SingularChainCoordinates.complex singular).X 1 :=
  SingularChainCoordinates.coordinates singular 1 cycleCoordinates

theorem cycle_boundary : (SingularChainCoordinates.complex singular).d 1 0 cycle = 0 := by
  rw [cycle, SingularChainCoordinates.coordinates_boundary, cycleCoordinates_boundary, map_zero]

/-- The first actual arc as a simplex in its contained-singular chart. -/
def firstContainedSimplex :
    (SingularSubcomplexes.subsetSingular space firstOpen).toSSet.obj (op ⦋1⦌) :=
  ⟨firstSimplex, firstSimplex_mem_first⟩

/-- The second actual arc as a simplex in its contained-singular chart. -/
def secondContainedSimplex :
    (SingularSubcomplexes.subsetSingular space secondOpen).toSSet.obj (op ⦋1⦌) :=
  ⟨secondSimplex, secondSimplex_mem_second⟩

/-- Each original endpoint simplex lies in the actual chart intersection. -/
def intersectionEndpoint (i : Bool) :
    (SingularSubcomplexes.subsetSingular space firstOpen ⊓
      SingularSubcomplexes.subsetSingular space secondOpen).toSSet.obj (op ⦋0⦌) :=
  ⟨endpoint i, ⟨fun _ ↦ (overlapPoint i).property.1,
    fun _ ↦ (overlapPoint i).property.2⟩⟩

/-- The same original endpoints in the small union of the two charts. -/
def smallEndpoint (i : Bool) : small.toSSet.obj (op ⦋0⦌) :=
  ⟨endpoint i, Or.inl (intersectionEndpoint i).property.1⟩

/-- The first small simplex, with its original first-chart containment proof. -/
def firstSmallSimplex : small.toSSet.obj (op ⦋1⦌) :=
  ⟨firstSimplex, Or.inl firstSimplex_mem_first⟩

/-- The second small simplex, with its original second-chart containment proof. -/
def secondSmallSimplex : small.toSSet.obj (op ⦋1⦌) :=
  ⟨secondSimplex, Or.inr secondSimplex_mem_second⟩

@[simp]
theorem firstSmallSimplex_face_zero :
    small.toSSet.δ (0 : Fin 2) firstSmallSimplex = smallEndpoint true :=
  Subtype.ext firstSimplex_face_zero

@[simp]
theorem firstSmallSimplex_face_one :
    small.toSSet.δ (1 : Fin 2) firstSmallSimplex = smallEndpoint false :=
  Subtype.ext firstSimplex_face_one

@[simp]
theorem secondSmallSimplex_face_zero :
    small.toSSet.δ (0 : Fin 2) secondSmallSimplex = smallEndpoint false :=
  Subtype.ext secondSimplex_face_zero

@[simp]
theorem secondSmallSimplex_face_one :
    small.toSSet.δ (1 : Fin 2) secondSmallSimplex = smallEndpoint true :=
  Subtype.ext secondSimplex_face_one

/-- The same actual two-arc finite chain in the genuine small singular subcomplex. -/
def smallCycleCoordinates : small.toSSet.obj (op ⦋1⦌) →₀ ℚ :=
  Finsupp.single firstSmallSimplex 1 + Finsupp.single secondSmallSimplex 1

/-- The actual native small-chain object represented by the two original arc simplices. -/
def smallCycle : (SingularChainCoordinates.complex small.toSSet).X 1 :=
  SingularChainCoordinates.coordinates small.toSSet 1 smallCycleCoordinates

/-- The small cycle includes as exactly the original full positive circle cycle. -/
theorem inclusion_smallCycle : (SubcomplexChainCoordinates.inclusion small).f 1 smallCycle = cycle := by
  rw [smallCycle, SubcomplexChainCoordinates.inclusion_coordinates]
  change SingularChainCoordinates.coordinates singular 1 _ =
    SingularChainCoordinates.coordinates singular 1 cycleCoordinates
  apply congrArg (SingularChainCoordinates.coordinates singular 1)
  rw [smallCycleCoordinates, map_add]
  simp only [SubcomplexChainCoordinates.inclusionCoordinates, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rfl

theorem smallCycle_boundary :
    (SingularChainCoordinates.complex small.toSSet).d 1 0 smallCycle = 0 := by
  apply SubcomplexChainCoordinates.inclusion_injective small 0
  rw [map_zero]
  have h := congrArg (fun f ↦ f smallCycle) ((SubcomplexChainCoordinates.inclusion small).comm 1 0)
  change (SingularChainCoordinates.complex singular).d 1 0
    ((SubcomplexChainCoordinates.inclusion small).f 1 smallCycle) =
      (SubcomplexChainCoordinates.inclusion small).f 0
        ((SingularChainCoordinates.complex small.toSSet).d 1 0 smallCycle) at h
  rw [← h, inclusion_smallCycle, cycle_boundary]

theorem smallCycleCoordinates_boundary :
    SingularChainCoordinates.boundary small.toSSet 0 smallCycleCoordinates = 0 := by
  apply (SingularChainCoordinates.coordinates small.toSSet 0).injective
  rw [map_zero, ← SingularChainCoordinates.coordinates_boundary]
  exact smallCycle_boundary

/-- The native full chain is literally the sum of its two original simplex injections. -/
theorem cycle_eq_injections : cycle =
    (singular.ιChainComplex firstSimplex (R := ModuleCat.of ℚ ℚ)) 1 +
      (singular.ιChainComplex secondSimplex (R := ModuleCat.of ℚ ℚ)) 1 := by
  simp [cycle, cycleCoordinates]

/-- The native small chain retains those same two actual simplex injections. -/
theorem smallCycle_eq_injections : smallCycle =
    (small.toSSet.ιChainComplex firstSmallSimplex (R := ModuleCat.of ℚ ℚ)) 1 +
      (small.toSSet.ιChainComplex secondSmallSimplex (R := ModuleCat.of ℚ ℚ)) 1 := by
  rw [smallCycle, smallCycleCoordinates, map_add,
    SingularChainCoordinates.coordinates_single small.toSSet 1 firstSmallSimplex 1,
    SingularChainCoordinates.coordinates_single small.toSSet 1 secondSmallSimplex 1]

end HodgeConjecture.CircleOrientedCycle
