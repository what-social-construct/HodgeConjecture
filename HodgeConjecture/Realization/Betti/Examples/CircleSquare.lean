module

public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The actual circle square map on native singular H¹

Angular simplices are original continuous singular simplices. The boundary
of an angular triangle proves additivity of every closed one-cochain along
angular intervals. Actual exponential periodicity then identifies full-loop
values at all base angles. Evaluation on the already constructed positive
circle cycle proves that the original continuous square map acts by two.
No Chow map, proposed cohomology coordinate action, or Hurewicz premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CircleSquare

open Classical CategoryTheory HomologicalComplex Opposite Simplicial Convexity
open CircleOrientedCycle

/-- The original continuous degree-two map of the native complex unit circle. -/
def square : C(Circle, Circle) := ⟨fun z ↦ z ^ 2, by fun_prop⟩

def squareMap : space ⟶ space := TopCat.ofHom square

def angularCoordinate (n : ℕ) (v : Fin (n + 1) → ℝ)
    (s : StdSimplex ℝ (Fin (n + 1))) : ℝ := s.iConvexComb v

theorem angularCoordinate_eq_sum (n : ℕ) (v : Fin (n + 1) → ℝ)
    (s : StdSimplex ℝ (Fin (n + 1))) :
    angularCoordinate n v s = ∑ i, s.weights i * v i := by
  rw [angularCoordinate, iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
  simp only [smul_eq_mul]

def angularContinuous (n : ℕ) (v : Fin (n + 1) → ℝ) :
    C(StdSimplex ℝ (Fin (n + 1)), Circle) where
  toFun s := Circle.exp (angularCoordinate n v s)
  continuous_toFun := Circle.exp.continuous.comp (by
    change Continuous (fun s : StdSimplex ℝ (Fin (n + 1)) ↦ angularCoordinate n v s)
    simp_rw [angularCoordinate_eq_sum]
    fun_prop)

/-- An actual native singular simplex obtained by exponentiating real
barycentric interpolation of the listed vertex angles. -/
def angularSimplex (n : ℕ) (v : Fin (n + 1) → ℝ) : singular.obj (op ⦋n⦌) :=
  (SingularCochains.simplexEquivContinuous space n).symm (angularContinuous n v)

theorem angularSimplex_face (n : ℕ) (v : Fin (n + 2) → ℝ) (i : Fin (n + 2)) :
    singular.δ i (angularSimplex (n + 1) v) =
      angularSimplex n (fun j ↦ v (i.succAbove j)) := by
  apply (SingularCochains.simplexEquivContinuous space n).injective
  apply ContinuousMap.ext
  intro s
  change Circle.exp (angularCoordinate (n + 1) v (StdSimplex.map i.succAbove s)) =
    Circle.exp (angularCoordinate n (fun j ↦ v (i.succAbove j)) s)
  rw [angularCoordinate, iConvexComb_map]
  rfl

def edge (a b : ℝ) : singular.obj (op ⦋1⦌) := angularSimplex 1 ![a, b]

def triangle (a b c : ℝ) : singular.obj (op ⦋2⦌) := angularSimplex 2 ![a, b, c]

theorem triangle_face_zero (a b c : ℝ) : singular.δ (0 : Fin 3) (triangle a b c) = edge b c := by
  rw [triangle, angularSimplex_face]
  congr 1

theorem triangle_face_one (a b c : ℝ) : singular.δ (1 : Fin 3) (triangle a b c) = edge a c := by
  rw [triangle, angularSimplex_face]
  congr 1; funext j; fin_cases j <;> rfl

theorem triangle_face_two (a b c : ℝ) : singular.δ (2 : Fin 3) (triangle a b c) = edge a b := by
  rw [triangle, angularSimplex_face]
  congr 1; funext j; fin_cases j <;> rfl

theorem edge_apply (a b : ℝ) (s : StdSimplex ℝ (Fin 2)) :
    SingularCochains.simplexEquivContinuous space 1 (edge a b) s =
      Circle.exp (a + (b - a) * s.weights 1) := by
  change Circle.exp (angularCoordinate 1 ![a, b] s) = _
  congr 1
  rw [angularCoordinate_eq_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have ht := s.total
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at ht
  have h0 : s.weights 0 = 1 - s.weights 1 := by linarith
  rw [h0]
  ring

theorem edge_periodic (a b : ℝ) : edge (a + 2 * Real.pi) (b + 2 * Real.pi) = edge a b := by
  apply (SingularCochains.simplexEquivContinuous space 1).injective
  apply ContinuousMap.ext
  intro s
  rw [edge_apply, edge_apply]
  convert Circle.exp_add_two_pi (a + (b - a) * s.weights 1) using 1; congr 1; ring

theorem square_edge (a b : ℝ) :
    (TopCat.toSSet.map squareMap).app (op ⦋1⦌) (edge a b) = edge (2 * a) (2 * b) := by
  apply (SingularCochains.simplexEquivContinuous space 1).injective
  apply ContinuousMap.ext
  intro s
  change (SingularCochains.simplexEquivContinuous space 1 (edge a b) s) ^ 2 = _
  rw [edge_apply, edge_apply, pow_two, ← Circle.exp_add]
  congr 1
  ring

theorem firstSimplex_eq_edge : firstSimplex = edge (-Real.pi / 2) (Real.pi / 2) := by
  apply (SingularCochains.simplexEquivContinuous space 1).injective
  apply ContinuousMap.ext
  intro s
  rw [edge_apply]
  change Circle.exp (firstAngle (StdSimplex.homeomorphI s)) = _
  rw [firstAngle, StdSimplex.homeomorphI_apply_coe]
  congr 1
  ring

theorem secondSimplex_eq_edge : secondSimplex = edge (Real.pi / 2) (3 * Real.pi / 2) := by
  apply (SingularCochains.simplexEquivContinuous space 1).injective
  apply ContinuousMap.ext
  intro s
  rw [edge_apply]
  change secondPath (StdSimplex.homeomorphI s) = _
  rw [secondPath_angle, StdSimplex.homeomorphI_apply_coe]
  congr 1
  ring

variable (φ : SubcomplexConnectingRepresentative.Cocycle singular 1)

/-- The literal native triangle boundary gives angular path additivity for
every original closed one-cochain. -/
theorem edge_add (a b c : ℝ) :
    φ.val (edge a c) = φ.val (edge a b) + φ.val (edge b c) := by
  have h := congrFun φ.property (triangle a b c)
  rw [CochainDualCoordinates.differential_apply] at h
  norm_num [Fin.sum_univ_succ, triangle_face_zero, triangle_face_one, triangle_face_two] at h
  linarith

/-- Full positive-loop evaluation is independent of its actual base angle. -/
theorem fullLoop_independent (a b : ℝ) :
    φ.val (edge a (a + 2 * Real.pi)) = φ.val (edge b (b + 2 * Real.pi)) := by
  have h₁ := edge_add φ a (a + 2 * Real.pi) (b + 2 * Real.pi)
  have h₂ := edge_add φ a b (b + 2 * Real.pi)
  rw [edge_periodic] at h₁
  linarith

theorem square_loop_value (a b : ℝ) :
    φ.val (edge (2 * a) (2 * b)) +
      φ.val (edge (2 * b) (2 * (a + 2 * Real.pi))) =
        2 * (φ.val (edge a b) + φ.val (edge b (a + 2 * Real.pi))) := by
  have h₁ := edge_add φ (2 * a) (2 * b) (2 * (a + 2 * Real.pi))
  have h₂ := edge_add φ (2 * a) (2 * a + 2 * Real.pi) (2 * (a + 2 * Real.pi))
  have h₃ := edge_add φ a b (a + 2 * Real.pi)
  have hend : 2 * (a + 2 * Real.pi) = (2 * a + 2 * Real.pi) + 2 * Real.pi := by ring
  rw [hend] at h₁ h₂
  rw [fullLoop_independent φ (2 * a) a,
    fullLoop_independent φ (2 * a + 2 * Real.pi) a] at h₂
  rw [hend]
  linarith

theorem evaluation_cycle (ψ : SubcomplexCochains.Cochain singular 1) :
    SingularCyclePairing.evaluation singular 1 cycle ψ =
      ψ firstSimplex + ψ secondSimplex := by
  rw [cycle, SingularCyclePairing.evaluation_coordinates, cycleCoordinates, map_add]
  simp [Finsupp.llift_apply, Finsupp.lift_apply]

theorem loopPairing_cocycleClass :
    CircleOrientedPairing.loopPairing
      (SubcomplexConnectingRepresentative.cocycleClass singular 1 φ) =
        φ.val firstSimplex + φ.val secondSimplex := by
  change SingularCyclePairing.pairing singular 0 cycle cycle_boundary
    (SubcomplexConnectingRepresentative.cocycleClass singular 1 φ) = _
  exact (SingularCyclePairing.pairing_cocycleClass singular 0 cycle cycle_boundary
    φ.val φ.property).trans (evaluation_cycle φ.val)

/-- The original continuous square map doubles the actual positive-loop pairing. -/
theorem loopPairing_square (z : SingularCochains.Cohomology space 1) :
    CircleOrientedPairing.loopPairing (SingularCochains.cohomologyPullback squareMap 1 z) =
      2 * CircleOrientedPairing.loopPairing z := by
  obtain ⟨φ, rfl⟩ := SubcomplexConnectingRepresentative.cocycleClass_surjective singular 1 z
  change CircleOrientedPairing.loopPairing
    (homologyMap (SubcomplexCochains.pullback (TopCat.toSSet.map squareMap)) 1
      (SubcomplexConnectingRepresentative.cocycleClass singular 1 φ)) = _
  rw [SubcomplexConnectingRepresentative.cocycleClass_pullback,
    loopPairing_cocycleClass, loopPairing_cocycleClass]
  change φ.val ((TopCat.toSSet.map squareMap).app (op ⦋1⦌) firstSimplex) +
    φ.val ((TopCat.toSSet.map squareMap).app (op ⦋1⦌) secondSimplex) =
      2 * (φ.val firstSimplex + φ.val secondSimplex)
  rw [firstSimplex_eq_edge, secondSimplex_eq_edge, square_edge, square_edge]
  have h := square_loop_value φ (-Real.pi / 2) (Real.pi / 2)
  have hend : -Real.pi / 2 + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  rw [hend] at h
  exact h

/-- Independently of cycle classes, actual continuous singular pullback by
the circle square map is multiplication by two. -/
theorem cohomologyPullback_square (z : SingularCochains.Cohomology space 1) :
    SingularCochains.cohomologyPullback squareMap 1 z = (2 : ℚ) • z := by
  apply CircleCohomology.h1Equiv.injective
  have h := loopPairing_square z
  rw [CircleOrientedPairing.loopPairing_eq_coordinate,
    CircleOrientedPairing.loopPairing_eq_coordinate] at h
  simpa only [map_smul, smul_eq_mul] using h

theorem cohomologyPullback_square_eq :
    (SingularCochains.cohomologyPullback squareMap 1).hom = (2 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact cohomologyPullback_square z

end HodgeConjecture.CircleSquare

end
