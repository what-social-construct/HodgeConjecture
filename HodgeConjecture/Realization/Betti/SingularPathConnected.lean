module

public import HodgeConjecture.Realization.Betti.SingularDegreeZero
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

@[expose] public section

/-!
# Singular degree-zero cohomology of a path-connected space

An actual path gives a continuous singular one-simplex by identifying the
standard one-simplex with the unit interval. Its two faces are the terminal
and initial point simplices, in the order used by `SingularDegreeZero.face`.
The singular cocycle equation therefore forces evaluations to agree along
paths. Evaluation at a specified point of a path-connected space identifies
its degree-zero rational singular cohomology with `ℚ`.
-/

set_option autoImplicit false

namespace HodgeConjecture.SingularDegreeZero

open CategoryTheory Simplicial

noncomputable section

universe u v

variable (X : Type u) [TopologicalSpace X]

/-- The actual constant singular zero-cocycle, available on any space. -/
def constantClass : ℚ →ₐ[ℚ] H0 X where
  toFun q := ⟨fun _ ↦ q, (mem_kernel_iff X _).2 (fun _ ↦ rfl)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem constantClass_apply (q : ℚ) (σ : Simplex X 0) :
    (constantClass X q).val σ = q := rfl

@[simp]
theorem eval_constantClass (q : ℚ) (x : X) :
    eval X (constantClass X q) x = q := rfl

/-- Evaluation at a specified point, as a rational algebra homomorphism. -/
def evalAt (x : X) : H0 X →ₐ[ℚ] ℚ where
  toFun h := eval X h x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem evalAt_apply (x : X) (h : H0 X) : evalAt X x h = eval X h x := rfl

variable {X}

/-- Turn an actual path into a singular one-simplex using the standard
one-simplex's homeomorphism with the unit interval. -/
def pathSimplex {x y : X} (p : Path x y) : Simplex X 1 :=
  p.toContinuousMap.comp
    ⟨Convexity.StdSimplex.homeomorphI, Convexity.StdSimplex.homeomorphI.continuous⟩

@[simp]
theorem face_pathSimplex_zero {x y : X} (p : Path x y) :
    face X (pathSimplex p) 0 = pointSimplex X y := by
  ext t
  simp only [face, pathSimplex, SimplexCategory.δ_zero_eq_const,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, pointSimplex_apply]
  change p (Convexity.StdSimplex.homeomorphI
    (Convexity.StdSimplex.map (fun _ : Fin 1 ↦ (1 : Fin 2)) t)) = y
  simp

@[simp]
theorem face_pathSimplex_one {x y : X} (p : Path x y) :
    face X (pathSimplex p) 1 = pointSimplex X x := by
  ext t
  simp only [face, pathSimplex, SimplexCategory.δ_one_eq_const,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, pointSimplex_apply]
  change p (Convexity.StdSimplex.homeomorphI
    (Convexity.StdSimplex.map (fun _ : Fin 1 ↦ (0 : Fin 2)) t)) = x
  simp

/-- The actual singular cocycle equation identifies the endpoint evaluations
of a path. -/
theorem eval_eq_of_path (h : H0 X) {x y : X} (p : Path x y) :
    eval X h x = eval X h y := by
  have hc := (mem_kernel_iff X h.val).1 h.property (pathSimplex p)
  simpa only [face_pathSimplex_zero, face_pathSimplex_one, eval_apply] using hc.symm

/-- Evaluation of a singular zero-class is constant on path components. -/
theorem eval_eq_of_joined (h : H0 X) {x y : X} (hxy : Joined x y) :
    eval X h x = eval X h y :=
  eval_eq_of_path h hxy.somePath

variable (X)

/-- Evaluation is constant throughout a path-connected space. -/
theorem eval_eq [PathConnectedSpace X] (h : H0 X) (x y : X) :
    eval X h x = eval X h y :=
  eval_eq_of_joined h (PathConnectedSpace.joined x y)

/-- Every degree-zero class on a path-connected space is its actual constant
cocycle, with value obtained by evaluating at a specified point. -/
theorem constantClass_eval [PathConnectedSpace X] (x : X) (h : H0 X) :
    constantClass X (eval X h x) = h := by
  apply eval_injective X
  funext y
  exact eval_eq X h x y

/-- Degree-zero rational singular cohomology of a path-connected space is
canonically the rational algebra, evaluated at a specified point. -/
def equivConstants [PathConnectedSpace X] (x : X) : H0 X ≃ₐ[ℚ] ℚ :=
  AlgEquiv.ofAlgHom (evalAt X x) (constantClass X)
    (AlgHom.ext (fun _ ↦ rfl)) (AlgHom.ext (constantClass_eval X x))

@[simp]
theorem equivConstants_apply [PathConnectedSpace X] (x : X) (h : H0 X) :
    equivConstants X x h = eval X h x := rfl

@[simp]
theorem equivConstants_symm_apply [PathConnectedSpace X] (x : X) (q : ℚ) :
    (equivConstants X x).symm q = constantClass X q := rfl

/-- The constant-coordinate identification is independent of the chosen point. -/
theorem equivConstants_eq [PathConnectedSpace X] (x y : X) :
    equivConstants X x = equivConstants X y := by
  apply AlgEquiv.ext
  intro h
  exact eval_eq X h x y

variable {Y : Type v} [TopologicalSpace Y]

/-- Pullback takes an actual constant cocycle to the same constant cocycle. -/
@[simp]
theorem pullback_constantClass (f : C(X, Y)) (q : ℚ) :
    pullback f (constantClass Y q) = constantClass X q := rfl

/-- A continuous map between path-connected spaces preserves constant
coordinates on degree-zero singular cohomology. -/
theorem equivConstants_pullback [PathConnectedSpace X] [PathConnectedSpace Y]
    (x : X) (y : Y) (f : C(X, Y)) (h : H0 Y) :
    equivConstants X x (pullback f h) = equivConstants Y y h :=
  eval_eq Y h (f x) y

end

end HodgeConjecture.SingularDegreeZero
