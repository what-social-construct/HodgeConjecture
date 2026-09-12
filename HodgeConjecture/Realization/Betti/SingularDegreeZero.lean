import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Rational singular cohomology in degree zero

The cochains are functions on actual continuous singular simplices, using
Mathlib's standard topological simplices. The differential is the alternating
sum of the two face restrictions. The face construction is explicitly
identified with Mathlib's singular simplicial set.

Unreduced singular cochains start in degree zero, so there are no incoming
boundaries in that degree: `H0` is exactly the kernel of this differential.
The degree-zero cup product is pointwise multiplication of zero-cochains.
For a discrete space every singular one-simplex is constant, so evaluation
on point simplices gives an algebra equivalence with functions on points.
-/

set_option autoImplicit false

namespace HodgeConjecture

open CategoryTheory Simplicial

noncomputable section

universe u v w

namespace SingularDegreeZero

variable (X : Type u) [TopologicalSpace X]

/-- Actual continuous singular simplices on the standard topological simplex. -/
abbrev Simplex (n : ℕ) := C(SimplexCategory.toTopObj ⦋n⦌, X)

/-- These are precisely the simplices in Mathlib's singular simplicial set. -/
def simplexEquivSingularSet (n : ℕ) :
    Simplex X n ≃ (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm

/-- The zero-simplex at an actual point of the space. -/
def pointSimplex (x : X) : Simplex X 0 := ContinuousMap.const _ x

@[simp]
theorem pointSimplex_apply (x : X) (t : SimplexCategory.toTopObj ⦋0⦌) :
    pointSimplex X x t = x := rfl

/-- Every continuous zero-simplex is its point simplex. -/
@[simp]
theorem pointSimplex_eq (σ : Simplex X 0) : pointSimplex X (σ default) = σ := by
  ext t
  exact congrArg σ (Subsingleton.elim default t)

/-- The actual two singular face restrictions. Face zero is the terminal
vertex and face one is the initial vertex. -/
def face (γ : Simplex X 1) (i : Fin 2) : Simplex X 0 :=
  γ.comp ⟨SimplexCategory.toTopMap (SimplexCategory.δ i),
    SimplexCategory.continuous_toTopMap _⟩

/-- The continuous-map face is exactly the face in the singular set. -/
theorem simplexEquivSingularSet_face (γ : Simplex X 1) (i : Fin 2) :
    simplexEquivSingularSet X 0 (face X γ i) =
      (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op
        (simplexEquivSingularSet X 1 γ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋0⦌)).injective
  ext t
  rfl

/-- Unrestricted rational functions on actual singular zero-simplices. -/
abbrev ZeroCochain := Simplex X 0 → ℚ

/-- Unrestricted rational functions on actual singular one-simplices. -/
abbrev OneCochain := Simplex X 1 → ℚ

/-- The actual degree-zero singular coboundary, dual to the alternating
boundary of a one-simplex. -/
def coboundary : ZeroCochain X →ₗ[ℚ] OneCochain X where
  toFun φ γ := φ (face X γ 0) - φ (face X γ 1)
  map_add' φ ψ := by
    funext γ
    simp only [Pi.add_apply]
    ring
  map_smul' r φ := by
    funext γ
    simp [mul_sub]

@[simp]
theorem coboundary_apply (φ : ZeroCochain X) (γ : Simplex X 1) :
    coboundary X φ γ = φ (face X γ 0) - φ (face X γ 1) := rfl

theorem mem_kernel_iff (φ : ZeroCochain X) :
    φ ∈ LinearMap.ker (coboundary X) ↔
      ∀ γ : Simplex X 1, φ (face X γ 0) = φ (face X γ 1) := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [coboundary_apply, Pi.zero_apply, sub_eq_zero]

/-- Singular zero-cocycles are the coboundary kernel, closed under the
degree-zero cup product. -/
def cocycles : Subalgebra ℚ (ZeroCochain X) where
  carrier := (LinearMap.ker (coboundary X) : Set (ZeroCochain X))
  zero_mem' := (mem_kernel_iff X 0).2 (fun γ ↦ rfl)
  one_mem' := (mem_kernel_iff X 1).2 (fun γ ↦ rfl)
  add_mem' {φ ψ} hφ hψ := by
    apply (mem_kernel_iff X (φ + ψ)).2
    intro γ
    change φ (face X γ 0) + ψ (face X γ 0) = φ (face X γ 1) + ψ (face X γ 1)
    rw [(mem_kernel_iff X φ).1 hφ γ, (mem_kernel_iff X ψ).1 hψ γ]
  mul_mem' {φ ψ} hφ hψ := by
    apply (mem_kernel_iff X (φ * ψ)).2
    intro γ
    change φ (face X γ 0) * ψ (face X γ 0) = φ (face X γ 1) * ψ (face X γ 1)
    rw [(mem_kernel_iff X φ).1 hφ γ, (mem_kernel_iff X ψ).1 hψ γ]
  algebraMap_mem' r := (mem_kernel_iff X (algebraMap ℚ (ZeroCochain X) r)).2 (fun γ ↦ rfl)

/-- The underlying submodule is literally the singular coboundary kernel. -/
theorem cocycles_toSubmodule :
    (cocycles X).toSubmodule = LinearMap.ker (coboundary X) := rfl

/-- Unreduced rational singular cohomology in degree zero. There is no
degree-negative-one cochain term, hence no incoming boundary quotient. -/
abbrev H0 := ↥(cocycles X)

/-- Evaluation of a singular zero-class at the zero-simplex of a point. -/
def eval : H0 X →ₐ[ℚ] (X → ℚ) where
  toFun h x := h.val (pointSimplex X x)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem eval_apply (h : H0 X) (x : X) :
    eval X h x = h.val (pointSimplex X x) := rfl

/-- A singular zero-class is determined by evaluation at actual points. -/
theorem eval_injective : Function.Injective (eval X) := by
  intro h k he
  apply Subtype.ext
  funext σ
  simpa only [eval_apply, pointSimplex_eq] using congrFun he (σ default)

/-- The cup product in degree zero is inherited from pointwise cochain
multiplication; closure was proved from the actual cocycle equations. -/
def cup (a b : H0 X) : H0 X := a * b

@[simp]
theorem eval_cup (a b : H0 X) (x : X) :
    eval X (cup X a b) x = eval X a x * eval X b x := rfl

section Discrete

variable [DiscreteTopology X]

/-- Both faces of a singular one-simplex agree in a discrete space. -/
theorem face_eq_of_discrete (γ : Simplex X 1) (i j : Fin 2) :
    face X γ i = face X γ j := by
  ext t
  exact TotallyDisconnectedSpace.eq_of_continuous γ γ.continuous _ _

/-- Every zero-cochain is a cocycle on a discrete space. -/
theorem coboundary_eq_zero (φ : ZeroCochain X) : coboundary X φ = 0 := by
  funext γ
  simp only [coboundary_apply, face_eq_of_discrete X γ 0 1, sub_self, Pi.zero_apply]

/-- A point function determines a genuine singular zero-cocycle. -/
def ofFunctions : (X → ℚ) →ₐ[ℚ] H0 X where
  toFun f := ⟨fun σ ↦ f (σ default), coboundary_eq_zero X _⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem ofFunctions_apply (f : X → ℚ) (σ : Simplex X 0) :
    (ofFunctions X f).val σ = f (σ default) := rfl

@[simp]
theorem eval_ofFunctions (f : X → ℚ) : eval X (ofFunctions X f) = f := rfl

@[simp]
theorem ofFunctions_eval (h : H0 X) : ofFunctions X (eval X h) = h := by
  apply eval_injective X
  exact eval_ofFunctions X _

/-- Actual degree-zero singular cohomology of a discrete space is the
algebra of rational functions on its points. -/
def equivFunctions : H0 X ≃ₐ[ℚ] (X → ℚ) :=
  AlgEquiv.ofAlgHom (eval X) (ofFunctions X)
    (AlgHom.ext (eval_ofFunctions X)) (AlgHom.ext (ofFunctions_eval X))

@[simp]
theorem equivFunctions_apply (h : H0 X) : equivFunctions X h = eval X h := rfl

@[simp]
theorem equivFunctions_symm_apply (f : X → ℚ) :
    (equivFunctions X).symm f = ofFunctions X f := rfl

end Discrete

variable {X}
variable {Y : Type v} [TopologicalSpace Y] {Z : Type w} [TopologicalSpace Z]

/-- Singular cohomology pullback is precomposition of actual simplices. -/
def pullback (f : C(X, Y)) : H0 Y →ₐ[ℚ] H0 X where
  toFun h := ⟨fun σ ↦ h.val (f.comp σ), by
    apply (mem_kernel_iff X _).2
    intro γ
    exact (mem_kernel_iff Y h.val).1 h.property (f.comp γ)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem pullback_apply (f : C(X, Y)) (h : H0 Y) (σ : Simplex X 0) :
    (pullback f h).val σ = h.val (f.comp σ) := rfl

@[simp]
theorem eval_pullback (f : C(X, Y)) (h : H0 Y) (x : X) :
    eval X (pullback f h) x = eval Y h (f x) := rfl

@[simp]
theorem pullback_id : pullback (ContinuousMap.id X) = AlgHom.id ℚ (H0 X) := by
  apply AlgHom.ext
  intro h
  apply eval_injective X
  funext x
  rfl

/-- Pullback is contravariantly functorial on continuous maps. -/
theorem pullback_comp (f : C(X, Y)) (g : C(Y, Z)) :
    pullback (g.comp f) = (pullback f).comp (pullback g) := by
  apply AlgHom.ext
  intro h
  apply eval_injective X
  funext x
  rfl

@[simp]
theorem equivFunctions_pullback [DiscreteTopology X] [DiscreteTopology Y]
    (f : C(X, Y)) (h : H0 Y) (x : X) :
    equivFunctions X (pullback f h) x = equivFunctions Y h (f x) := rfl

end SingularDegreeZero

end

end HodgeConjecture
