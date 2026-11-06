module

public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import HodgeConjecture.Realization.Betti.SingularCochains

@[expose] public section

/-!
# Degree-zero singular cohomology from actual path components

A continuous map to a discrete label space, with one chosen point in each
label and paths from every point to its labelled point, computes actual
singular H⁰ as functions on the labels. This will distinguish the two
components of a circle-chart overlap without replacing cohomology by a
desired coordinate space.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularComponents

open SingularDegreeZero

universe u v

variable {X : Type u} [TopologicalSpace X] {I : Type v} [TopologicalSpace I]

/-- Evaluate original singular zero-classes at the specified actual component points. -/
def evaluationOnSamples (point : I → X) : H0 X →ₐ[ℚ] (I → ℚ) where
  toFun h i := eval X h (point i)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Pull a point function back along the original continuous discrete-component map. -/
def classFromComponents [DiscreteTopology I] (label : C(X, I)) : (I → ℚ) →ₐ[ℚ] H0 X :=
  (pullback label).comp (ofFunctions I)

/-- Component evaluation is an equivalence, proved using the original path/cocycle equation. -/
def componentEquiv [DiscreteTopology I] (label : C(X, I)) (point : I → X)
    (hpoint : ∀ i, label (point i) = i)
    (hjoined : ∀ x, Joined x (point (label x))) : H0 X ≃ₐ[ℚ] (I → ℚ) :=
  AlgEquiv.ofAlgHom (evaluationOnSamples point) (classFromComponents label)
    (by
      apply AlgHom.ext
      intro q
      funext i
      change eval X (pullback label (ofFunctions I q)) (point i) = q i
      rw [eval_pullback, eval_ofFunctions, hpoint])
    (by
      apply AlgHom.ext
      intro h
      apply eval_injective X
      funext x
      change eval X (pullback label (ofFunctions I (fun i ↦ eval X h (point i)))) x = eval X h x
      rw [eval_pullback, eval_ofFunctions]
      exact (eval_eq_of_joined h (hjoined x)).symm)

@[simp]
theorem componentEquiv_apply [DiscreteTopology I] (label : C(X, I)) (point : I → X)
    (hpoint : ∀ i, label (point i) = i) (hjoined : ∀ x, Joined x (point (label x)))
    (h : H0 X) (i : I) :
    componentEquiv label point hpoint hjoined h i = eval X h (point i) := rfl

@[simp]
theorem componentEquiv_constantClass [DiscreteTopology I] (label : C(X, I)) (point : I → X)
    (hpoint : ∀ i, label (point i) = i) (hjoined : ∀ x, Joined x (point (label x))) (q : ℚ) :
    componentEquiv label point hpoint hjoined (constantClass X q) = fun _ ↦ q := rfl

/-- Categorical H⁰ of the original full singular complex has these same proved coordinates. -/
def cohomologyZeroEquiv [DiscreteTopology I] (label : C(X, I)) (point : I → X)
    (hpoint : ∀ i, label (point i) = i) (hjoined : ∀ x, Joined x (point (label x))) :
    SingularCochains.Cohomology (TopCat.of X) 0 ≃ₗ[ℚ] (I → ℚ) :=
  (SingularCochains.cohomologyZeroIso X).toLinearEquiv.trans
    (componentEquiv label point hpoint hjoined).toLinearEquiv

section Sum

variable (A : Type u) (B : Type v) [TopologicalSpace A] [TopologicalSpace B]

/-- The actual two labels of a topological disjoint union. -/
def sumLabel : C(A ⊕ B, Bool) where
  toFun := Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  continuous_toFun := continuous_sum_dom.mpr ⟨continuous_const, continuous_const⟩

/-- Actual component base points in the two summands. -/
def sumPoint (a : A) (b : B) : Bool → A ⊕ B :=
  fun i ↦ if i then Sum.inr b else Sum.inl a

theorem sumLabel_point (a : A) (b : B) (i : Bool) :
    sumLabel A B (sumPoint A B a b i) = i := by cases i <;> rfl

theorem joined_sumPoint [PathConnectedSpace A] [PathConnectedSpace B] (a : A) (b : B)
    (x : A ⊕ B) : Joined x (sumPoint A B a b (sumLabel A B x)) := by
  cases x with
  | inl x => exact (PathConnectedSpace.joined x a).map continuous_inl
  | inr x => exact (PathConnectedSpace.joined x b).map continuous_inr

/-- A disjoint union of two actual path-connected spaces has two independent H⁰ coordinates. -/
def sumEquiv [PathConnectedSpace A] [PathConnectedSpace B] (a : A) (b : B) :
    H0 (A ⊕ B) ≃ₐ[ℚ] (Bool → ℚ) :=
  componentEquiv (sumLabel A B) (sumPoint A B a b) (sumLabel_point A B a b)
    (joined_sumPoint A B a b)

end Sum

end HodgeConjecture.SingularComponents
