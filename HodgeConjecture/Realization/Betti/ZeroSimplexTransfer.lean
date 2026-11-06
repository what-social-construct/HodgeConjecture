module

public import HodgeConjecture.Realization.Betti.FiniteTransfer

@[expose] public section

/-!
# Transfer as a sum over actual singular-simplex lifts

Lifts of a singular zero-simplex are classified by the actual fiber over
its point. This identifies degree-zero transfer with the conventional sum
of cochain values over all lifted singular zero-simplices.
-/

set_option autoImplicit false

namespace HodgeConjecture.SingularDegreeZero

noncomputable section

open Classical
open scoped BigOperators

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual continuous singular zero-simplices lifting the given simplex. -/
abbrev ZeroSimplexLift (f : C(X, Y)) (σ : Simplex Y 0) :=
  {τ : Simplex X 0 // f.comp τ = σ}

/-- A lift of a zero-simplex is determined by its point in the actual fiber.
No discreteness or finiteness assumption is needed for this classification. -/
def zeroSimplexLiftEquiv (f : C(X, Y)) (σ : Simplex Y 0) :
    ZeroSimplexLift f σ ≃ {x : X // f x = σ default} where
  toFun τ := ⟨τ.val default, congrArg (fun t : Simplex Y 0 ↦ t default) τ.property⟩
  invFun x := ⟨pointSimplex X x.val, by
    ext t
    apply x.property.trans
    apply congrArg σ
    apply Convexity.StdSimplex.ext
    ext i
    simp⟩
  left_inv τ := Subtype.ext (pointSimplex_eq X τ.val)
  right_inv _ := Subtype.ext rfl

@[simp]
theorem zeroSimplexLiftEquiv_apply (f : C(X, Y)) (σ : Simplex Y 0)
    (τ : ZeroSimplexLift f σ) :
    (zeroSimplexLiftEquiv f σ τ).val = τ.val default := rfl

@[simp]
theorem zeroSimplexLiftEquiv_symm_apply (f : C(X, Y)) (σ : Simplex Y 0)
    (x : {x : X // f x = σ default}) :
    ((zeroSimplexLiftEquiv f σ).symm x).val = pointSimplex X x.val := rfl

/-- The finite lift set is obtained from the actual point fiber equivalence,
without adding a finiteness instance for unrestricted singular simplices. -/
instance zeroSimplexLiftFintype [Fintype X] (f : C(X, Y)) (σ : Simplex Y 0) :
    Fintype (ZeroSimplexLift f σ) :=
  Fintype.ofEquiv {x : X // f x = σ default} (zeroSimplexLiftEquiv f σ).symm

/-- Cochain summation over actual zero-simplex lifts equals the point-fiber sum. -/
theorem sum_zeroSimplexLifts [Fintype X] (f : C(X, Y)) (σ : Simplex Y 0)
    (a : ZeroCochain X) :
    (∑ τ : ZeroSimplexLift f σ, a τ.val) =
      ∑ x, if f x = σ default then a (pointSimplex X x) else 0 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun x : X ↦ f x = σ default) _
    (by simp) (fun x ↦ a (pointSimplex X x))]
  exact ((zeroSimplexLiftEquiv f σ).symm.sum_comp (fun τ ↦ a τ.val)).symm

variable [DiscreteTopology X] [DiscreteTopology Y]

omit [DiscreteTopology X] in
/-- Degree-zero transfer is literally the sum of cochain values over the
actual continuous singular zero-simplices lifting the target simplex. -/
theorem transfer_simplex_eq_sum_lifts [Fintype X] (f : C(X, Y)) (h : H0 X)
    (σ : Simplex Y 0) :
    (transfer f h).val σ = ∑ τ : ZeroSimplexLift f σ, h.val τ.val := by
  rw [sum_zeroSimplexLifts]
  simpa only [eval_apply, pointSimplex_eq] using eval_transfer f h (σ default)

end

end HodgeConjecture.SingularDegreeZero
