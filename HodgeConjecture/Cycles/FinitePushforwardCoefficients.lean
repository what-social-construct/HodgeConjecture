module

public import HodgeConjecture.Cycles.FinitePushforwardResidue
public import HodgeConjecture.Cycles.FiniteAffineFiber

@[expose] public section

/-!
# Coefficients of the existing finite pushforward

The coefficient at a reduced point closure is the sum over the actual
scheme fiber, weighted by the actual residue-field degrees. This identifies
the existing support-to-image pushforward with the coefficient expression
in Stacks 02RT: https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The existing scheme-theoretic image is the reduced closure of the image point. -/
theorem imageSubscheme_eq_pointSupport (W : IntegralClosedSubscheme X) :
    imageSubscheme f W = pointSupport Y (f.base (ambientGenericPoint W)) := by
  rw [← ambientGenericPoint_imageSubscheme, pointSupport_ambientGenericPoint]

/-- Every actual point fiber of a finite morphism is finite. -/
theorem finiteFiber_finite [IsFinite f] (y : Y) : Finite {x : X // f.base x = y} := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := y) (by trivial)
  exact finiteAffine_fiber_finite f U hU ⟨y, hy⟩

/-- The original cycle pushforward, evaluated using actual points and residue degrees. -/
theorem finitePushforward_apply_pointSupport (R : Type v) [CommSemiring R] [IsFinite f]
    (c : Cycles X R) (y : Y) :
    finitePushforward R f c (pointSupport Y y) =
      ∑ᶠ x : {x : X // f.base x = y},
        (residueFieldDegree f x.val : R) * c (pointSupport X x.val) := by
  classical
  letI := finiteFiber_finite f y
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, Finsupp.add_apply, mul_add, hc, hd]
    exact (finsum_add_distrib (Set.toFinite _) (Set.toFinite _)).symm
  | single W r =>
    rw [finitePushforward_single, imageSubscheme_eq_pointSupport,
      finitePushforwardDegree_eq_residueFieldDegree]
    by_cases h : f.base (ambientGenericPoint W) = y
    · let x₀ : {x : X // f.base x = y} := ⟨ambientGenericPoint W, h⟩
      rw [finsum_eq_single _ x₀]
      · simp [x₀, h, fundamentalCycle, pointSupport_ambientGenericPoint, mul_comm]
      · intro x hx
        have hn : pointSupport X x.val ≠ W := by
          intro he
          apply hx
          apply Subtype.ext
          simpa using congrArg ambientGenericPoint he
        simp [Ne.symm hn]
    · have himage : pointSupport Y (f.base (ambientGenericPoint W)) ≠ pointSupport Y y := by
        intro he
        exact h (by simpa using congrArg ambientGenericPoint he)
      have hz : ∀ x : {x : X // f.base x = y},
          (residueFieldDegree f x.val : R) * Finsupp.single W r (pointSupport X x.val) = 0 := by
        intro x
        have hn : pointSupport X x.val ≠ W := by
          intro he
          apply h
          have he' : x.val = ambientGenericPoint W := by
            simpa using congrArg ambientGenericPoint he
          rw [← he']
          exact x.property
        simp [Ne.symm hn]
      rw [finsum_eq_zero_of_forall_eq_zero hz]
      simp [fundamentalCycle, himage]

end

end HodgeConjecture.SchemeCycles
