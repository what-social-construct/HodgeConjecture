module

public import HodgeConjecture.Cycles.FinitePushforwardCoefficients
public import HodgeConjecture.Cycles.DivisorSupport

@[expose] public section

/-!
# Finite pushforward through actual closed carriers

For a commuting square with closed horizontal inclusions, the existing
finite and closed pushforwards commute. The image supports and residue
degrees are compared directly; no relation-preservation premise is used.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- Compatibility with closed carrier inclusions, on the existing cycle modules. -/
theorem finitePushforward_closedImmersion_square (R : Type v) [Semiring R]
    {W Z X Y : Scheme.{u}} (i : W ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (f : X ⟶ Y) (g : W ⟶ Z) [IsFinite f] [IsFinite g]
    (h : i ≫ f = g ≫ j) :
    (finitePushforward R f).comp (closedImmersionPushforward R i) =
      (closedImmersionPushforward R j).comp (finitePushforward R g) := by
  apply Finsupp.lhom_ext
  intro V r
  have hd : finitePushforwardDegree f (closedImageSubscheme i V) =
      finitePushforwardDegree g V := by
    rw [finitePushforwardDegree_eq_residueFieldDegree,
      finitePushforwardDegree_eq_residueFieldDegree, ambientGenericPoint_closedImageSubscheme]
    rw [← residueFieldDegree_comp_of_source_surjectiveOnStalks i f,
      h, residueFieldDegree_comp_of_target_surjectiveOnStalks]
  have hs : imageSubscheme f (closedImageSubscheme i V) =
      closedImageSubscheme j (imageSubscheme g V) := by
    apply (pointEquivIntegralClosedSubscheme Y).symm.injective
    change ambientGenericPoint _ = ambientGenericPoint _
    rw [ambientGenericPoint_imageSubscheme, ambientGenericPoint_closedImageSubscheme,
      ambientGenericPoint_closedImageSubscheme, ambientGenericPoint_imageSubscheme]
    exact congrArg (fun m : W ⟶ Y ↦ m.base (ambientGenericPoint V)) h
  simp only [LinearMap.comp_apply, closedImmersionPushforward_single,
    closedImageCycle, map_smul, finitePushforward_fundamentalCycle,
    finitePushforward_single, map_nsmul, closedImmersionPushforward_fundamentalCycle,
    hd, hs]

end

end HodgeConjecture.SchemeCycles
