import HodgeConjecture.Cycles.CoefficientExtension
import HodgeConjecture.Cycles.GradedPushforward
import HodgeConjecture.Cycles.IsomorphismTransport

/-!
# Coefficient extension and actual closed pushforward

The same geometric closed-image operation commutes with integer-to-rational
coefficient extension, first on all finite cycles and then on their existing
homogeneous submodules. No relation or quotient hypothesis is used here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- The actual ungraded closed pushforward commutes with coefficient cast
on the same integral closed supports. -/
theorem closedImmersionPushforward_rationalize {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (c : Cycles X ℤ) :
    closedImmersionPushforward ℚ i
        (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _)
        (closedImmersionPushforward ℤ i c) := by
  have h : ((closedImmersionPushforward ℚ i).restrictScalars ℤ).comp
      (Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap) =
      (Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap).comp
        (closedImmersionPushforward ℤ i) := by
    apply Finsupp.lhom_ext
    intro W a
    simp [closedImmersionPushforward_single, closedImageCycle, fundamentalCycle]
  exact LinearMap.congr_fun h c

/-- Restrict coefficient/pushforward compatibility to the same existing
homogeneous submodules, with the identical support-degree comparison. -/
theorem gradedClosedImmersionPushforward_rationalize {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hdeg n
        (cyclesOfDegreeRationalize δX n c) =
      cyclesOfDegreeRationalize δY n
        (gradedClosedImmersionPushforward δX δY i hdeg n c) := by
  apply Subtype.ext
  exact closedImmersionPushforward_rationalize i c.val

/-- Actual open restriction along an isomorphism preserves the corresponding
homogeneous cycle submodules over any semiring of coefficients. -/
theorem openRestriction_iso_mem_cyclesOfDegree
    (R : Type v) [Semiring R] {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) (c : Cycles Y R)
    (hc : c ∈ cyclesOfDegree R δ n) :
    openRestriction R e.hom c ∈
      cyclesOfDegree R (δ.comapClosedImmersion e.hom) n := by
  rw [openRestriction_iso_eq_pushforward_inv]
  apply closedImmersionPushforward_mem_cyclesOfDegree R δ
    (δ.comapClosedImmersion e.hom) e.inv n c hc
  intro W
  rw [supportDegree_comapClosedImmersion]
  have h : closedImageSubscheme e.hom (closedImageSubscheme e.inv W) = W :=
    (closedImageSubschemeEquiv e).apply_symm_apply W
  rw [h]

end

end HodgeConjecture.SchemeCycles
