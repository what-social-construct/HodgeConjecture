import HodgeConjecture.Cycles.FinitePushforward
import HodgeConjecture.Cycles.CoefficientExtension
import HodgeConjecture.Cycles.GradedPushforward

/-!
# Finite pushforward on the existing homogeneous cycles

The actual degree-weighted finite pushforward restricts to the existing
supported submodules for compatible dimension functions. Its underlying
cycle map is unchanged. Integer-to-rational coefficient extension commutes
with that same map. No principal-relation or quotient-descent input is
part of these constructions.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- The degree of the actual image is evaluated at the mapped generic point. -/
theorem supportDegree_imageSubscheme {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (f : X ⟶ Y) (W : IntegralClosedSubscheme X) :
    supportDegree δ (imageSubscheme f W) = δ (f.base (ambientGenericPoint W)) := by
  rw [supportDegree, ambientGenericPoint_imageSubscheme]

/-- Degree-weighted finite pushforward preserves compatible homogeneous cycles. -/
theorem finitePushforward_mem_cyclesOfDegree (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R δX n)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W) :
    finitePushforward R f c ∈ cyclesOfDegree R δY n := by
  have hle : cyclesOfDegree R δX n ≤
      (cyclesOfDegree R δY n).comap (finitePushforward R f) := by
    change Finsupp.supported R R {W | supportDegree δX W = n} ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨W, hW, rfl⟩
    change finitePushforward R f (fundamentalCycle R W) ∈ cyclesOfDegree R δY n
    rw [finitePushforward_fundamentalCycle]
    exact (cyclesOfDegree R δY n).nsmul_mem
      (fundamentalCycle_mem_cyclesOfDegree R δY n (imageSubscheme f W)
        ((hdeg W).trans hW)) _
  exact hle hc

/-- Restriction of the same finite pushforward to the existing degree submodules. -/
def gradedFinitePushforward (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) : cyclesOfDegree R δX n →ₗ[R] cyclesOfDegree R δY n where
  toFun c := ⟨finitePushforward R f c.val,
    finitePushforward_mem_cyclesOfDegree R δX δY f n c.val c.property hdeg⟩
  map_add' c d := Subtype.ext ((finitePushforward R f).map_add c.val d.val)
  map_smul' r c := Subtype.ext ((finitePushforward R f).map_smul r c.val)

@[simp]
theorem gradedFinitePushforward_val (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree R δX n) :
    (gradedFinitePushforward R δX δY f hdeg n c).val =
      finitePushforward R f c.val := rfl

/-- On closed immersions the graded operation is exactly the existing one. -/
theorem gradedFinitePushforward_eq_closedImmersionPushforward (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme i W) = supportDegree δX W)
    (n : ℤ) :
    gradedFinitePushforward R δX δY i hdeg n =
      gradedClosedImmersionPushforwardWithCoefficients R δX δY i
        (fun W ↦ by simpa only [imageSubscheme_eq_closedImageSubscheme] using hdeg W) n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact LinearMap.congr_fun (finitePushforward_eq_closedImmersionPushforward i R) c.val

/-- Actual finite pushforward commutes with integer-to-rational coefficient cast. -/
theorem finitePushforward_rationalize {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (c : Cycles X ℤ) :
    finitePushforward ℚ f (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) (finitePushforward ℤ f c) := by
  have h : ((finitePushforward ℚ f).restrictScalars ℤ).comp
      (Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap) =
      (Finsupp.mapRange.linearMap (Int.castAddHom ℚ).toIntLinearMap).comp
        (finitePushforward ℤ f) := by
    apply Finsupp.lhom_ext
    intro W a
    simp [finitePushforward_single, fundamentalCycle, Finsupp.smul_single,
      mul_comm]
  exact LinearMap.congr_fun h c

/-- The same coefficient square restricts to the existing homogeneous submodules. -/
theorem gradedFinitePushforward_rationalize {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    gradedFinitePushforward ℚ δX δY f hdeg n (cyclesOfDegreeRationalize δX n c) =
      cyclesOfDegreeRationalize δY n (gradedFinitePushforward ℤ δX δY f hdeg n c) := by
  apply Subtype.ext
  exact finitePushforward_rationalize f c.val

end

end HodgeConjecture.SchemeCycles
