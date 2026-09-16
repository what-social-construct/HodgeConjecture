import HodgeConjecture.Cycles.PrincipalDivisorDegree

/-!
# Existing closed pushforward on homogeneous cycles

The geometric closed-immersion pushforward restricts to the existing
degree submodules when source and image support degrees agree. Identity
and composition are inherited from the same ungraded geometric map.
The compatibility is an equality of support degrees; no relation or
quotient-descent hypothesis is part of this construction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- Restrict the existing closed pushforward to homogeneous cycles over
any coefficient semiring, with compatible source and image degrees. -/
def gradedClosedImmersionPushforwardWithCoefficients (R : Type v) [Semiring R]
    {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) : cyclesOfDegree R δX n →ₗ[R] cyclesOfDegree R δY n where
  toFun c := ⟨closedImmersionPushforward R i c.val,
    closedImmersionPushforward_mem_cyclesOfDegree R δX δY i n c.val c.property hdeg⟩
  map_add' c d := Subtype.ext ((closedImmersionPushforward R i).map_add c.val d.val)
  map_smul' r c := Subtype.ext ((closedImmersionPushforward R i).map_smul r c.val)

@[simp]
theorem gradedClosedImmersionPushforwardWithCoefficients_val (R : Type v) [Semiring R]
    {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree R δX n) :
    (gradedClosedImmersionPushforwardWithCoefficients R δX δY i hdeg n c).val =
      closedImmersionPushforward R i c.val := rfl

/-- Graded identity is inherited from the existing cycle identity. -/
theorem gradedClosedImmersionPushforwardWithCoefficients_id (R : Type v) [Semiring R]
    (X : Scheme.{u})
    (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (closedImageSubscheme (𝟙 X) W) = supportDegree δ W)
    (n : ℤ) :
    gradedClosedImmersionPushforwardWithCoefficients R δ δ (𝟙 X) hdeg n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change closedImmersionPushforward R (𝟙 X) c.val = c.val
  rw [closedImmersionPushforward_id, LinearMap.id_apply]

/-- Composition is the existing geometric composition, restricted to the
same homogeneous submodules. -/
theorem gradedClosedImmersionPushforwardWithCoefficients_comp (R : Type v) [Semiring R]
    {X Y Z : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (hj : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (closedImageSubscheme j W) = supportDegree δY W)
    (hij : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (closedImageSubscheme (i ≫ j) W) = supportDegree δX W)
    (n : ℤ) :
    (gradedClosedImmersionPushforwardWithCoefficients R δY δZ j hj n).comp
      (gradedClosedImmersionPushforwardWithCoefficients R δX δY i hi n) =
        gradedClosedImmersionPushforwardWithCoefficients R δX δZ (i ≫ j) hij n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change ((closedImmersionPushforward R j).comp
    (closedImmersionPushforward R i)) c.val = _
  rw [closedImmersionPushforward_comp]
  rfl

/-- The existing integral API is the integer specialization of the same
coefficient-parametric geometric map. -/
abbrev gradedClosedImmersionPushforward {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) : cyclesOfDegree ℤ δX n →ₗ[ℤ] cyclesOfDegree ℤ δY n :=
  gradedClosedImmersionPushforwardWithCoefficients ℤ δX δY i hdeg n

@[simp]
theorem gradedClosedImmersionPushforward_val {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    (gradedClosedImmersionPushforward δX δY i hdeg n c).val =
      closedImmersionPushforward ℤ i c.val := rfl

/-- Integral graded identity, using the coefficient-parametric theorem. -/
theorem gradedClosedImmersionPushforward_id (X : Scheme.{u})
    (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (closedImageSubscheme (𝟙 X) W) = supportDegree δ W)
    (n : ℤ) :
    gradedClosedImmersionPushforward δ δ (𝟙 X) hdeg n = LinearMap.id :=
  gradedClosedImmersionPushforwardWithCoefficients_id ℤ X δ hdeg n

/-- Integral graded composition, using the coefficient-parametric theorem. -/
theorem gradedClosedImmersionPushforward_comp {X Y Z : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (hj : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (closedImageSubscheme j W) = supportDegree δY W)
    (hij : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (closedImageSubscheme (i ≫ j) W) = supportDegree δX W)
    (n : ℤ) :
    (gradedClosedImmersionPushforward δY δZ j hj n).comp
      (gradedClosedImmersionPushforward δX δY i hi n) =
        gradedClosedImmersionPushforward δX δZ (i ≫ j) hij n :=
  gradedClosedImmersionPushforwardWithCoefficients_comp ℤ δX δY δZ i j hi hj hij n

end

end HodgeConjecture.SchemeCycles
