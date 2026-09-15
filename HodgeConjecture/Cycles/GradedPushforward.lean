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

universe u

/-- Restrict the existing closed pushforward to homogeneous integral
cycles with compatible source and image degrees. -/
def gradedClosedImmersionPushforward {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) : cyclesOfDegree ℤ δX n →ₗ[ℤ] cyclesOfDegree ℤ δY n where
  toFun c := ⟨closedImmersionPushforward ℤ i c.val,
    closedImmersionPushforward_mem_cyclesOfDegree ℤ δX δY i n c.val c.property hdeg⟩
  map_add' c d := Subtype.ext ((closedImmersionPushforward ℤ i).map_add c.val d.val)
  map_smul' r c := Subtype.ext ((closedImmersionPushforward ℤ i).map_smul r c.val)

@[simp]
theorem gradedClosedImmersionPushforward_val {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    (gradedClosedImmersionPushforward δX δY i hdeg n c).val =
      closedImmersionPushforward ℤ i c.val := rfl

/-- Graded identity is inherited from the existing cycle identity. -/
theorem gradedClosedImmersionPushforward_id (X : Scheme.{u})
    (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (closedImageSubscheme (𝟙 X) W) = supportDegree δ W)
    (n : ℤ) :
    gradedClosedImmersionPushforward δ δ (𝟙 X) hdeg n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change closedImmersionPushforward ℤ (𝟙 X) c.val = c.val
  rw [closedImmersionPushforward_id, LinearMap.id_apply]

/-- Composition is the existing geometric composition, restricted to the
same homogeneous submodules. -/
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
        gradedClosedImmersionPushforward δX δZ (i ≫ j) hij n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change ((closedImmersionPushforward ℤ j).comp
    (closedImmersionPushforward ℤ i)) c.val = _
  rw [closedImmersionPushforward_comp]
  rfl

end

end HodgeConjecture.SchemeCycles
