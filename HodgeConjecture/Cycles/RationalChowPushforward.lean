module

public import HodgeConjecture.Cycles.RationalChow
public import HodgeConjecture.Cycles.CoefficientPushforward
public import HodgeConjecture.Cycles.ChowPushforward

@[expose] public section

/-!
# Rational Chow pushforward along actual closed immersions

Coefficient extension commutes with the existing geometric pushforward.
Its proved action on actual integral principal divisors therefore preserves
the rational relation span. Quotient descent retains the cycle formula,
identity and composition, and commutes with the integral Chow comparison.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TensorProduct

noncomputable section

universe u

/-- The actual principal-generator identity also preserves the rational span. -/
theorem rationalPrincipalRelations_le_comap_closedImmersionPushforward
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) :
    rationalPrincipalRelations δX n ≤ (rationalPrincipalRelations δY n).comap
      (gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hdeg n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hdeg n
    (cyclesOfDegreeRationalize δX n (principalRelation δX n d)) ∈
      rationalPrincipalRelations δY n
  rw [gradedClosedImmersionPushforward_rationalize,
    gradedClosedImmersionPushforward_principalRelation]
  exact Submodule.subset_span ⟨d.closedImage δX δY i hdeg n, rfl⟩

/-- Closed pushforward on the quotient of actual rational homogeneous cycles. -/
def rationalChowClosedImmersionPushforward {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) : RationalChowGroup δX n →ₗ[ℚ] RationalChowGroup δY n :=
  (rationalPrincipalRelations δX n).mapQ (rationalPrincipalRelations δY n)
    (gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hdeg n)
    (rationalPrincipalRelations_le_comap_closedImmersionPushforward δX δY i hdeg n)

@[simp]
theorem rationalChowClosedImmersionPushforward_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℚ δX n) :
    rationalChowClosedImmersionPushforward δX δY i hdeg n (rationalClassMap δX n c) =
      rationalClassMap δY n
        (gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hdeg n c) := rfl

/-- The actual restricted dimension function supplies the degree comparison. -/
theorem rationalChowClosedImmersionPushforward_restricted_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (n : ℤ) (c : cyclesOfDegree ℚ (δ.comapClosedImmersion i) n) :
    rationalChowClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n
        (rationalClassMap (δ.comapClosedImmersion i) n c) =
      rationalClassMap δ n
        (gradedClosedImmersionPushforwardWithCoefficients ℚ (δ.comapClosedImmersion i) δ i
          (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n c) := rfl

/-- Identity is inherited from the same geometric cycle identity. -/
theorem rationalChowClosedImmersionPushforward_id (X : Scheme.{u}) [IsNoetherian X]
    (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (closedImageSubscheme (𝟙 X) W) = supportDegree δ W)
    (n : ℤ) :
    rationalChowClosedImmersionPushforward δ δ (𝟙 X) hdeg n = LinearMap.id := by
  apply (rationalPrincipalRelations δ n).quot_hom_ext
  intro c
  change rationalClassMap δ n
    (gradedClosedImmersionPushforwardWithCoefficients ℚ δ δ (𝟙 X) hdeg n c) =
      rationalClassMap δ n c
  rw [gradedClosedImmersionPushforwardWithCoefficients_id, LinearMap.id_apply]

/-- Quotient composition follows the existing actual cycle composition. -/
theorem rationalChowClosedImmersionPushforward_comp {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (hj : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (closedImageSubscheme j W) = supportDegree δY W)
    (hij : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (closedImageSubscheme (i ≫ j) W) = supportDegree δX W)
    (n : ℤ) :
    (rationalChowClosedImmersionPushforward δY δZ j hj n).comp
      (rationalChowClosedImmersionPushforward δX δY i hi n) =
        rationalChowClosedImmersionPushforward δX δZ (i ≫ j) hij n := by
  apply (rationalPrincipalRelations δX n).quot_hom_ext
  intro c
  change rationalClassMap δZ n
      (((gradedClosedImmersionPushforwardWithCoefficients ℚ δY δZ j hj n).comp
        (gradedClosedImmersionPushforwardWithCoefficients ℚ δX δY i hi n)) c) =
    rationalClassMap δZ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ δX δZ (i ≫ j) hij n c)
  rw [gradedClosedImmersionPushforwardWithCoefficients_comp]

/-- Rationalization of integral Chow classes commutes with actual closed pushforward. -/
theorem rationalChowClosedImmersionPushforward_chowRationalize {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (z : ChowGroup δX n) :
    rationalChowClosedImmersionPushforward δX δY i hdeg n (chowRationalize δX n z) =
      chowRationalize δY n (chowClosedImmersionPushforward δX δY i hdeg n z) := by
  obtain ⟨c, rfl⟩ := classMap_surjective δX n z
  simp only [chowRationalize_classMap, rationalChowClosedImmersionPushforward_classMap,
    chowClosedImmersionPushforward_classMap, gradedClosedImmersionPushforward_rationalize]

/-- The rational cycle quotient map is exactly scalar extension of the
integral Chow pushforward under the representative-preserving comparisons. -/
theorem rationalChowClosedImmersionPushforward_chowRationalizationEquiv
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (t : ℚ ⊗[ℤ] ChowGroup δX n) :
    rationalChowClosedImmersionPushforward δX δY i hdeg n
        (chowRationalizationEquiv δX n t) =
      chowRationalizationEquiv δY n
        ((chowClosedImmersionPushforward δX δY i hdeg n).baseChange ℚ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul q z =>
      obtain ⟨c, rfl⟩ := classMap_surjective δX n z
      simp only [chowRationalizationEquiv_tmul_classMap,
        rationalChowClosedImmersionPushforward_classMap, map_smul,
        LinearMap.baseChange_tmul, chowClosedImmersionPushforward_classMap,
        gradedClosedImmersionPushforward_rationalize]
  | add t s ht hs => simp only [map_add, ht, hs]

end

end HodgeConjecture.SchemeCycles
