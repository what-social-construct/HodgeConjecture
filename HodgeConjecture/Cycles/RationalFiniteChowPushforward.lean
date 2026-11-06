module

public import HodgeConjecture.Cycles.FiniteChowPushforward
public import HodgeConjecture.Cycles.RationalChow

@[expose] public section

/-!
# Rational finite Chow pushforward

The existing coefficient-extension square transfers the proved integral
norm-generator identity to the rational relation span. Quotient descent
uses the same rational finite cycle map and commutes with the existing
integral-to-rational Chow map.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The rational span of the same actual principal generators is preserved. -/
theorem rationalPrincipalRelations_le_comap_finitePushforward
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) :
    rationalPrincipalRelations δX n ≤ (rationalPrincipalRelations δY n).comap
      (gradedFinitePushforward ℚ δX δY f hdeg n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedFinitePushforward ℚ δX δY f hdeg n
    (cyclesOfDegreeRationalize δX n (principalRelation δX n d)) ∈
      rationalPrincipalRelations δY n
  rw [gradedFinitePushforward_rationalize,
    gradedFinitePushforward_principalRelation k pY]
  exact Submodule.subset_span ⟨d.finiteImage δX δY f hdeg n, rfl⟩

/-- The original rational Chow quotient carries the same finite pushforward,
with canonical grading and proved relation preservation. -/
def rationalChowFinitePushforward
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ) :
    RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n →ₗ[ℚ]
      RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n :=
  let δX := DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)
  let δY := DimensionFunction.ofLocallyOfFiniteType k Y pY
  let hdeg := supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f
  (rationalPrincipalRelations δX n).mapQ (rationalPrincipalRelations δY n)
    (gradedFinitePushforward ℚ δX δY f hdeg n)
    (rationalPrincipalRelations_le_comap_finitePushforward k pY δX δY f hdeg n)

/-- The quotient map retains the original degree-weighted rational cycle map. -/
@[simp]
theorem rationalChowFinitePushforward_classMap
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ)
    (c : cyclesOfDegree ℚ (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n) :
    rationalChowFinitePushforward k pY f n
        (rationalClassMap (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n c) =
      rationalClassMap (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
        (gradedFinitePushforward ℚ
          (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY))
          (DimensionFunction.ofLocallyOfFiniteType k Y pY) f
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n c) := rfl

/-- Integral-to-rational Chow extension commutes with this same finite pushforward. -/
theorem rationalChowFinitePushforward_rationalize
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ)
    (c : ChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n) :
    rationalChowFinitePushforward k pY f n
        (chowRationalize (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n c) =
      chowRationalize (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
        (chowFinitePushforward k pY f n c) := by
  obtain ⟨c, rfl⟩ := classMap_surjective _ n c
  rw [chowRationalize_classMap, rationalChowFinitePushforward_classMap,
    chowFinitePushforward_classMap, chowRationalize_classMap,
    gradedFinitePushforward_rationalize]

end

end HodgeConjecture.SchemeCycles
