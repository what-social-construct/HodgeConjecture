module

public import HodgeConjecture.Cycles.FinitePushforwardComposition
public import HodgeConjecture.Cycles.RationalFiniteChowPushforward

@[expose] public section

/-!
# Functoriality of the existing finite Chow pushforward

The cycle composition law descends to the original integral and rational
Chow quotients. The field-induced gradings use the given structural map
and its actual composites; no new quotient or compatibility premise is
introduced. These laws concern finite morphisms, not general proper maps.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Identity induces identity on the existing integral Chow quotient. -/
@[simp]
theorem chowFinitePushforward_id
    (k : Type u) [Field k] (X : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℤ) :
    chowFinitePushforward k p (𝟙 X) n = LinearMap.id := by
  apply (principalRelations _ n).quot_hom_ext
  intro c
  change classMap _ n (gradedFinitePushforward ℤ _ _ (𝟙 X) _ n c) = classMap _ n c
  rw [gradedFinitePushforward_id]
  rfl

/-- Integral finite Chow pushforward respects composition on the existing
canonical field grading and principal-relation quotient. -/
theorem chowFinitePushforward_comp
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g] (n : ℤ) :
    (chowFinitePushforward k p g n).comp
        (chowFinitePushforward k (g ≫ p) f n) =
      chowFinitePushforward k p (f ≫ g) n := by
  apply (principalRelations _ n).quot_hom_ext
  intro c
  change classMap _ n
      (((gradedFinitePushforward ℤ _ _ g
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k p g) n).comp
        (gradedFinitePushforward ℤ _ _ f
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k (g ≫ p) f) n)) c) =
    classMap _ n (gradedFinitePushforward ℤ _ _ (f ≫ g)
      (supportDegree_imageSubscheme_ofLocallyOfFiniteType k p (f ≫ g)) n c)
  rw [gradedFinitePushforward_comp]
  rfl

/-- Identity induces identity on the existing rational Chow quotient. -/
@[simp]
theorem rationalChowFinitePushforward_id
    (k : Type u) [Field k] (X : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℤ) :
    rationalChowFinitePushforward k p (𝟙 X) n = LinearMap.id := by
  apply (rationalPrincipalRelations _ n).quot_hom_ext
  intro c
  change rationalClassMap _ n (gradedFinitePushforward ℚ _ _ (𝟙 X) _ n c) =
    rationalClassMap _ n c
  rw [gradedFinitePushforward_id]
  rfl

/-- Rational finite Chow pushforward respects the same composition, using
the actual rational cycles and the rational span of principal relations. -/
theorem rationalChowFinitePushforward_comp
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g] (n : ℤ) :
    (rationalChowFinitePushforward k p g n).comp
        (rationalChowFinitePushforward k (g ≫ p) f n) =
      rationalChowFinitePushforward k p (f ≫ g) n := by
  apply (rationalPrincipalRelations _ n).quot_hom_ext
  intro c
  change rationalClassMap _ n
      (((gradedFinitePushforward ℚ _ _ g
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k p g) n).comp
        (gradedFinitePushforward ℚ _ _ f
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k (g ≫ p) f) n)) c) =
    rationalClassMap _ n (gradedFinitePushforward ℚ _ _ (f ≫ g)
      (supportDegree_imageSubscheme_ofLocallyOfFiniteType k p (f ≫ g)) n c)
  rw [gradedFinitePushforward_comp]
  rfl

end

end HodgeConjecture.SchemeCycles
