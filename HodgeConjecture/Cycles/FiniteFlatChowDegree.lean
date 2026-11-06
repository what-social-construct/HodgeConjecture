module

public import HodgeConjecture.Cycles.FiniteFlatChowPullback
public import HodgeConjecture.Cycles.FiniteFlatRank
public import HodgeConjecture.Cycles.RationalFiniteChowPushforward

@[expose] public section

/-! The degree law on the original integral and rational Chow quotients,
for the original maps and the geometric rank of the original finite flat morphism. -/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

theorem chowFinitePushforward_finiteFlatPullback_of_finrank_eq
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) (d : ℕ)
    (hd : ∀ y : Y, f.finrank y = d)
    (c : ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    chowFinitePushforward k pY f n (chowFiniteFlatPullback k pY f n c) = d • c := by
  obtain ⟨c, rfl⟩ := classMap_surjective _ n c
  rw [chowFiniteFlatPullback_classMap, chowFinitePushforward_classMap]
  have h : gradedFinitePushforward ℤ
      (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY))
      (DimensionFunction.ofLocallyOfFiniteType k Y pY) f
      (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n
      (gradedFiniteFiberPullback f k ℤ pY n c) = d • c := by
    apply Subtype.ext
    exact finitePushforward_finiteFiberPullback_of_finrank_eq f ℤ d hd c.val
  rw [h, map_nsmul]

theorem rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) (d : ℕ)
    (hd : ∀ y : Y, f.finrank y = d)
    (c : RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    rationalChowFinitePushforward k pY f n (rationalChowFiniteFlatPullback k pY f n c) =
      d • c := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n c
  rw [rationalChowFiniteFlatPullback_classMap, rationalChowFinitePushforward_classMap]
  have h : gradedFinitePushforward ℚ
      (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY))
      (DimensionFunction.ofLocallyOfFiniteType k Y pY) f
      (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n
      (gradedFiniteFiberPullback f k ℚ pY n c) = d • c := by
    apply Subtype.ext
    exact finitePushforward_finiteFiberPullback_of_finrank_eq f ℚ d hd c.val
  rw [h, map_nsmul]

end

end HodgeConjecture.SchemeCycles
