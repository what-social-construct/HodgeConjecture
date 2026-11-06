module

public import HodgeConjecture.Cycles.FiniteFlatChowDegree
public import HodgeConjecture.Realization.Chow.TransferProjector

@[expose] public section

/-! Positive geometric rank supplies the existing rational transfer structure
using the actual Chow maps and their proved degree law. -/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory SchemeCycles

noncomputable section

universe u

/-- An actual finite flat map of positive constant geometric rank instantiates the
existing transfer interface on the existing rational Chow groups. -/
def finiteFlatChowTransfer
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hrank : ∀ y : Y, f.finrank y = d) :
    RationalDegreeTransfer
      (RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n)
      (RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) where
  pull := rationalChowFiniteFlatPullback k pY f n
  push := rationalChowFinitePushforward k pY f n
  degree := d
  degree_ne_zero := hd
  push_comp_pull := by
    apply LinearMap.ext
    intro c
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Nat.cast_smul_eq_nsmul] using
      rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq k pY f n d hrank c

/-- Positive geometric rank makes the actual rational Chow pullback injective. -/
theorem rationalChowFiniteFlatPullback_injective
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hrank : ∀ y : Y, f.finrank y = d) :
    Function.Injective (rationalChowFiniteFlatPullback k pY f n) :=
  (finiteFlatChowTransfer k pY f n d hd hrank).pull_injective

/-- The existing normalized projector is now instantiated by actual Chow operations. -/
theorem finiteFlatChow_normalizedProjector_isIdempotent
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hrank : ∀ y : Y, f.finrank y = d) :
    IsIdempotentElem ((d : ℚ)⁻¹ •
      (rationalChowFiniteFlatPullback k pY f n).comp
        (rationalChowFinitePushforward k pY f n)) :=
  (finiteFlatChowTransfer k pY f n d hd hrank).normalizedProjector_isIdempotent

end

end HodgeConjecture
