import HodgeConjecture.Cycles.OpenRestriction
import HodgeConjecture.Cycles.ClosedImmersionPushforward

/-!
# Cycle transport through actual scheme isomorphisms

Actual ideal images along a scheme isomorphism and its inverse give
inverse maps on integral closed supports. The existing closed-immersion
pushforward therefore preserves each coefficient at its actual image.

Inverse image of an ideal through an isomorphism equals its image through
the inverse. Consequently the existing open restriction agrees with the
existing closed-immersion pushforward along the inverse. This compares
the two geometric cycle operations, without a new cycle type or quotient.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}}

/-- A scheme isomorphism identifies actual integral supports by the
existing ideal-sheaf image, with inverse the image under its inverse. -/
def closedImageSubschemeEquiv (e : X ≅ Y) :
    IntegralClosedSubscheme X ≃ IntegralClosedSubscheme Y where
  toFun Z := closedImageSubscheme e.hom Z
  invFun W := closedImageSubscheme e.inv W
  left_inv Z := by
    apply Subtype.ext
    change (Z.val.map e.hom).map e.inv = Z.val
    rw [← Scheme.IdealSheafData.map_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.map_id]
  right_inv W := by
    apply Subtype.ext
    change (W.val.map e.inv).map e.hom = W.val
    rw [← Scheme.IdealSheafData.map_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.map_id]

@[simp]
theorem closedImageSubschemeEquiv_apply (e : X ≅ Y) (Z : IntegralClosedSubscheme X) :
    closedImageSubschemeEquiv e Z = closedImageSubscheme e.hom Z := rfl

@[simp]
theorem closedImageSubschemeEquiv_symm_apply (e : X ≅ Y) (W : IntegralClosedSubscheme Y) :
    (closedImageSubschemeEquiv e).symm W = closedImageSubscheme e.inv W := rfl

/-- The existing geometric pushforward is coefficient reindexing by its
proved actual support equivalence; it is not redefined by this equation. -/
theorem closedImmersionPushforward_iso_eq_lmapDomain (R : Type v) [Semiring R]
    (e : X ≅ Y) :
    closedImmersionPushforward R e.hom =
      Finsupp.lmapDomain R R (closedImageSubschemeEquiv e) := by
  apply Finsupp.lhom_ext
  intro Z r
  simp [closedImageCycle, fundamentalCycle, Finsupp.smul_single]

/-- Pushforward along a scheme isomorphism preserves the coefficient of
each integral support at its actual ideal-sheaf image. -/
theorem closedImmersionPushforward_iso_apply_image (R : Type v) [Semiring R]
    (e : X ≅ Y) (c : Cycles X R) (Z : IntegralClosedSubscheme X) :
    closedImmersionPushforward R e.hom c (closedImageSubscheme e.hom Z) = c Z := by
  rw [closedImmersionPushforward_iso_eq_lmapDomain, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply (closedImageSubschemeEquiv e).injective c Z

/-- At an arbitrary target support, pushforward reads the coefficient of
its actual image under the inverse scheme isomorphism. -/
theorem closedImmersionPushforward_iso_apply (R : Type v) [Semiring R]
    (e : X ≅ Y) (c : Cycles X R) (W : IntegralClosedSubscheme Y) :
    closedImmersionPushforward R e.hom c W = c (closedImageSubscheme e.inv W) := by
  rw [closedImmersionPushforward_iso_eq_lmapDomain, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_equiv_apply c W

/-- Ideal pullback through an isomorphism is ideal image through its inverse. -/
theorem ideal_comap_iso_eq_map_inv (e : X ≅ Y) (I : Y.IdealSheafData) :
    I.comap e.hom = I.map e.inv := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le,
      ← Scheme.IdealSheafData.comap_comp]
    simp
  · have h := Scheme.IdealSheafData.map_mono e.inv (I.le_map_comap e.hom)
    simpa only [← Scheme.IdealSheafData.map_comp, Iso.hom_inv_id,
      Scheme.IdealSheafData.map_id] using h

/-- The two existing geometric cycle operations coincide for inverse isomorphisms. -/
theorem openRestriction_iso_eq_pushforward_inv (R : Type v) [Semiring R]
    (e : X ≅ Y) :
    openRestriction R e.hom = closedImmersionPushforward R e.inv := by
  apply Finsupp.lhom_ext
  intro Z r
  rw [openRestriction_single, closedImmersionPushforward_single]
  congr 1
  rw [← openRestriction_fundamentalCycle]
  exact openRestriction_fundamentalCycle_of_comap_eq e.hom R Z
    (closedImageSubscheme e.inv Z) (ideal_comap_iso_eq_map_inv e Z.val)

/-- Closed pushforward commutes with pullback through compatible actual
automorphisms, on the entire finite-cycle module. -/
theorem pushforward_openRestriction_iso (R : Type v) [Semiring R]
    (f : X ⟶ Y) [IsClosedImmersion f] (eX : X ≅ X) (eY : Y ≅ Y)
    (h : eX.hom ≫ f = f ≫ eY.hom) :
    (closedImmersionPushforward R f).comp (openRestriction R eX.hom) =
      (openRestriction R eY.hom).comp (closedImmersionPushforward R f) := by
  rw [openRestriction_iso_eq_pushforward_inv, openRestriction_iso_eq_pushforward_inv,
    closedImmersionPushforward_comp, closedImmersionPushforward_comp]
  congr 1
  apply (cancel_epi eX.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end HodgeConjecture.SchemeCycles
