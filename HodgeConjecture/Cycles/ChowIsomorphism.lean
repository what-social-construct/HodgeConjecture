module

public import HodgeConjecture.Cycles.ChowPushforward

@[expose] public section

/-!
# Actual scheme isomorphisms on the principal-relation quotient

The existing closed pushforward and inverse open restriction give inverse
maps of homogeneous cycles. Both maps preserve the actual principal
relations by the proved closed-image transport. They therefore induce an
equivalence of the constructed Chow groups. No injectivity on Chow is
claimed for a general closed immersion.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

theorem iso_inverse_supportDegree {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (e : X ≅ Y) (W : IntegralClosedSubscheme Y) :
    supportDegree (δ.comapClosedImmersion e.hom) (closedImageSubscheme e.inv W) =
      supportDegree δ W := by
  rw [supportDegree_comapClosedImmersion]
  have h : closedImageSubscheme e.hom (closedImageSubscheme e.inv W) = W :=
    (closedImageSubschemeEquiv e).apply_symm_apply W
  rw [h]

/-- Isomorphism pushforward on the existing homogeneous cycles, with
inverse the existing closed pushforward along the inverse isomorphism. -/
def gradedIsoEquiv {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    cyclesOfDegree ℤ (δ.comapClosedImmersion e.hom) n ≃ₗ[ℤ] cyclesOfDegree ℤ δ n :=
  { gradedClosedImmersionPushforward (δ.comapClosedImmersion e.hom) δ e.hom
      (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n with
    invFun := gradedClosedImmersionPushforward δ (δ.comapClosedImmersion e.hom) e.inv
      (iso_inverse_supportDegree δ e) n
    left_inv := by
      intro c
      apply Subtype.ext
      change ((closedImmersionPushforward ℤ e.inv).comp
        (closedImmersionPushforward ℤ e.hom)) c.val = c.val
      rw [closedImmersionPushforward_comp]
      simp only [Iso.hom_inv_id, closedImmersionPushforward_id, LinearMap.id_apply]
    right_inv := by
      intro c
      apply Subtype.ext
      change ((closedImmersionPushforward ℤ e.hom).comp
        (closedImmersionPushforward ℤ e.inv)) c.val = c.val
      rw [closedImmersionPushforward_comp]
      simp only [Iso.inv_hom_id, closedImmersionPushforward_id, LinearMap.id_apply] }

@[simp]
theorem gradedIsoEquiv_val {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ (δ.comapClosedImmersion e.hom) n) :
    (gradedIsoEquiv δ e n c).val = closedImmersionPushforward ℤ e.hom c.val := rfl

/-- The inverse graded map is precisely the already-defined geometric
open restriction, not a new pullback operation. -/
theorem gradedIsoEquiv_symm_val {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    ((gradedIsoEquiv δ e n).symm c).val = openRestriction ℤ e.hom c.val := by
  change closedImmersionPushforward ℤ e.inv c.val = openRestriction ℤ e.hom c.val
  rw [openRestriction_iso_eq_pushforward_inv]

/-- Both directions preserve the actual relation submodule, so its
image under the geometric graded isomorphism is exactly the target one. -/
theorem principalRelations_map_gradedIsoEquiv {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    (principalRelations (δ.comapClosedImmersion e.hom) n).map
      (gradedIsoEquiv δ e n).toLinearMap = principalRelations δ n := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    exact principalRelations_le_comap_closedImmersionPushforward
      (δ.comapClosedImmersion e.hom) δ e.hom
      (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n
  · intro c hc
    apply Submodule.mem_map.mpr
    refine ⟨(gradedIsoEquiv δ e n).symm c, ?_, (gradedIsoEquiv δ e n).apply_symm_apply c⟩
    exact principalRelations_le_comap_closedImmersionPushforward
      δ (δ.comapClosedImmersion e.hom) e.inv (iso_inverse_supportDegree δ e) n hc

/-- The actual homogeneous-cycle isomorphism descends to the quotient by
the actual principal relations. -/
def chowIsoEquiv {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    ChowGroup (δ.comapClosedImmersion e.hom) n ≃ₗ[ℤ] ChowGroup δ n :=
  Submodule.Quotient.equiv (principalRelations (δ.comapClosedImmersion e.hom) n)
    (principalRelations δ n) (gradedIsoEquiv δ e n)
    (principalRelations_map_gradedIsoEquiv δ e n)

@[simp]
theorem chowIsoEquiv_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ (δ.comapClosedImmersion e.hom) n) :
    chowIsoEquiv δ e n (classMap (δ.comapClosedImmersion e.hom) n c) =
      classMap δ n (gradedIsoEquiv δ e n c) := rfl

/-- On quotient representatives, the inverse is induced by the same
graded inverse whose underlying cycle map is actual open restriction. -/
@[simp]
theorem chowIsoEquiv_symm_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    (chowIsoEquiv δ e n).symm (classMap δ n c) =
      classMap (δ.comapClosedImmersion e.hom) n ((gradedIsoEquiv δ e n).symm c) := rfl

/-- The quotient isomorphism's forward map is the already constructed
closed-immersion quotient pushforward, not an additional assignment. -/
theorem chowIsoEquiv_toLinearMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    (chowIsoEquiv δ e n).toLinearMap =
      chowClosedImmersionPushforward (δ.comapClosedImmersion e.hom) δ e.hom
        (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n := rfl

end

end HodgeConjecture.SchemeCycles
