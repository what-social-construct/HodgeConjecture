module

public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

/-!
# Actual affine sections in a specified fraction field

For a nonempty open of `Spec T`, evaluate a section at the generic point
and identify the existing generic stalk with a specified fraction field.
The result is an injective algebra homomorphism for Mathlib's existing
base action on sections. No second field or global algebra instance is
introduced, and neither normality nor Noetherianity is needed.

The image is the actual section subalgebra, with restriction compatibility.
The construction adapts the sibling collision-ideals boundary-section map
to this repository's pinned Mathlib APIs.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {T : CommRingCat.{u}} [IsDomain T]
variable {N : Type v} [Field N] [Algebra T N] [IsFractionRing T N]

/-- The actual generic germ of a section, expressed in the specified
fraction field rather than a newly defined function-field object. -/
def affineSectionsToFractionField
    (U : (Spec T).Opens) [Nonempty U] :
    Γ(Spec T, U) →ₐ[T] N where
  toRingHom :=
    (IsLocalization.algEquiv (nonZeroDivisors T)
      (Spec T).functionField N).toRingHom.comp
        ((Spec T).germToFunctionField U).hom
  commutes' t := by
    change
      (IsLocalization.algEquiv (nonZeroDivisors T)
        (Spec T).functionField N)
        (((Spec T).germToFunctionField U)
          (algebraMap T Γ(Spec T, U) t)) = _
    have h : ((Spec T).germToFunctionField U) (algebraMap T Γ(Spec T, U) t) =
        algebraMap T (Spec T).functionField t :=
      StructureSheaf.algebraMap_germ_apply U _ _ t
    rw [h]
    exact AlgEquiv.commutes _ t

/-- The existing generic germ is injective on every nonempty open of
the integral affine scheme. -/
theorem affineSectionsToFractionField_injective
    (U : (Spec T).Opens) [Nonempty U] :
    Function.Injective (affineSectionsToFractionField (N := N) U) :=
  (IsLocalization.algEquiv (nonZeroDivisors T)
    (Spec T).functionField N).injective.comp
      ((Spec T).germToFunctionField_injective U)

/-- Constants keep their original embedding into the specified fraction field. -/
@[simp]
theorem affineSectionsToFractionField_algebraMap
    (U : (Spec T).Opens) [Nonempty U] (t : T) :
    affineSectionsToFractionField (N := N) U
      (algebraMap T Γ(Spec T, U) t) = algebraMap T N t :=
  (affineSectionsToFractionField U).commutes t

/-- Restricting an actual section does not change its rational function. -/
@[simp]
theorem affineSectionsToFractionField_restrict
    (U V : (Spec T).Opens) [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (s : Γ(Spec T, U)) :
    affineSectionsToFractionField (N := N) V
        ((Spec T).presheaf.map (homOfLE hVU).op s) =
      affineSectionsToFractionField (N := N) U s := by
  change (IsLocalization.algEquiv (nonZeroDivisors T)
    (Spec T).functionField N)
      ((Spec T).germToFunctionField V
        ((Spec T).presheaf.map (homOfLE hVU).op s)) =
    (IsLocalization.algEquiv (nonZeroDivisors T)
      (Spec T).functionField N) ((Spec T).germToFunctionField U s)
  apply congrArg (IsLocalization.algEquiv (nonZeroDivisors T)
    (Spec T).functionField N)
  exact (Spec T).presheaf.germ_res_apply (homOfLE hVU)
    (genericPoint (Spec T)) _ s

/-- The actual sections, as a subalgebra of the specified fraction field. -/
def affineSectionSubalgebra
    (U : (Spec T).Opens) [Nonempty U] : Subalgebra T N :=
  (affineSectionsToFractionField (N := N) U).range

@[simp]
theorem mem_affineSectionSubalgebra_iff
    (U : (Spec T).Opens) [Nonempty U] (z : N) :
    z ∈ affineSectionSubalgebra U ↔
      ∃ s : Γ(Spec T, U), affineSectionsToFractionField U s = z :=
  Iff.rfl

/-- The image presentation keeps the actual section ring, up to its
canonical algebra equivalence onto the image. -/
def affineSectionsEquivSubalgebra
    (U : (Spec T).Opens) [Nonempty U] :
    Γ(Spec T, U) ≃ₐ[T] affineSectionSubalgebra (N := N) U :=
  AlgEquiv.ofInjective (affineSectionsToFractionField U)
    (affineSectionsToFractionField_injective U)

@[simp]
theorem affineSectionsEquivSubalgebra_apply
    (U : (Spec T).Opens) [Nonempty U] (s : Γ(Spec T, U)) :
    (affineSectionsEquivSubalgebra (N := N) U s : N) =
      affineSectionsToFractionField U s := rfl

/-- A smaller nonempty open has a larger section subalgebra in the common
fraction field. This is actual sheaf restriction, not a supplied comparison. -/
theorem affineSectionSubalgebra_anti
    (U V : (Spec T).Opens) [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) :
    affineSectionSubalgebra (N := N) U ≤ affineSectionSubalgebra V := by
  rintro z ⟨s, rfl⟩
  exact ⟨(Spec T).presheaf.map (homOfLE hVU).op s,
    affineSectionsToFractionField_restrict U V hVU s⟩

local instance : Nonempty (⊤ : (Spec T).Opens) :=
  ⟨⟨(⊥ : PrimeSpectrum T), trivial⟩⟩

/-- On the full affine scheme, the section subalgebra is exactly the
embedded base ring. Here `⊥` denotes the base subalgebra, not the zero ring. -/
@[simp]
theorem affineSectionSubalgebra_top :
    affineSectionSubalgebra (T := T) (N := N) ⊤ = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro z ⟨s, rfl⟩
  rw [Algebra.mem_bot]
  refine ⟨(Scheme.ΓSpecIso T).hom s, ?_⟩
  have hs : algebraMap T Γ(Spec T, ⊤)
      ((Scheme.ΓSpecIso T).hom s) = s := by
    change (Scheme.ΓSpecIso T).inv
      ((Scheme.ΓSpecIso T).hom s) = s
    exact Iso.hom_inv_id_apply _ s
  rw [← affineSectionsToFractionField_algebraMap ⊤, hs]
  rfl

end

end HodgeConjecture.NormalizationInertia
