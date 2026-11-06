module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Length

@[expose] public section

/-!
# Localization of principal quotients

The canonical comparison `S⁻¹(B/(b)) ≃ S⁻¹B/(b/1)`, linear over the
actual localized ring, with its representative formula and length equality.
This is the principal-ideal specialization of Stacks Project, Tag 02C8:
https://stacks.math.columbia.edu/tag/02C8

The proof reuses Mathlib's `IsLocalizedModule.toLocalizedQuotient'` and
`Submodule.localized'_span`. No Noetherian, domain, normality, nonzero-element
or nonzero-denominator-submonoid hypothesis is needed for this comparison.
-/

set_option autoImplicit false
namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (B : Type*) [CommRing B] (S : Submonoid B)

/-- Localizing the actual principal quotient is canonically the principal quotient
of the localized ring, as a module over that ring. -/
def localizedPrincipalQuotientEquiv (b : B) :
    LocalizedModule S (B ⧸ Ideal.span {b}) ≃ₗ[Localization S]
      (Localization S ⧸ Ideal.span {algebraMap B (Localization S) b}) := by
  let I : Ideal B := Ideal.span {b}
  let f := I.toLocalizedQuotient' (Localization S) S (Algebra.linearMap B (Localization S))
  let e := (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (B ⧸ I)) f).extendScalarsOfIsLocalization
    S (Localization S)
  have h : I.localized' (Localization S) S (Algebra.linearMap B (Localization S)) =
      Ideal.span {algebraMap B (Localization S) b} := by
    change (Submodule.span B {b}).localized' (Localization S) S
      (Algebra.linearMap B (Localization S)) = _
    rw [Submodule.localized'_span]
    simp
  exact e.trans (Submodule.quotEquivOfEq _ _ h)

/-- The comparison sends the class of `x/1` to the class of its actual localization image. -/
@[simp]
theorem localizedPrincipalQuotientEquiv_mk (b x : B) :
    localizedPrincipalQuotientEquiv B S b
      (LocalizedModule.mkLinearMap S (B ⧸ Ideal.span {b}) (Ideal.Quotient.mk _ x)) =
        Ideal.Quotient.mk _ (algebraMap B (Localization S) x) := by
  simp only [localizedPrincipalQuotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.extendScalarsOfIsLocalization_apply, IsLocalizedModule.linearEquiv_apply]
  rfl

/-- On an arbitrary fraction, the comparison sends `[x]/s` to `[x/s]`. -/
theorem localizedPrincipalQuotientEquiv_fraction (b x : B) (s : S) :
    localizedPrincipalQuotientEquiv B S b
      (LocalizedModule.mk (Ideal.Quotient.mk (Ideal.span {b}) x) s) =
        Ideal.Quotient.mk _ (IsLocalization.mk' (Localization S) x s) := by
  have h : LocalizedModule.mk (Ideal.Quotient.mk (Ideal.span {b}) x) s =
      IsLocalization.mk' (Localization S) 1 s •
        LocalizedModule.mkLinearMap S (B ⧸ Ideal.span {b}) (Ideal.Quotient.mk _ x) := by
    change _ = IsLocalization.mk' (Localization S) 1 s • LocalizedModule.mk _ 1
    simp only [IsLocalizedModule.mk_eq_mk']
    rw [IsLocalizedModule.mk'_smul_mk' (Localization S), one_smul, mul_one]
  rw [h, map_smul, localizedPrincipalQuotientEquiv_mk]
  change Ideal.Quotient.mk _ (IsLocalization.mk' (Localization S) 1 s *
    algebraMap B (Localization S) x) = _
  rw [mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

/-- Length is preserved by the canonical principal-quotient comparison. -/
theorem length_localized_principalQuotient (b : B) :
    Module.length (Localization S) (LocalizedModule S (B ⧸ Ideal.span {b})) =
      Module.length (Localization S)
        (Localization S ⧸ Ideal.span {algebraMap B (Localization S) b}) :=
  (localizedPrincipalQuotientEquiv B S b).length_eq

/-- A principal quotient vanishes after its generator is inverted. -/
theorem length_localized_principalQuotient_eq_zero (b : B) (hb : b ∈ S) :
    Module.length (Localization S) (LocalizedModule S (B ⧸ Ideal.span {b})) = 0 := by
  rw [length_localized_principalQuotient]
  have htop : Ideal.span {algebraMap B (Localization S) b} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (IsLocalization.map_units (Localization S) ⟨b, hb⟩)
  letI : Subsingleton (Localization S ⧸ Ideal.span {algebraMap B (Localization S) b}) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact Module.length_eq_zero

end

end HodgeConjecture.CommutativeAlgebra
