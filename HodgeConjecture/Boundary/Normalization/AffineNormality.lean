import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Affine normality from actual local rings

On a nonempty affine open of an integral scheme, integral closedness of the
actual local rings implies integral closedness of the section ring.  The local
normality input is explicit; this module does not derive it from smoothness.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

open AlgebraicGeometry

universe u

/-- The section ring of a nonempty affine open is integrally closed if the
actual local rings at its points are integrally closed. -/
theorem affineSections_isIntegrallyClosed_of_stalks
    {Y : Scheme.{u}} [IsIntegral Y] {V : Y.Opens} [Nonempty V]
    (hV : IsAffineOpen V)
    (hNormal : ∀ y : V, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    IsIntegrallyClosed Γ(Y, V) := by
  letI (y : PrimeSpectrum Γ(Y, V)) :
      Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec.base y)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf
      ⟨hV.fromSpec.base y, (hV.isoSpec.inv.base y).2⟩
  letI hLocalization : ∀ (P : Ideal Γ(Y, V)) [hP : P.IsMaximal],
      IsLocalization.AtPrime
        (Y.presheaf.stalk (hV.fromSpec.base ⟨P, hP.isPrime⟩)) P :=
    fun P hP ↦ hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hV.isoSpec.inv.base _).2
  exact @IsIntegrallyClosed.of_isLocalization_maximal Γ(Y, V) _
    (fun P hP ↦ Y.presheaf.stalk (hV.fromSpec.base ⟨P, hP.isPrime⟩))
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    hLocalization inferInstance
    (fun P hP ↦ hNormal
      ⟨hV.fromSpec.base ⟨P, hP.isPrime⟩, (hV.isoSpec.inv.base _).2⟩)

end HodgeConjecture.NormalizationInertia
