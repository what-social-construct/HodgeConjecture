module

public import HodgeConjecture.Realization.DeRham.AffineFormsSheaf
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

/-!
# Actual differential sheaves on the Laurent overlap

The overlap algebra is the original localization of `k[X]` at `X`.
Its principal ideal property follows from the localization ideal theorem.
The existing Euler coordinates are normalized by the actual inverse of
the coordinate unit, so `d T` has coordinate one. The canonical affine
sheafification-unit theorem then applies to this actual overlap scheme.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace KaehlerDifferential

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The original Laurent localization is a principal ideal ring. -/
instance laurentPrincipalIdealRing : IsPrincipalIdealRing (LaurentPolynomial k) where
  principal I := by
    rw [← IsLocalization.map_under (.powers (Polynomial.X : Polynomial k))
      (LaurentPolynomial k) I]
    exact Submodule.IsPrincipal.map_ringHom _ inferInstance

/-- Actual Laurent differential coordinates normalized on `d T`. -/
def laurentOrdinaryKaehlerCoordinates :
    Ω[LaurentPolynomial k⁄k] ≃ₗ[LaurentPolynomial k] LaurentPolynomial k :=
  (LaurentDeRham.kaehlerCoordinates k).trans
    (LinearEquiv.smulOfUnit (M := LaurentPolynomial k) ((LaurentDeRham.variableUnit k)⁻¹))

theorem laurentOrdinaryKaehlerCoordinates_D_T :
    laurentOrdinaryKaehlerCoordinates k
      (D k (LaurentPolynomial k) (LaurentPolynomial.T 1)) = 1 := by
  change LaurentPolynomial.T (-1) *
    (LaurentDeRham.eulerDerivation k).liftKaehlerDifferential
      (D k (LaurentPolynomial k) (LaurentPolynomial.T 1)) = 1
  rw [Derivation.liftKaehlerDifferential_comp_D, LaurentDeRham.eulerDerivation_T,
    one_zsmul, ← LaurentPolynomial.T_add]
  norm_num

/-- All actual sectionwise forms on the overlap already satisfy the sheaf condition. -/
theorem laurentFormsPresheaf_isSheaf (n : ℕ) :
    (formsPresheaf k (Spec (.of (LaurentPolynomial k)))
      (affineStructureMorphism k (LaurentPolynomial k)) n).IsSheaf :=
  affineFormsPresheaf_isSheaf k (LaurentPolynomial k)
    (laurentOrdinaryKaehlerCoordinates k) (LaurentPolynomial.T 1)
    (laurentOrdinaryKaehlerCoordinates_D_T k) n

/-- The canonical unit identifies every degree of the overlap forms with its actual sheaf. -/
theorem laurentFormsSheafUnit_isIso (n : ℕ) :
    IsIso (CategoryTheory.toSheafify
      (Opens.grothendieckTopology (Spec (.of (LaurentPolynomial k))))
      (formsPresheaf k (Spec (.of (LaurentPolynomial k)))
        (affineStructureMorphism k (LaurentPolynomial k)) n)) :=
  affineFormsSheafUnit_isIso k (LaurentPolynomial k)
    (laurentOrdinaryKaehlerCoordinates k) (LaurentPolynomial.T 1)
    (laurentOrdinaryKaehlerCoordinates_D_T k) n

end

end HodgeConjecture.SchemeDeRham
