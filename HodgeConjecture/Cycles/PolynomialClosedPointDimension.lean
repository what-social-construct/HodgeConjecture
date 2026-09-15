import HodgeConjecture.Cycles.PolynomialMaximalHeight
import HodgeConjecture.Cycles.SupportCodimension

/-!
# Actual local dimensions at closed points of affine space

The stalk of the actual polynomial spectrum is a localization at the
point's prime ideal. The maximal-height theorem therefore computes every
closed-point stalk dimension. In the scheme's closure-inclusion order
this is point coheight, not point height.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The actual structure-sheaf stalk at a polynomial maximal point has
dimension equal to the number of variables. -/
theorem mvPolynomial_stalk_dimension_of_isMaximal
    (k : Type u) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk p) =
      (n : WithBot ℕ∞) := by
  change ringKrullDim ((AlgebraicGeometry.Spec.structureSheaf
    (MvPolynomial (Fin n) k)).presheaf.stalk p) = (n : WithBot ℕ∞)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal,
    mvPolynomial_height_eq_card_of_isMaximal k n p.asIdeal]
  rfl

/-- Closedness alone supplies the maximal-ideal input for the actual
affine-space stalk calculation. -/
theorem mvPolynomial_stalk_dimension_of_isClosed
    (k : Type u) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hp : IsClosed ({p} : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))) :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk p) =
      (n : WithBot ℕ∞) := by
  letI := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp
  exact mvPolynomial_stalk_dimension_of_isMaximal k n p

/-- Closed-point coheight in the actual scheme order equals the number
of variables. Its closed-carrier dimension is a different quantity. -/
theorem mvPolynomial_closedPoint_coheight
    (k : Type u) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hp : IsClosed ({p} : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))) :
    Order.coheight (α := (Spec (CommRingCat.of (MvPolynomial (Fin n) k)) : Scheme)) p =
      (n : ℕ∞) := by
  apply WithBot.coe_injective
  exact (point_coheight_eq_stalkDim (Spec (CommRingCat.of (MvPolynomial (Fin n) k))) p).trans
    (mvPolynomial_stalk_dimension_of_isClosed k n p hp)

end

end HodgeConjecture.SchemeCycles
