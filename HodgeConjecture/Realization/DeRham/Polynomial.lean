module

public import HodgeConjecture.Realization.DeRham.AffineDegreeZero
public import Mathlib.RingTheory.Kaehler.Polynomial

@[expose] public section

/-!
# Degree-zero de Rham cohomology of polynomial algebras

Adjoining a polynomial variable preserves the actual universal-derivation
kernel when the coefficient ring has no additive torsion. The maps are the
original constant inclusion and evaluation at zero. This is a degree-zero
calculation, not a comparison with singular cohomology or a statement about
higher de Rham cohomology.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open CategoryTheory KaehlerDifferential
open scoped Polynomial

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- Forgetting differentials of coefficients detects the usual polynomial derivative. -/
theorem derivative_eq_zero_of_closed {p : A[X]} (hp : D k A[X] p = 0) :
    Polynomial.derivative p = 0 := by
  have h := congrArg (KaehlerDifferential.map k A A[X] A[X]) hp
  have h' : D A A[X] p = 0 := by simpa only [map_D, map_zero, Algebra.algebraMap_self,
    RingHom.id_apply] using h
  have h'' := congrArg (KaehlerDifferential.polynomialEquiv A) h'
  simpa only [polynomialEquiv_D, map_zero] using h''

/-- A constant polynomial is closed exactly when its original coefficient is closed. -/
theorem closed_C_iff (a : A) : D k A[X] (Polynomial.C a) = 0 ↔ D k A a = 0 := by
  constructor
  · intro h
    have h' := map_closed k (Polynomial.aevalTower (AlgHom.id k A) (0 : A)) h
    simpa only [Polynomial.aevalTower_C, AlgHom.id_apply] using h'
  · exact map_closed k (IsScalarTower.toAlgHom k A A[X])

variable [HasUniqueDiv A]

/-- A closed polynomial has no nonconstant coefficients. -/
theorem eq_C_of_closed {p : A[X]} (hp : D k A[X] p = 0) :
    p = Polynomial.C (p.coeff 0) :=
  Polynomial.eq_C_of_derivative_eq_zero (derivative_eq_zero_of_closed k A hp)

/-- Closed polynomial functions are exactly the constant polynomials with closed coefficient. -/
theorem closed_polynomial_iff (p : A[X]) :
    D k A[X] p = 0 ↔ p = Polynomial.C (p.coeff 0) ∧ D k A (p.coeff 0) = 0 := by
  constructor
  · intro hp
    have hc := eq_C_of_closed k A hp
    exact ⟨hc, (closed_C_iff k A _).mp (hc ▸ hp)⟩
  · rintro ⟨hp, hc⟩
    rw [hp]
    exact (closed_C_iff k A _).mpr hc

/-- Evaluation at zero identifies degree-zero cohomology before and after adjoining a variable. -/
def polynomialCoordinates : H0 k A[X] ≃ₐ[k] H0 k A :=
  AlgEquiv.ofAlgHom
    (map k (Polynomial.aevalTower (AlgHom.id k A) (0 : A)))
    (map k (IsScalarTower.toAlgHom k A A[X]))
    (by
      apply AlgHom.ext
      intro a
      apply Subtype.ext
      change Polynomial.aevalTower (AlgHom.id k A) (0 : A) (Polynomial.C a.val) = a.val
      simp)
    (by
      apply AlgHom.ext
      intro p
      apply Subtype.ext
      change Polynomial.C (Polynomial.aeval (0 : A) p.val) = p.val
      rw [← Polynomial.coeff_zero_eq_aeval_zero]
      exact (eq_C_of_closed k A p.property).symm)

@[simp]
theorem polynomialCoordinates_symm_coe (a : H0 k A) :
    ((polynomialCoordinates k A).symm a).val = Polynomial.C a.val := rfl

/-- The calculation identifies homology of the original constructed complexes. -/
def polynomialCohomologyZeroIso :
    (deRhamComplex k A[X]).homology 0 ≅ (deRhamComplex k A).homology 0 :=
  cohomologyZeroIso k A[X] ≪≫ (polynomialCoordinates k A).toLinearEquiv.toModuleIso ≪≫
    (cohomologyZeroIso k A).symm

/-- Every evaluation agrees on closed polynomial functions. -/
theorem eval_closed (p : H0 k A[X]) (a : A) :
    Polynomial.aevalTower (AlgHom.id k A) a p.val =
      (polynomialCoordinates k A p).val := by
  change Polynomial.aevalTower (AlgHom.id k A) a p.val =
    Polynomial.aevalTower (AlgHom.id k A) 0 p.val
  rw [eq_C_of_closed k A p.property]
  simp

/-- The affine line has exactly the constants as closed functions over a torsion-free base. -/
def affineLineCoordinates (k : Type u) [CommRing k] [HasUniqueDiv k] :
    H0 k k[X] ≃ₐ[k] k :=
  (polynomialCoordinates k k).trans (unramifiedCoordinates k k)

@[simp]
theorem affineLineCoordinates_symm_coe [HasUniqueDiv k] (a : k) :
    ((affineLineCoordinates k).symm a).val = Polynomial.C a := rfl

end

end HodgeConjecture.AffineDeRham
