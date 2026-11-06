module

public import HodgeConjecture.Cycles.PolynomialMaximalHeight
public import HodgeConjecture.CommutativeAlgebra.NormalGoingDown
public import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section

/-!
# Local dimensions through actual Noether normalization

Integral incomparability and going-down chain lifting compare the heights
of an actual prime and its contraction. The lower-bound comparison is
reused from the existing normalization spine. The comparison concerns
prime chains; it does not assume that localization at one selected
upstairs prime preserves integrality of the local-ring map.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

/-- Integral incomparability and going down give equality of prime heights.
No finiteness, domain or injectivity assumptions are needed by this comparison. -/
theorem primeHeight_eq_under_of_isIntegral_of_hasGoingDown
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (Q : Ideal S) [Q.IsPrime] : Q.height = (Q.under R).height := by
  apply le_antisymm
  · change (⟨Q, inferInstance⟩ : PrimeSpectrum S).asIdeal.height ≤
      ((PrimeSpectrum.comap (algebraMap R S)) ⟨Q, inferInstance⟩).asIdeal.height
    rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
    exact Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap (algebraMap R S)) (integral_specComap_strictMono R S)
      (⟨Q, inferInstance⟩ : PrimeSpectrum S)
  · exact NormalizationInertia.primeHeight_under_le_of_hasGoingDown Q

private theorem polynomialIntegral_maximal_primeHeight
    (k : Type u) [Field k] (A : Type v) [CommRing A] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.IsIntegral (MvPolynomial (Fin n) k) A]
    [Algebra.HasGoingDown (MvPolynomial (Fin n) k) A]
    (m : Ideal A) [m.IsMaximal] : m.height = (n : ℕ∞) := by
  rw [primeHeight_eq_under_of_isIntegral_of_hasGoingDown (MvPolynomial (Fin n) k) A]
  letI : (m.under (MvPolynomial (Fin n) k)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := MvPolynomial (Fin n) k) m
  exact mvPolynomial_primeHeight_eq_card_of_isMaximal k n _

/-- An actual integral injective polynomial normalization determines the
height of every maximal ideal upstairs. Going down is proved from normality
of the polynomial base, not required as an input. -/
theorem normalization_primeHeight_eq_size
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral)
    (m : Ideal A) [m.IsMaximal] : m.height = (s : ℕ∞) := by
  algebraize [g.toRingHom]
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  letI : Algebra.HasGoingDown (MvPolynomial (Fin s) k) A :=
    CommutativeAlgebra.hasGoingDown_of_isIntegrallyClosed
      (R := MvPolynomial (Fin s) k) (S := A) hinj
  exact polynomialIntegral_maximal_primeHeight k A s m

/-- Every maximal ideal of a finite-type domain has height equal to the
domain's finite transcendence degree. No normality of the domain is assumed. -/
theorem primeHeight_eq_trdeg_toNat_of_isMaximal
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : m.height = ((Algebra.trdeg k A).toNat : ℕ∞) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [trdeg_eq_normalization_size k A s g hinj hint]
  simpa using normalization_primeHeight_eq_size k A s g hinj hint m

/-- The ordinary ideal-height interface for maximal ideals of finite-type domains. -/
theorem height_eq_trdeg_toNat_of_isMaximal
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : m.height = ((Algebra.trdeg k A).toNat : ℕ∞) := by
  rw [primeHeight_eq_trdeg_toNat_of_isMaximal k A m]

/-- The actual local ring at every maximal ideal of a finite-type domain
has the full global dimension. This uses prime heights, not an assertion
that the map between selected localizations is integral. -/
theorem localization_dimension_eq_of_isMaximal
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m,
    height_eq_trdeg_toNat_of_isMaximal k A m,
    ringKrullDim_eq_trdeg_toNat_of_finiteType k A]
  rfl

end

end HodgeConjecture.SchemeCycles
