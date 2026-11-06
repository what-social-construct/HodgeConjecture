module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Polynomial.Quotient

@[expose] public section

/-!
# Prime height under extension to a polynomial ring

Extension along the actual constant-polynomial homomorphism embeds the
prime spectrum, since contraction recovers the original ideal. It
therefore does not decrease prime height.

An extended ideal is never maximal: its quotient is the polynomial ring
over the original quotient, and a polynomial ring is not a field.
Consequently the extension of the contraction of any maximal ideal is
strictly smaller than that maximal ideal. This gives one additional
prime-height step, without Jacobson, Noetherian, or domain assumptions.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open Polynomial

noncomputable section

universe u

variable (R : Type u) [CommRing R]

/-- Extending an ideal by constant polynomials and contracting recovers that ideal. -/
@[simp]
theorem polynomial_comap_map_C (p : Ideal R) :
    (p.map (C : R →+* Polynomial R)).comap C = p := by
  ext r
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa only [coeff_C_zero] using h 0
  · intro hr n
    cases n with
    | zero => simpa only [coeff_C_zero] using hr
    | succ n => simp only [coeff_C_ne_zero (Nat.succ_ne_zero n), Ideal.zero_mem]

/-- The actual prime extension map is an order embedding. -/
def polynomialPrimeExtension : PrimeSpectrum R ↪o PrimeSpectrum (Polynomial R) where
  toFun p := ⟨p.asIdeal.map C, inferInstance⟩
  inj' := by
    intro p q hpq
    apply PrimeSpectrum.ext
    have h := congrArg (fun t : PrimeSpectrum (Polynomial R) ↦ t.asIdeal.comap C) hpq
    simpa only [polynomial_comap_map_C] using h
  map_rel_iff' := by
    intro p q
    change p.asIdeal.map C ≤ q.asIdeal.map C ↔ p.asIdeal ≤ q.asIdeal
    constructor
    · intro h
      have hc := Ideal.comap_mono (f := (C : R →+* Polynomial R)) h
      simpa only [polynomial_comap_map_C] using hc
    · exact Ideal.map_mono

/-- Every prime chain below the original prime extends below the extended prime. -/
theorem polynomialPrimeExtension_height_le (p : PrimeSpectrum R) :
    Order.height p ≤ Order.height (polynomialPrimeExtension R p) :=
  Order.height_le_height_apply_of_strictMono
    (polynomialPrimeExtension R) (polynomialPrimeExtension R).strictMono p

/-- No ideal extended from the coefficient ring is maximal in the polynomial ring. -/
theorem polynomial_map_C_not_isMaximal (p : Ideal R) :
    ¬ (p.map (C : R →+* Polynomial R)).IsMaximal := by
  intro hp
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hp
  exact Ideal.polynomial_not_isField _
    (MulEquiv.isField hfield p.polynomialQuotientEquivQuotientPolynomial.toMulEquiv)

/-- The actual extension of a maximal ideal's contraction lies strictly below it. -/
theorem polynomial_map_comap_C_lt (m : Ideal (Polynomial R)) [m.IsMaximal] :
    (m.comap C).map (C : R →+* Polynomial R) < m := by
  refine lt_of_le_of_ne Ideal.map_comap_le ?_
  intro h
  apply polynomial_map_C_not_isMaximal R (m.comap C)
  rw [h]
  infer_instance

/-- There is at least one extra prime-height step above the coefficient contraction. -/
theorem polynomial_primeHeight_comap_add_one_le
    (m : Ideal (Polynomial R)) [m.IsMaximal] :
    (m.comap (C : R →+* Polynomial R)).height + 1 ≤ m.height := by
  letI : ((m.comap C).map (C : R →+* Polynomial R)).IsPrime :=
    inferInstance
  have he (p : PrimeSpectrum R) :
      (polynomialPrimeExtension R p).asIdeal = Ideal.map C p.asIdeal := rfl
  have hheight : (m.comap (C : R →+* Polynomial R)).height ≤
      ((m.comap C).map (C : R →+* Polynomial R)).height :=
    by simpa only [← PrimeSpectrum.height_eq_orderHeight, he] using
      polynomialPrimeExtension_height_le R ⟨m.comap C, inferInstance⟩
  exact (add_le_add_left hheight 1).trans
    (Ideal.height_add_one_le_of_lt_of_isPrime (polynomial_map_comap_C_lt R m))

end

end HodgeConjecture.SchemeCycles
