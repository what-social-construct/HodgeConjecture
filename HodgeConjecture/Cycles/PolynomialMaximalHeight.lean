module

public import HodgeConjecture.Cycles.AffineDimension
public import HodgeConjecture.Cycles.PolynomialPrimeHeight
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

/-!
# Heights of maximal ideals in polynomial algebras over fields

Maximal contraction over a Jacobson ring and the strict prime-extension
step give the lower bound by induction on the variables. The independently
proved sharp polynomial dimension gives the upper bound. Thus every
maximal ideal, not only a rational-point kernel, has the full height.

The actual prime localization has that dimension. This does not assert
regularity, a generator bound, or uniform lengths of saturated chains.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u

/-- Every maximal ideal of a polynomial algebra over a field has the
full height, including the zero-variable case. -/
theorem mvPolynomial_primeHeight_eq_card_of_isMaximal
    (k : Type u) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      apply le_antisymm _ zero_le
      apply WithBot.coe_le_coe.mp
      exact (Ideal.height_le_ringKrullDim_of_isPrime (I := m)).trans
        (mvPolynomial_ringKrullDim_eq_card k 0).le
  | succ n ih =>
      have hupper : m.height ≤ ((n + 1 : ℕ) : ℕ∞) := by
        apply WithBot.coe_le_coe.mp
        exact (Ideal.height_le_ringKrullDim_of_isPrime (I := m)).trans
          (mvPolynomial_ringKrullDim_eq_card k (n + 1)).le
      apply le_antisymm hupper
      let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
      let M : Ideal (Polynomial (MvPolynomial (Fin n) k)) := m.comap e.symm
      letI : M.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) k) := M.comap Polynomial.C
      letI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
      have hp : p.height = (n : ℕ∞) := ih p
      have hM : M.height = m.height := by
        skip
        exact e.symm.height_comap m
      have hstep := polynomial_primeHeight_comap_add_one_le
        (MvPolynomial (Fin n) k) M
      change p.height + 1 ≤ M.height at hstep
      simpa only [hp, hM, Nat.cast_add, Nat.cast_one] using hstep

/-- The ordinary ideal-height interface gives the same maximal height. -/
theorem mvPolynomial_height_eq_card_of_isMaximal
    (k : Type u) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : m.height = (n : ℕ∞) := by
  rw [mvPolynomial_primeHeight_eq_card_of_isMaximal k n m]

/-- The actual localization at every polynomial maximal ideal has the
full dimension; no residue-field degree-one assumption is made. -/
theorem mvPolynomial_localization_dimension_of_isMaximal
    (k : Type u) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m,
    mvPolynomial_height_eq_card_of_isMaximal k n m]
  rfl

end

end HodgeConjecture.SchemeCycles
