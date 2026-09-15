import HodgeConjecture.Cycles.IntegralDimension
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.NoetherNormalization

/-!
# The dimension lower bound from Noether normalization

An actual injective integral polynomial normalization has as many variables
as the transcendence degree of its domain. Integral dimension invariance and
the proved polynomial lower bound then give the lower dimension bound for
every finite-type domain over a field.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
  [Algebra k A]

/-- The size of an actual polynomial normalization is the transcendence degree. -/
theorem trdeg_eq_normalization_size (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    Algebra.trdeg k A = s := by
  algebraize [g.toRingHom]
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  letI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have ht := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero,
    MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff] using ht.symm

omit [IsDomain A] in
/-- The proved polynomial lower bound passes through an actual normalization map. -/
theorem normalization_size_le_ringKrullDim (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    (s : WithBot ℕ∞) ≤ ringKrullDim A := by
  algebraize [g.toRingHom]
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  rw [← ringKrullDim_eq_of_injective_integral (MvPolynomial (Fin s) k) A hinj]
  simpa using
    (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := k) (Fin s))

/-- Noether normalization supplies the transcendence-degree lower bound. -/
theorem trdeg_toNat_le_ringKrullDim_of_finiteType [Algebra.FiniteType k A] :
    ((Algebra.trdeg k A).toNat : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [trdeg_eq_normalization_size k A s g hinj hint]
  simpa using normalization_size_le_ringKrullDim k A s g hinj hint

end

end HodgeConjecture.SchemeCycles
