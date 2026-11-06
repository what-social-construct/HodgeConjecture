module

public import HodgeConjecture.Cycles.TranscendenceDegreeDrop
public import HodgeConjecture.Cycles.NormalizationDimension
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

/-!
# Affine dimension and transcendence degree

The fraction-field comparison retains the actual algebra maps and scalar
tower. The finite-type dimension calculation below concerns genuine prime
chains; no unit-step specialization law is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

/-- Passing from a domain to its actual fraction field preserves
transcendence degree over the base field. -/
theorem trdeg_eq_of_isFractionRing (k : Type u) [Field k]
    (A K : Type v) [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K]
    [IsFractionRing A K] : Algebra.trdeg k A = Algebra.trdeg k K := by
  letI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  simpa only [trdeg_eq_zero, add_zero] using trdeg_add_eq (A := K) k A

/-- In particular, the canonical fraction ring gives the same invariant. -/
theorem trdeg_eq_fractionRing (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] :
    Algebra.trdeg k A = Algebra.trdeg k (FractionRing A) :=
  trdeg_eq_of_isFractionRing k A (FractionRing A)

private theorem krullDim_le_of_strictAnti_nat {α : Type*} [Preorder α]
    (f : α → ℕ) (hf : StrictAnti f) (n : ℕ) (hn : ∀ x, f x ≤ n) :
    Order.krullDim α ≤ (n : WithBot ℕ∞) := by
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  have hx := Order.height_le_height_apply_of_strictMono
    (fun y : αᵒᵈ ↦ f y) (fun _ _ h ↦ hf h) x
  rw [Order.height_nat] at hx
  exact (WithBot.coe_le_coe.mpr hx).trans (by exact_mod_cast hn x)

/-- A prime chain strictly lowers finite transcendence degree at each
step, giving the sharp upper bound even for a reducible algebra. -/
theorem ringKrullDim_le_trdeg_toNat_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A ≤ ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  apply krullDim_le_of_strictAnti_nat
    (fun p : PrimeSpectrum A ↦ (Algebra.trdeg k (A ⧸ p.asIdeal)).toNat)
    (primeQuotient_trdeg_toNat_strictAnti k A)
  intro p
  exact Cardinal.toNat_le_toNat
    (trdeg_le_of_surjective (Ideal.Quotient.mkₐ k p.asIdeal) Ideal.Quotient.mk_surjective)
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := A))

/-- The actual Krull dimension of a finite-type domain is its finite
transcendence degree. The two bounds are proved independently. -/
theorem ringKrullDim_eq_trdeg_toNat_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) :=
  le_antisymm (ringKrullDim_le_trdeg_toNat_of_finiteType k A)
    (trdeg_toNat_le_ringKrullDim_of_finiteType k A)

/-- The same equality with the actual fraction field, as in the classical
finite-type domain dimension statement. -/
theorem ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k (FractionRing A)).toNat : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_trdeg_toNat_of_finiteType k A, ← trdeg_eq_fractionRing k A]

/-- The sharp polynomial dimension formula over a field follows from the
proved transcendence-degree calculation, without using an unproved formula. -/
theorem mvPolynomial_ringKrullDim_eq_card (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_trdeg_toNat_of_finiteType k (MvPolynomial (Fin n) k),
    MvPolynomial.trdeg_of_isDomain]
  simp

/-- The dimension formula concerns the topology of the actual affine scheme. -/
theorem spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of A)) =
      ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum A) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_eq_trdeg_toNat_of_finiteType k A

end

end HodgeConjecture.SchemeCycles
