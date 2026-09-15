import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Finite dimension for finite-type algebras over a field

The proved inequality `dim A[T] ≤ 2 dim A + 1` gives an explicit finite
bound for a polynomial algebra in finitely many variables. A finite-type
algebra is an actual quotient of one of these polynomial algebras, so its
Krull dimension is finite, including when its spectrum is empty.

This module uses no exact polynomial-dimension formula. In particular, it
does not identify dimension with transcendence degree or construct a
dimension function on an arbitrary finite-type scheme.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry

noncomputable section

universe u v

/-- The finite bound obtained by iterating the proved one-variable inequality. -/
def polynomialDimensionBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * polynomialDimensionBound n + 1

/-- A finite polynomial algebra over a field has an explicit finite upper bound. -/
theorem mvPolynomial_ringKrullDim_le_bound (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) ≤ polynomialDimensionBound n := by
  induction n with
  | zero =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0))]
      simp [polynomialDimensionBound]
  | succ n ih =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv k n).toRingEquiv]
      calc
        ringKrullDim (Polynomial (MvPolynomial (Fin n) k)) ≤
            2 * ringKrullDim (MvPolynomial (Fin n) k) + 1 :=
          Polynomial.ringKrullDim_le
        _ ≤ 2 * (polynomialDimensionBound n : WithBot ℕ∞) + 1 := by gcongr
        _ = polynomialDimensionBound (n + 1) := by
          simp [polynomialDimensionBound]

/-- An actual finite polynomial presentation bounds the dimension of its quotient. -/
theorem ringKrullDim_le_bound_of_surjective (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] (n : ℕ)
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    ringKrullDim A ≤ polynomialDimensionBound n :=
  (ringKrullDim_le_of_surjective f.toRingHom hf).trans
    (mvPolynomial_ringKrullDim_le_bound k n)

/-- Finite generation supplies a finite upper bound, without a nontriviality assumption. -/
theorem exists_ringKrullDim_le_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A ≤ n := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  exact ⟨polynomialDimensionBound n, ringKrullDim_le_bound_of_surjective k A n f hf⟩

/-- Every finite-type algebra over a field has Krull dimension strictly below infinity. -/
theorem ringKrullDim_lt_top_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A < ⊤ := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_le_of_finiteType k A
  exact hn.trans_lt (WithBot.coe_lt_coe.mpr (ENat.coe_lt_top n))

/-- The nonempty finite-dimensional-order package additionally requires a nontrivial ring. -/
theorem finiteRingKrullDim_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] :
    FiniteRingKrullDim A := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  exact ⟨ne_bot_of_le_ne_bot (by simp) (ringKrullDim_nonneg_of_nontrivial (R := A)),
    (ringKrullDim_lt_top_of_finiteType k A).ne⟩

/-- The same finite bound concerns the topology of the actual affine scheme. -/
theorem spec_topologicalKrullDim_lt_top_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    topologicalKrullDim (Spec (CommRingCat.of A)) < ⊤ := by
  change topologicalKrullDim (PrimeSpectrum A) < ⊤
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_lt_top_of_finiteType k A

/-- Every actual affine closed subscheme presented by a quotient retains finite dimension. -/
theorem quotientSpec_topologicalKrullDim_lt_top_of_finiteType (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) :
    topologicalKrullDim (Spec (CommRingCat.of (A ⧸ I))) < ⊤ := by
  change topologicalKrullDim (PrimeSpectrum (A ⧸ I)) < ⊤
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (ringKrullDim_quotient_le I).trans_lt (ringKrullDim_lt_top_of_finiteType k A)

/-- Finite generation of an affine scheme's actual global-section algebra is sufficient. -/
theorem affine_topologicalKrullDim_lt_top_of_finiteType (k : Type u) [Field k]
    (X : Scheme.{v}) [IsAffine X] [Algebra k Γ(X, ⊤)] [Algebra.FiniteType k Γ(X, ⊤)] :
    topologicalKrullDim X < ⊤ := by
  rw [(Scheme.homeoOfIso X.isoSpec).isHomeomorph.topologicalKrullDim_eq]
  exact spec_topologicalKrullDim_lt_top_of_finiteType k Γ(X, ⊤)

end

end HodgeConjecture.SchemeCycles
