module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# Residue degrees at actual maximal localizations

The residue field of any localization at a maximal ideal is canonically
the quotient by that ideal. The comparison respects the original base
map, hence identifies the actual residue degree with the quotient-field
weight in Stacks 02MJ and its scheme application 02RT:
https://stacks.math.columbia.edu/tag/02MJ
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (B P : Type*) [CommRing B] [CommRing P] [IsLocalRing P]
  (q : Ideal B) [q.IsMaximal] [Algebra B P] [IsLocalization.AtPrime P q]

/-- The residue field of the actual local ring is the original maximal quotient. -/
def maximalQuotientResidueEquiv : (B ⧸ q) ≃+* IsLocalRing.ResidueField P :=
  (RingEquiv.ofBijective (algebraMap (B ⧸ q) q.ResidueField)
    q.bijective_algebraMap_quotient_residueField).trans
      (IsLocalRing.ResidueField.mapEquiv
        (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) P).toRingEquiv)

/-- The residue comparison sends the class of a section to its actual residue. -/
theorem maximalQuotientResidueEquiv_mk (b : B) :
    maximalQuotientResidueEquiv B P q (Ideal.Quotient.mk q b) =
      IsLocalRing.residue P (algebraMap B P b) := by
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) P
  letI : IsLocalHom e.toRingHom := ⟨fun a ha => by
    have h := ha.map e.symm.toRingHom
    change IsUnit (e.symm (e a)) at h
    simpa only [AlgEquiv.symm_apply_apply] using h⟩
  change IsLocalRing.ResidueField.map
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) P).toRingHom
      (IsLocalRing.residue (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) b)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue P) (e.commutes b)

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R B] [Algebra R P]
  [IsScalarTower R B P] [q.LiesOver (IsLocalRing.maximalIdeal R)]
  [IsLocalHom (algebraMap R P)]

/-- Actual residue-field degrees equal the canonical quotient degrees in the semilocal sum. -/
theorem residueDegree_eq_quotientDegree :
    letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField P) :=
      (IsLocalRing.ResidueField.map (algebraMap R P)).toAlgebra
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField P) =
      Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q) := by
  let eR : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* IsLocalRing.ResidueField R :=
    RingEquiv.refl _
  have hc (a : R ⧸ IsLocalRing.maximalIdeal R) (b : B ⧸ q) :
      (maximalQuotientResidueEquiv B P q).toAddEquiv (a • b) =
        eR a • (maximalQuotientResidueEquiv B P q).toAddEquiv b := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R) a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := q) b
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_mk_of_liesOver,
      ← map_mul, eR, RingEquiv.refl_apply]
    change maximalQuotientResidueEquiv B P q
        (Ideal.Quotient.mk q (algebraMap R B r * s)) =
      IsLocalRing.residue P (algebraMap R P r) *
        maximalQuotientResidueEquiv B P q (Ideal.Quotient.mk q s)
    rw [maximalQuotientResidueEquiv_mk, maximalQuotientResidueEquiv_mk,
      map_mul, map_mul, ← IsScalarTower.algebraMap_apply]
  have h := _root_.lift_rank_eq_of_equiv_equiv eR
    (maximalQuotientResidueEquiv B P q).toAddEquiv eR.bijective hc
  simpa only [Cardinal.toNat_lift, Module.finrank] using
    (congrArg Cardinal.toNat h).symm

end

end HodgeConjecture.CommutativeAlgebra
