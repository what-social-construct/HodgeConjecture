import HodgeConjecture.Cycles.FiniteAffineStalkMap

/-!
# Actual residue degrees in the affine norm sum

The quotient-field weights in the semilocal calculation equal the degrees
of the original scheme residue maps. The comparison uses the proved stalk
map compatibility, as in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (U : Y.Opens) (hU : IsAffineOpen U) (y : U)

set_option quotPrecheck false in
local notation "A" => Γ(Y, U)
set_option quotPrecheck false in
local notation "B" => Γ(X, f ⁻¹ᵁ U)
set_option quotPrecheck false in
local notation "p" => (hU.primeIdealOf y).asIdeal
set_option quotPrecheck false in
local notation "T" => finiteLocalization A B p
set_option quotPrecheck false in
local notation "R" => Y.presheaf.stalk y.val

local instance finiteAffineResidueSectionAlgebra : Algebra A B := (f.app U).hom.toAlgebra
attribute [local instance] finiteAlgebra_maximal_liesOver

/-- The semilocal quotient degree is the degree of the actual scheme residue map. -/
theorem finiteAffineFiber_residueDegree (q : MaximalSpectrum T) :
    letI : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
    letI : Algebra A R := Y.presheaf.algebra_section_stalk y
    letI : IsLocalization.AtPrime R p := hU.isLocalization_stalk y
    letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
    letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
    letI : Module.Finite R T := Module.Finite.of_isLocalization A B (p).primeCompl
    let x := finiteAffineFiberEquiv f U hU y q
    letI : Algebra (Y.residueField (f.base x.val)) (X.residueField x.val) :=
      (f.residueFieldMap x.val).hom.toAlgebra
    Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ q.asIdeal) =
      Module.finrank (Y.residueField (f.base x.val)) (X.residueField x.val) := by
  letI : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
  letI : Algebra A R := Y.presheaf.algebra_section_stalk y
  letI : IsLocalization.AtPrime R p := hU.isLocalization_stalk y
  letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
  letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
  letI : Module.Finite R T := Module.Finite.of_isLocalization A B (p).primeCompl
  let x := finiteAffineFiberEquiv f U hU y q
  have hx : f.base x.val ∈ U := by rw [x.property]; exact y.property
  letI := X.presheaf.algebra_section_stalk (⟨x.val, hx⟩ : f ⁻¹ᵁ U)
  letI : Algebra (Y.residueField (f.base x.val)) (X.residueField x.val) :=
    (f.residueFieldMap x.val).hom.toAlgebra
  letI : Field (T ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  let e := (finiteAffineFiber_stalkEquiv f U hU y q).toRingEquiv
  let eR : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* Y.residueField (f.base x.val) :=
    (Y.residueFieldCongr x.property.symm).commRingCatIsoToRingEquiv
  let eT : (T ⧸ q.asIdeal) ≃+* X.residueField x.val :=
    (maximalQuotientResidueEquiv T (Localization.AtPrime q.asIdeal) q.asIdeal).trans
      (IsLocalRing.ResidueField.mapEquiv e.symm)
  apply Algebra.finrank_eq_of_equiv_equiv eR eT
  apply Ideal.Quotient.ringHom_ext
  ext r
  change f.residueFieldMap x.val (eR (IsLocalRing.residue R r)) =
    eT (Ideal.Quotient.mk q.asIdeal (algebraMap R T r))
  have hr := RingHom.congr_fun (finiteAffineFiber_stalkEquiv_stalkMap f U hU y q) r
  have hc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.residue_residueFieldCongr Y x.property.symm)) r
  change eR (IsLocalRing.residue R r) =
    Y.residue (f.base x.val) ((Y.presheaf.stalkCongr (.of_eq x.property.symm)).hom r) at hc
  rw [hc]
  change IsLocalRing.residue (X.presheaf.stalk x.val)
      (f.stalkMap x.val ((Y.presheaf.stalkCongr (.of_eq x.property.symm)).hom r)) =
    IsLocalRing.ResidueField.mapEquiv e.symm
      (maximalQuotientResidueEquiv T (Localization.AtPrime q.asIdeal) q.asIdeal
        (Ideal.Quotient.mk q.asIdeal (algebraMap R T r)))
  rw [maximalQuotientResidueEquiv_mk]
  change _ = IsLocalRing.residue (X.presheaf.stalk x.val)
    (e.symm (algebraMap T (Localization.AtPrime q.asIdeal) (algebraMap R T r)))
  rw [← IsScalarTower.algebraMap_apply]
  apply congrArg (IsLocalRing.residue (X.presheaf.stalk x.val))
  exact (e.symm_apply_eq.mpr hr.symm).symm

end

end HodgeConjecture.SchemeCycles
