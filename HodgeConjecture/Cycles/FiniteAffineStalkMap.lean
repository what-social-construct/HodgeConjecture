import HodgeConjecture.Cycles.FiniteAffineFiber
import HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
import HodgeConjecture.CommutativeAlgebra.LocalizedResidueDegree
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The semilocal base action is the actual scheme stalk map

Compatibility is proved on germs of sections and extended by localization.
It identifies the residue degree in Stacks 02MJ with the scheme residue
degree used in 02RT: https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

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

local instance finiteAffineStalkMapSectionAlgebra : Algebra A B := (f.app U).hom.toAlgebra

/-- The stalk equivalence intertwines the actual target stalk map with the
canonical base action on the maximal localization. -/
theorem finiteAffineFiber_stalkEquiv_stalkMap (q : MaximalSpectrum T) :
    letI : Algebra A R := Y.presheaf.algebra_section_stalk y
    letI : IsLocalization.AtPrime R p := hU.isLocalization_stalk y
    letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
    let x := finiteAffineFiberEquiv f U hU y q
    letI := X.presheaf.algebra_section_stalk
      (⟨x.val, by change f.base x.val ∈ U; rw [x.property]; exact y.property⟩ : f ⁻¹ᵁ U)
    (finiteAffineFiber_stalkEquiv f U hU y q).toRingHom.comp
        (((Y.presheaf.stalkCongr (.of_eq x.property.symm)).hom ≫ f.stalkMap x.val).hom) =
      algebraMap R (Localization.AtPrime q.asIdeal) := by
  letI : Algebra A R := Y.presheaf.algebra_section_stalk y
  letI : IsLocalization.AtPrime R p := hU.isLocalization_stalk y
  letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
  letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
  let x := finiteAffineFiberEquiv f U hU y q
  have hx : f.base x.val ∈ U := by rw [x.property]; exact y.property
  letI := X.presheaf.algebra_section_stalk (⟨x.val, hx⟩ : f ⁻¹ᵁ U)
  let e := finiteAffineFiber_stalkEquiv f U hU y q
  have hgerm : Y.presheaf.germ U y.val y.property ≫
      (Y.presheaf.stalkCongr (.of_eq x.property.symm)).hom ≫ f.stalkMap x.val =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x.val hx := by
    rw [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes, Scheme.stalkMap_germ]
  apply IsLocalization.ringHom_ext (p).primeCompl
  ext a
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hgerm) a
  change (((Y.presheaf.stalkCongr (.of_eq x.property.symm)).hom ≫ f.stalkMap x.val).hom)
      (algebraMap A R a) = algebraMap B (X.presheaf.stalk x.val) (algebraMap A B a) at h
  change e (_) = algebraMap R (Localization.AtPrime q.asIdeal) (algebraMap A R a)
  rw [h, e.commutes, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

end

end HodgeConjecture.SchemeCycles
