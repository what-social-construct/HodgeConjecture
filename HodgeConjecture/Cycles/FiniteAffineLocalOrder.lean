import HodgeConjecture.Cycles.FiniteAffineFiber
import HodgeConjecture.Cycles.FiniteLocalizationNorm
import HodgeConjecture.Cycles.FunctionFieldNorm
import HodgeConjecture.Cycles.SchemeLocalOrder
import HodgeConjecture.CommutativeAlgebra.LocalizedResidueDegree
import HodgeConjecture.Cycles.FiniteAffineStalk
import HodgeConjecture.Cycles.FiniteAffineResidue
import HodgeConjecture.Cycles.FiniteDivisorPoints
import HodgeConjecture.Cycles.FunctionFieldResidue

/-!
# Norm coefficients over an actual target stalk

Apply the local norm formula to the section algebra of the whole affine
inverse image, localized at a target divisor point. The field extension
is the original generic-stalk pullback; the base ring is the actual target
stalk. The maximal localizations are compared with the source stalks by
`finiteAffineFiber_stalkEquiv`. This implements the coefficient reduction
in Stacks 02RT: https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory HodgeConjecture.CommutativeAlgebra
open scoped HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
open scoped HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  (U : Y.Opens) [hU : IsAffine U] [Nonempty U]

set_option quotPrecheck false in
local notation "A" => Γ(Y, U)
set_option quotPrecheck false in
local notation "B" => Γ(X, f ⁻¹ᵁ U)

local instance finiteAffineOrderPreimageNonempty : Nonempty (f ⁻¹ᵁ U) := nonempty_preimage_of_isDominant f U
local instance finiteAffineOrderSectionAlgebra : Algebra A B := (f.app U).hom.toAlgebra
local instance finiteAffineOrderSectionFinite : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
local instance finiteAffineOrderBaseFractionRing : IsFractionRing A Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
local instance finiteAffineOrderSourceFractionRing : IsFractionRing B X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X _ (IsAffineOpen.preimage hU f)

local instance finiteAffineOrderSectionFaithful : FaithfulSMul A B := by
  letI : Algebra A X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  letI : Algebra Y.functionField X.functionField := (functionFieldMapOfDominant f).hom.toAlgebra
  letI : IsScalarTower A B X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A Y.functionField X.functionField :=
    CollisionFoundations.functionFieldMapOfDominant_sectionScalarTower f U
  have hinj : Function.Injective (algebraMap A X.functionField) := by
    rw [IsScalarTower.algebraMap_eq A Y.functionField X.functionField]
    exact (algebraMap Y.functionField X.functionField).injective.comp
      (IsFractionRing.injective A Y.functionField)
  apply (faithfulSMul_iff_algebraMap_injective A B).mpr
  intro a b h
  apply hinj
  simpa only [IsScalarTower.algebraMap_apply A B X.functionField] using
    congrArg (algebraMap B X.functionField) h

variable (y : DivisorPoint Y) (hy : y.val ∈ U)

set_option quotPrecheck false in
local notation "p" => (IsAffineOpen.primeIdealOf hU ⟨y.val, hy⟩).asIdeal
set_option quotPrecheck false in
local notation "R" => Y.presheaf.stalk y.val
set_option quotPrecheck false in
local notation "T" => finiteLocalization A B p

attribute [local instance] atPrime_krullDimLE_one finiteAlgebra_maximal_liesOver

/-- The norm coefficient is computed over the actual target stalk and the original function fields. -/
theorem divisorOrder_norm_eq_sum_finiteAffine (g : X.functionFieldˣ) :
    letI : Algebra A R := Y.presheaf.algebra_section_stalk ⟨y.val, hy⟩
    letI : IsLocalization.AtPrime R p :=
      IsAffineOpen.isLocalization_stalk hU ⟨y.val, hy⟩
    letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
    letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
    letI : Module.Finite R T := Module.Finite.of_isLocalization A B (p).primeCompl
    letI : IsDomain T := finiteLocalization_isDomain A B p
    letI : IsNoetherianRing T := IsNoetherianRing.of_finite R T
    letI : Ring.KrullDimLE 1 T := integralAlgebra_krullDimLE_one R T
    divisorOrder Y y (functionFieldNorm f g) =
      ∑ᶠ q : MaximalSpectrum T,
        (Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ q.asIdeal) : ℤ) *
          localOrder (Localization.AtPrime q.asIdeal) g := by
  letI : Algebra A R := Y.presheaf.algebra_section_stalk ⟨y.val, hy⟩
  letI : IsLocalization.AtPrime R p :=
    IsAffineOpen.isLocalization_stalk hU ⟨y.val, hy⟩
  letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
  letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
  letI : Module.Finite R T := Module.Finite.of_isLocalization A B (p).primeCompl
  letI : IsDomain T := finiteLocalization_isDomain A B p
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  letI : Ring.KrullDimLE 1 T := integralAlgebra_krullDimLE_one R T
  letI : Algebra A X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  letI : Algebra Y.functionField X.functionField := (functionFieldMapOfDominant f).hom.toAlgebra
  letI : IsScalarTower A B X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A Y.functionField X.functionField :=
    CollisionFoundations.functionFieldMapOfDominant_sectionScalarTower f U
  letI : Algebra R X.functionField :=
    ((functionFieldMapOfDominant f).hom.comp (algebraMap R Y.functionField)).toAlgebra
  letI : IsScalarTower R Y.functionField X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A R Y.functionField := functionField_isScalarTower Y U ⟨y.val, hy⟩
  letI : IsScalarTower A R X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply A Y.functionField X.functionField,
      IsScalarTower.algebraMap_apply A R Y.functionField,
      ← IsScalarTower.algebraMap_apply R Y.functionField X.functionField]
  rw [functionFieldNorm_eq]
  exact localOrder_norm_eq_sum_finiteLocalization A B R Y.functionField X.functionField p g

include U hy in
private theorem divisorOrder_norm_eq_sum_finiteAffine_fiber
    (k : Type u) [Field k] (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [IsLocallyNoetherian X] (g : X.functionFieldˣ) :
    divisorOrder Y y (functionFieldNorm f g) =
      ∑ᶠ x : {x : X // f.base x = y.val},
        (residueFieldDegree f x.val : ℤ) *
          divisorOrder X (divisorPointOfFiniteFiber k pY f y x) g := by
  letI : Algebra A R := Y.presheaf.algebra_section_stalk ⟨y.val, hy⟩
  letI : IsLocalization.AtPrime R p := IsAffineOpen.isLocalization_stalk hU ⟨y.val, hy⟩
  letI : Algebra R T := finiteLocalization_baseAlgebra A B p R
  letI : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R
  letI : Module.Finite R T := Module.Finite.of_isLocalization A B (p).primeCompl
  letI : IsDomain T := finiteLocalization_isDomain A B p
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  letI : Ring.KrullDimLE 1 T := integralAlgebra_krullDimLE_one R T
  rw [divisorOrder_norm_eq_sum_finiteAffine f U y hy]
  apply finsum_eq_of_bijective (finiteAffineFiberEquiv f U hU ⟨y.val, hy⟩)
    (finiteAffineFiberEquiv f U hU ⟨y.val, hy⟩).bijective
  intro q
  have hd := finiteAffineFiber_residueDegree f U hU ⟨y.val, hy⟩ q
  change Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ q.asIdeal) =
    residueFieldDegree f (finiteAffineFiberEquiv f U hU ⟨y.val, hy⟩ q).val at hd
  rw [hd]
  congr 1
  exact finiteAffineFiber_localOrder f U hU ⟨y.val, hy⟩ q g

/-- The norm coefficient is the weighted sum of the existing divisor orders over the
actual source fiber. The field setting uses only the previously proved codimension comparison. -/
theorem divisorOrder_norm_eq_sum_fiber
    (k : Type u) [Field k] (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [IsLocallyNoetherian X] (g : X.functionFieldˣ) :
    divisorOrder Y y (functionFieldNorm f g) =
      ∑ᶠ x : {x : X // f.base x = y.val},
        (residueFieldDegree f x.val : ℤ) *
          divisorOrder X (divisorPointOfFiniteFiber k pY f y x) g := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := y.val) (by trivial)
  letI : IsAffine U := hU
  letI : Nonempty U := ⟨⟨y.val, hy⟩⟩
  exact divisorOrder_norm_eq_sum_finiteAffine_fiber f U y hy k pY g

end

end HodgeConjecture.SchemeCycles
