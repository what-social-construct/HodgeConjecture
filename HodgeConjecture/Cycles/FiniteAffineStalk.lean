module

public import HodgeConjecture.Cycles.FiniteAffineFiber
public import HodgeConjecture.Cycles.SchemeLocalOrder
public import HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
public import HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

@[expose] public section

/-!
# The semilocal orders are the actual source-stalk orders

The section-linear stalk equivalence identifies the orders in the finite
norm sum with orders in the original function field of the source scheme.
This is the local-ring comparison in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory HodgeConjecture.CommutativeAlgebra
open scoped HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
open scoped HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U)
  [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]

set_option quotPrecheck false in
local notation "A" => Γ(Y, U)
set_option quotPrecheck false in
local notation "B" => Γ(X, f ⁻¹ᵁ U)

local instance finiteAffineStalkSectionAlgebra : Algebra A B := (f.app U).hom.toAlgebra

variable [hFaith : FaithfulSMul Γ(Y, U) Γ(X, f ⁻¹ᵁ U)] (y : U)

set_option quotPrecheck false in
local notation "T" => finiteLocalization A B (hU.primeIdealOf y).asIdeal

include hFaith in
local instance finiteAffineStalkLocalizedDomain : IsDomain T := finiteLocalization_isDomain A B (hU.primeIdealOf y).asIdeal
variable [hNoeth : IsNoetherianRing (finiteLocalization Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
    (hU.primeIdealOf y).asIdeal)]
  [hDim : Ring.KrullDimLE 1 (finiteLocalization Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
    (hU.primeIdealOf y).asIdeal)]

attribute [local instance] atPrime_krullDimLE_one

omit [IsIntegral X] [IsIntegral Y] [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] hFaith hNoeth in
/-- The source stalk inherits the dimension bound through the actual stalk equivalence. -/
theorem finiteAffineFiber_stalkKrullDimLE (q : MaximalSpectrum T) :
    Ring.KrullDimLE 1 (X.presheaf.stalk (finiteAffineFiberEquiv f U hU y q).val) := by
  let x := finiteAffineFiberEquiv f U hU y q
  letI := X.presheaf.algebra_section_stalk
    (⟨x.val, by change f.base x.val ∈ U; rw [x.property]; exact y.property⟩ : f ⁻¹ᵁ U)
  apply Ring.krullDimLE_iff.mpr
  rw [(finiteAffineFiber_stalkEquiv f U hU y q).toRingEquiv.ringKrullDim]
  exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal))

omit [IsIntegral X] [IsIntegral Y] [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] hFaith hDim in
/-- The source stalk inherits Noetherianity from the semilocal algebra. -/
theorem finiteAffineFiber_stalkIsNoetherianRing (q : MaximalSpectrum T) :
    IsNoetherianRing (X.presheaf.stalk (finiteAffineFiberEquiv f U hU y q).val) := by
  let x := finiteAffineFiberEquiv f U hU y q
  letI := X.presheaf.algebra_section_stalk
    (⟨x.val, by change f.base x.val ∈ U; rw [x.property]; exact y.property⟩ : f ⁻¹ᵁ U)
  exact isNoetherianRing_of_ringEquiv (Localization.AtPrime q.asIdeal)
    (finiteAffineFiber_stalkEquiv f U hU y q).toRingEquiv.symm

/-- Each order in the semilocal norm sum is the order in the actual source stalk,
using its canonical embedding in the original scheme function field. -/
theorem finiteAffineFiber_localOrder (q : MaximalSpectrum T) (g : X.functionFieldˣ) :
    letI : IsFractionRing B X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X _ (hU.preimage f)
    let x := finiteAffineFiberEquiv f U hU y q
    letI := finiteAffineFiber_stalkIsNoetherianRing f U hU y q
    letI := finiteAffineFiber_stalkKrullDimLE f U hU y q
    localOrder (Localization.AtPrime q.asIdeal) g = localOrder (X.presheaf.stalk x.val) g := by
  letI : IsFractionRing B X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ (hU.preimage f)
  let x := finiteAffineFiberEquiv f U hU y q
  have hx : f.base x.val ∈ U := by rw [x.property]; exact y.property
  letI := X.presheaf.algebra_section_stalk (⟨x.val, hx⟩ : f ⁻¹ᵁ U)
  letI := (hU.preimage f).isLocalization_stalk (⟨x.val, hx⟩ : f ⁻¹ᵁ U)
  letI := functionField_isScalarTower X (f ⁻¹ᵁ U) ⟨x.val, hx⟩
  letI : IsScalarTower B (Localization.AtPrime q.asIdeal) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun b => by
      rw [IsScalarTower.algebraMap_apply B T X.functionField,
        IsScalarTower.algebraMap_apply B T (Localization.AtPrime q.asIdeal),
        ← IsScalarTower.algebraMap_apply T (Localization.AtPrime q.asIdeal) X.functionField]
  letI := finiteAffineFiber_stalkIsNoetherianRing f U hU y q
  letI := finiteAffineFiber_stalkKrullDimLE f U hU y q
  exact localOrder_algEquiv_of_isLocalization
    ((hU.preimage f).primeIdealOf ⟨x.val, hx⟩).asIdeal.primeCompl
    (finiteAffineFiber_stalkEquiv f U hU y q) g

end

end HodgeConjecture.SchemeCycles
