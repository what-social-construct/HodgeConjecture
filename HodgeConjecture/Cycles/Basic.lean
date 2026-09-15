import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Finite cycles on actual integral closed subschemes

The generators are ideal-sheaf data whose associated closed subschemes are
integral. Cycles are finite formal sums of these actual generators, with
specified coefficients. They are ungraded here: no dimension-preservation
claim, rational-equivalence quotient, or Chow multiplication is imposed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- Actual integral closed subschemes, represented by their ideal sheaves. -/
abbrev IntegralClosedSubscheme (X : Scheme.{u}) :=
  {J : X.IdealSheafData // IsIntegral J.subscheme}

/-- Finite, ungraded cycles on a scheme with coefficients in `R`. -/
abbrev Cycles (X : Scheme.{u}) (R : Type v) [Zero R] :=
  IntegralClosedSubscheme X →₀ R

variable {X : Scheme.{u}} (R : Type v) [Semiring R]

/-- The fundamental cycle of an integral closed subscheme has coefficient one. -/
def fundamentalCycle (Z : IntegralClosedSubscheme X) : Cycles X R :=
  Finsupp.single Z 1

@[simp]
theorem fundamentalCycle_apply_self (Z : IntegralClosedSubscheme X) :
    fundamentalCycle R Z Z = 1 := by
  simp [fundamentalCycle]

/-- An integral generator defines a nonzero cycle over nontrivial coefficients. -/
theorem fundamentalCycle_ne_zero [Nontrivial R] (Z : IntegralClosedSubscheme X) :
    fundamentalCycle R Z ≠ 0 := by
  simp [fundamentalCycle]

omit [Semiring R] in
/-- Integrality transports across an actual scheme isomorphism. -/
theorem isIntegral_of_iso {Y : Scheme.{u}} (e : X ≅ Y) [IsIntegral X] :
    IsIntegral Y := by
  letI : Nonempty Y := ⟨e.hom.base (Classical.arbitrary X)⟩
  exact isIntegral_of_isOpenImmersion e.inv

end

end HodgeConjecture.SchemeCycles
