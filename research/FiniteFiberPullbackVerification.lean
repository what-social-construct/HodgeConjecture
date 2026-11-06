module

import HodgeConjecture
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! The new finite-fiber operation is checked on the existing cycle type,
including coefficients with zero divisors. Its axioms must remain the standard
Lean logical axioms. No Chow descent is asserted by these cycle-level checks. -/

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

noncomputable section
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

example (c : Cycles Y (ZMod 6)) :
    finiteFiberPullback (𝟙 Y) (ZMod 6) c = c := by
  rw [finiteFiberPullback_id]
  rfl

example [IsOpenImmersion f] :
    finiteFiberPullback f (ZMod 6) = openRestriction (ZMod 6) f :=
  finiteFiberPullback_eq_openRestriction f (ZMod 6)

example (d : ℕ) (hd : ∀ y : Y, finiteFiberDegree f y = d)
    (c : Cycles Y (ZMod 6)) :
    finitePushforward (ZMod 6) f (finiteFiberPullback f (ZMod 6) c) = d • c :=
  finitePushforward_finiteFiberPullback_of_degree_eq f (ZMod 6) d hd c

#print axioms fiberResidueFieldAlgEquiv
#print axioms finiteFiberPullback
#print axioms finiteFiberPullback_mem_cyclesOfDegree
#print axioms finiteFiberDegree_eq_sum
#print axioms finitePushforward_finiteFiberPullback_of_degree_eq
