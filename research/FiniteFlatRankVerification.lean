module

import HodgeConjecture.Cycles.FiniteFlatRank
import Mathlib.Algebra.DualNumber
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Finite-flat rank comparisons on the actual cycle maps. The square-zero
algebra checks that geometric degree retains nilpotent length. -/

open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCycles

noncomputable section

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    finiteFiberDegree f y = f.finrank y := finiteFiberDegree_eq_finrank f y

example (Y : Scheme.{u}) (y : Y) : finiteFiberDegree (𝟙 Y) y = 1 := by
  rw [finiteFiberDegree_eq_finrank, Scheme.Hom.finrank_eq_one_of_isIso]
  rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    (d : ℕ) (hd : ∀ y, f.finrank y = d) (c : Cycles Y (ZMod 6)) :
    finitePushforward (ZMod 6) f (finiteFiberPullback f (ZMod 6) c) = d • c :=
  finitePushforward_finiteFiberPullback_of_finrank_eq f (ZMod 6) d hd c

example (k : Type u) [Field k] (y : PrimeSpectrum k) :
    finiteFiberDegree (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) y = 2 := by
  letI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  rw [finiteFiberDegree_SpecMap_field]
  change Module.finrank k (k × k) = 2
  simp

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SchemeCycles.finrank_toSpec_eq_globalSection_finrank,
      `HodgeConjecture.SchemeCycles.finiteFiberDegree_eq_finrank,
      `HodgeConjecture.SchemeCycles.finiteFiberDegree_SpecMap_algebraMap,
      `HodgeConjecture.SchemeCycles.finiteFiberDegree_SpecMap_field,
      `HodgeConjecture.SchemeCycles.finiteFiberDegree_isLocallyConstant,
      `HodgeConjecture.SchemeCycles.finitePushforward_finiteFiberPullback_of_finrank_eq] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end
