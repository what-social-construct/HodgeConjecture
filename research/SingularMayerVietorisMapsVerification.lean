module

import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory HodgeConjecture HodgeConjecture.SingularMayerVietoris
open HodgeConjecture.SingularSubcomplexes

example (X : TopCat.{0}) (U V : Set X) (x : ↥(U ∩ V)) :
    (intersectionToLeft X U V x).val = x.val ∧
      (intersectionToRight X U V x).val = x.val := ⟨rfl, rfl⟩

example (X : TopCat.{0}) (U V : Set X) :
    intersectionToLeft X U V ≫ subsetInclusion X U =
      intersectionToRight X U V ≫ subsetInclusion X V := by simp

example (X : TopCat.{0}) (U V : Set X) (n : ℕ) (z : SingularCochains.Cohomology X n) :
    restriction X U V n z =
      (SingularCochains.cohomologyPullback (subsetInclusion X U) n z,
        SingularCochains.cohomologyPullback (subsetInclusion X V) n z) :=
  restriction_apply X U V n z

example (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (a : SingularCochains.Cohomology (TopCat.of U) n)
    (b : SingularCochains.Cohomology (TopCat.of V) n) :
    difference X U V n (a, b) =
      SingularCochains.cohomologyPullback (intersectionToLeft X U V) n a -
        SingularCochains.cohomologyPullback (intersectionToRight X U V) n b :=
  difference_apply X U V n a b

-- The second component carries the genuine negative sign.
example (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (b : SingularCochains.Cohomology (TopCat.of V) n) :
    difference X U V n (0, b) =
      -SingularCochains.cohomologyPullback (intersectionToRight X U V) n b := by
  rw [difference_apply, map_zero, zero_sub]

example (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (a : SingularCochains.Cohomology (TopCat.of U) n) :
    difference X U V n (a, 0) =
      SingularCochains.cohomologyPullback (intersectionToLeft X U V) n a := by
  rw [difference_apply, map_zero, sub_zero]

-- Both independent original pullbacks meet at the same actual intersection inclusion.
example (X : TopCat.{0}) (U V : Set X) (n : ℕ) (z : SingularCochains.Cohomology X n) :
    difference X U V n (restriction X U V n z) = 0 := by
  rw [restriction_apply, difference_apply]
  have hU := congrArg (fun f ↦ f z)
    (SingularCochains.cohomologyPullback_comp (intersectionToLeft X U V) (subsetInclusion X U) n)
  have hV := congrArg (fun f ↦ f z)
    (SingularCochains.cohomologyPullback_comp (intersectionToRight X U V) (subsetInclusion X V) n)
  rw [intersectionToLeft_subsetInclusion] at hU
  rw [intersectionToRight_subsetInclusion] at hV
  simp only [ModuleCat.comp_apply] at hU hV
  rw [← hU, ← hV, sub_self]

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularMayerVietoris.intersectionToLeft,
      `HodgeConjecture.SingularMayerVietoris.intersectionToRight,
      `HodgeConjecture.SingularMayerVietoris.intersectionToLeft_subsetInclusion,
      `HodgeConjecture.SingularMayerVietoris.intersectionToRight_subsetInclusion,
      `HodgeConjecture.SingularMayerVietoris.chartCohomologyIso_hom,
      `HodgeConjecture.SingularMayerVietoris.chartCohomologyIso_inv,
      `HodgeConjecture.SingularMayerVietoris.restriction_cochain_fst,
      `HodgeConjecture.SingularMayerVietoris.restriction_cochain_snd,
      `HodgeConjecture.SingularMayerVietoris.restriction_homology_fst,
      `HodgeConjecture.SingularMayerVietoris.restriction_homology_snd,
      `HodgeConjecture.SingularMayerVietoris.restriction_apply,
      `HodgeConjecture.SingularMayerVietoris.difference_cochain_inl,
      `HodgeConjecture.SingularMayerVietoris.difference_cochain_inr,
      `HodgeConjecture.SingularMayerVietoris.intersection_cochain_left,
      `HodgeConjecture.SingularMayerVietoris.intersection_cochain_right,
      `HodgeConjecture.SingularMayerVietoris.intersection_homology_left,
      `HodgeConjecture.SingularMayerVietoris.intersection_homology_right,
      `HodgeConjecture.SingularMayerVietoris.difference_apply] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
