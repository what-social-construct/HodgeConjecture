module

public import HodgeConjecture.Realization.Betti.SmallSingularComparison
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The native small-chain inclusion is tested on genuine open covers in every
degree, including degenerate cover members and the original P¹ complex
charts. This proves a cover comparison, with no sphere group computation
or singular-cohomology dualization supplied as a premise.
-/

set_option autoImplicit false

open CategoryTheory HomologicalComplex HodgeConjecture
open SmallSingularComparison SingularSubdivision

namespace SmallSingularComparisonVerification

noncomputable section

example (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (smallInclusion X U V) :=
  inclusion_quasiIso X U V hU hV hcover

-- Empty cover members are valid, including the boundary degree zero.
example (X : TopCat.{0}) : IsIso (homologyMap (smallInclusion X Set.univ ∅) 0) :=
  isIso_homologyMap_inclusion X Set.univ ∅ isOpen_univ isOpen_empty (by simp) 0

example (X : TopCat.{0}) : IsIso (homologyMap (smallInclusion X ∅ Set.univ) 2) :=
  isIso_homologyMap_inclusion X ∅ Set.univ isOpen_empty isOpen_univ (by simp) 2

example : IsIso (homologyMap (smallInclusion (TopCat.of Empty) ∅ ∅) 3) :=
  isIso_homologyMap_inclusion (TopCat.of Empty) ∅ ∅ isOpen_empty isOpen_empty (by ext x; exact x.elim) 3

theorem real_twoOpen_cover : Set.Iio (1 : ℝ) ∪ Set.Ioi (-1 : ℝ) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ, iff_true]
  by_cases hx : x < 1
  · exact Or.inl hx
  · exact Or.inr (by linarith)

example : IsIso (homologyMap
    (smallInclusion (TopCat.of ℝ) (Set.Iio 1) (Set.Ioi (-1))) 2) :=
  isIso_homologyMap_inclusion (TopCat.of ℝ) _ _ isOpen_Iio isOpen_Ioi real_twoOpen_cover 2

example : IsIso (homologyMap
    (smallInclusion (TopCat.of ℝ) (Set.Iio 1) (Set.Ioi (-1))) 3) :=
  isIso_homologyMap_inclusion (TopCat.of ℝ) _ _ isOpen_Iio isOpen_Ioi real_twoOpen_cover 3

example (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (homologyIso X U V hU hV hcover n).hom = homologyMap (smallInclusion X U V) n :=
  homologyIso_hom X U V hU hV hcover n

-- The comparison applies to the original affine evaluation topology on actual scheme-valued points.
example : IsIso (homologyMap
    (smallInclusion (TopCat.of ProjectiveLineComplexPoints.Point)
      (Set.range ProjectiveLineComplexPoints.finite)
      (Set.range ProjectiveLineComplexPoints.reciprocal)) 2) :=
  isIso_homologyMap_inclusion _ _ _
    ProjectiveLineComplexPoints.isOpenEmbedding_finite.isOpen_range
    ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal.isOpen_range
    ProjectiveLineComplexPoints.range_finite_union_reciprocal 2

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ChainHomologyClasses.classOf,
      `HodgeConjecture.ChainHomologyClasses.cyclesMk_i,
      `HodgeConjecture.ChainHomologyClasses.classOf_ι,
      `HodgeConjecture.ChainHomologyClasses.classOf_surjective,
      `HodgeConjecture.ChainHomologyClasses.classOf_eq_zero_iff,
      `HodgeConjecture.ChainHomologyClasses.classOf_map,
      `HodgeConjecture.ChainHomologyClasses.map_cycle,
      `HodgeConjecture.ChainHomologyClasses.classOf_congr,
      `HodgeConjecture.ChainHomologyClasses.quasiIso_of_eventual_image,
      `HodgeConjecture.SmallSingularComparison.inclusion_quasiIso,
      `HodgeConjecture.SmallSingularComparison.isIso_homologyMap_inclusion,
      `HodgeConjecture.SmallSingularComparison.homologyIso,
      `HodgeConjecture.SmallSingularComparison.homologyIso_hom,
      `SmallSingularComparisonVerification.real_twoOpen_cover] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end

end SmallSingularComparisonVerification
