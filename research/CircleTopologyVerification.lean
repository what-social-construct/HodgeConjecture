module

import HodgeConjecture.Realization.Betti.Examples.CircleTopology
import Lean.Util.CollectAxioms

/-!
Checks on the native complex unit circle: original punctures, continuous
argument charts, the two genuine overlap components, and the original
inclusion behavior. Every audited declaration must exist and use at most
the three standard Lean axioms.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture.CircleTopology

example : IsOpen firstOpen ∧ IsOpen secondOpen :=
  ⟨firstOpen_isOpen, secondOpen_isOpen⟩

example : firstOpen ∪ secondOpen = Set.univ := opens_cover

example : (1 : Circle) ∈ firstOpen ∧ (-1 : Circle) ∈ secondOpen := by
  constructor
  · change (1 : Circle) ≠ -1
    exact (Circle.neg_ne_self 1).symm
  · change (-1 : Circle) ≠ 1
    exact Circle.neg_ne_self 1

example : (-1 : Circle) ∉ firstOpen ∧ (1 : Circle) ∉ secondOpen := by
  constructor <;> exact not_not_intro rfl

example (z : firstOpen) :
    Circle.exp (firstHomeomorph z : ℝ) = (z : Circle) :=
  Circle.exp_arg z.val

example (t : Arc) :
    firstHomeomorph (firstHomeomorph.symm t) = t :=
  firstHomeomorph.apply_symm_apply t

example : ContractibleSpace firstOpen ∧ ContractibleSpace secondOpen :=
  ⟨inferInstance, inferInstance⟩

example : ContractibleSpace negativeComponent ∧ ContractibleSpace positiveComponent :=
  ⟨inferInstance, inferInstance⟩

example : IsOpen negativeComponent ∧ IsOpen positiveComponent ∧
    Disjoint negativeComponent positiveComponent ∧
    negativeComponent ∪ positiveComponent = Set.univ :=
  ⟨negativeComponent_isOpen, positiveComponent_isOpen, components_disjoint, components_cover⟩

-- The chosen points retain the actual exponential coordinates, rather than only their labels.
example : (overlapPoint false : Circle) = Circle.exp (-Real.pi / 2) :=
  overlapPoint_false_coe

example : (overlapPoint true : Circle) = Circle.exp (Real.pi / 2) :=
  overlapPoint_true_coe

example (t : NegativeArc) :
    Complex.arg ((negativeInclusion t : Circle) : ℂ) = (t : ℝ) :=
  arg_negativeInclusion t

example (t : PositiveArc) :
    Complex.arg ((positiveInclusion t : Circle) : ℂ) = (t : ℝ) :=
  arg_positiveInclusion t

example : overlapLabel (overlapPoint false) ≠ overlapLabel (overlapPoint true) := by
  simp

example : ¬ PathConnectedSpace overlap := by
  intro h
  exact overlapPoints_not_joined (PathConnectedSpace.joined _ _)

-- Both actual restriction maps identify the two components inside their connected chart.
example : Joined (overlapToFirst (overlapPoint false))
    (overlapToFirst (overlapPoint true)) := joined_firstOverlapPoints false true

example : Joined (overlapToSecond (overlapPoint false))
    (overlapToSecond (overlapPoint true)) := joined_secondOverlapPoints false true

example (z : overlap) : Joined z (overlapPoint (overlapLabel z)) :=
  joined_overlapPoint z

example (x y : overlap) : Joined x y ↔ overlapLabel x = overlapLabel y :=
  joined_iff_label_eq x y

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CircleTopology.firstOpen,
    `HodgeConjecture.CircleTopology.secondOpen,
    `HodgeConjecture.CircleTopology.firstOpen_isOpen,
    `HodgeConjecture.CircleTopology.secondOpen_isOpen,
    `HodgeConjecture.CircleTopology.opens_cover,
    `HodgeConjecture.CircleTopology.arg_ne_pi,
    `HodgeConjecture.CircleTopology.arg_mem_arc,
    `HodgeConjecture.CircleTopology.exp_ne_neg_one,
    `HodgeConjecture.CircleTopology.continuous_arg_first,
    `HodgeConjecture.CircleTopology.firstHomeomorph,
    `HodgeConjecture.CircleTopology.firstHomeomorph_apply,
    `HodgeConjecture.CircleTopology.firstHomeomorph_symm_apply,
    `HodgeConjecture.CircleTopology.negateCharts,
    `HodgeConjecture.CircleTopology.secondHomeomorph,
    `HodgeConjecture.CircleTopology.arcContractibleSpace,
    `HodgeConjecture.CircleTopology.firstContractibleSpace,
    `HodgeConjecture.CircleTopology.secondContractibleSpace,
    `HodgeConjecture.CircleTopology.overlap,
    `HodgeConjecture.CircleTopology.puncturedArc,
    `HodgeConjecture.CircleTopology.overlapToFirst,
    `HodgeConjecture.CircleTopology.overlapToSecond,
    `HodgeConjecture.CircleTopology.continuous_overlapToFirst,
    `HodgeConjecture.CircleTopology.continuous_overlapToSecond,
    `HodgeConjecture.CircleTopology.arg_ne_zero,
    `HodgeConjecture.CircleTopology.exp_ne_one,
    `HodgeConjecture.CircleTopology.overlapArgumentHomeomorph,
    `HodgeConjecture.CircleTopology.negativePart,
    `HodgeConjecture.CircleTopology.negativePart_isOpen,
    `HodgeConjecture.CircleTopology.negativePart_compl,
    `HodgeConjecture.CircleTopology.negativePart_compl_isOpen,
    `HodgeConjecture.CircleTopology.signSplitHomeomorph,
    `HodgeConjecture.CircleTopology.negativeHomeomorph,
    `HodgeConjecture.CircleTopology.positiveHomeomorph,
    `HodgeConjecture.CircleTopology.overlapHomeomorph,
    `HodgeConjecture.CircleTopology.negativeArcContractibleSpace,
    `HodgeConjecture.CircleTopology.positiveArcContractibleSpace,
    `HodgeConjecture.CircleTopology.negativeComponent,
    `HodgeConjecture.CircleTopology.positiveComponent,
    `HodgeConjecture.CircleTopology.negativeComponentHomeomorph,
    `HodgeConjecture.CircleTopology.positiveComponentHomeomorph,
    `HodgeConjecture.CircleTopology.negativeComponentContractibleSpace,
    `HodgeConjecture.CircleTopology.positiveComponentContractibleSpace,
    `HodgeConjecture.CircleTopology.negativeComponent_isOpen,
    `HodgeConjecture.CircleTopology.positiveComponent_isOpen,
    `HodgeConjecture.CircleTopology.components_cover,
    `HodgeConjecture.CircleTopology.components_disjoint,
    `HodgeConjecture.CircleTopology.negativeInclusion,
    `HodgeConjecture.CircleTopology.positiveInclusion,
    `HodgeConjecture.CircleTopology.continuous_negativeInclusion,
    `HodgeConjecture.CircleTopology.continuous_positiveInclusion,
    `HodgeConjecture.CircleTopology.negativeInclusion_coe,
    `HodgeConjecture.CircleTopology.positiveInclusion_coe,
    `HodgeConjecture.CircleTopology.arg_negativeInclusion,
    `HodgeConjecture.CircleTopology.arg_positiveInclusion,
    `HodgeConjecture.CircleTopology.overlapLabel,
    `HodgeConjecture.CircleTopology.negativePoint,
    `HodgeConjecture.CircleTopology.positivePoint,
    `HodgeConjecture.CircleTopology.overlapPoint,
    `HodgeConjecture.CircleTopology.overlapPoint_false_coe,
    `HodgeConjecture.CircleTopology.overlapPoint_true_coe,
    `HodgeConjecture.CircleTopology.overlapLabel_point,
    `HodgeConjecture.CircleTopology.joined_overlapPoint,
    `HodgeConjecture.CircleTopology.joined_iff_label_eq,
    `HodgeConjecture.CircleTopology.overlapPoints_not_joined,
    `HodgeConjecture.CircleTopology.joined_firstOverlapPoints,
    `HodgeConjecture.CircleTopology.joined_secondOverlapPoints]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
