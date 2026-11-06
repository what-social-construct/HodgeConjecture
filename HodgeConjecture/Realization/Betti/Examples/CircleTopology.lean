module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-!
# Two actual punctured-circle charts

The native complex unit circle is covered by the complements of its two
real points. The argument and exponential give a proved homeomorphism
from the complement of `-1` to `(-π, π)`. Negation gives the other chart.
The overlap retains its two actual argument-sign components.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.CircleTopology

open Complex Set

/-- The actual unit circle with its native topology. -/
abbrev Space := Circle

/-- The chart obtained by removing the negative real point. -/
def firstOpen : Set Space := {z | z ≠ -1}

/-- The chart obtained by removing the positive real point. -/
def secondOpen : Set Space := {z | z ≠ 1}

/-- The argument interval of the first chart. -/
abbrev Arc := Ioo (-Real.pi) Real.pi

theorem firstOpen_isOpen : IsOpen firstOpen := isOpen_ne

theorem secondOpen_isOpen : IsOpen secondOpen := isOpen_ne

theorem opens_cover : firstOpen ∪ secondOpen = Set.univ := by
  ext z
  change (z ≠ -1 ∨ z ≠ 1) ↔ True
  constructor
  · intro _; trivial
  · intro _
    by_cases hz : z = -1
    · right
      rw [hz]
      exact Circle.neg_ne_self 1
    · exact Or.inl hz

theorem arg_ne_pi (z : Space) (hz : z ≠ -1) : arg (z : ℂ) ≠ Real.pi := by
  intro h
  apply hz
  apply Circle.injective_arg
  simpa using h

theorem arg_mem_arc (z : Space) (hz : z ≠ -1) : arg (z : ℂ) ∈ Arc :=
  ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (arg_ne_pi z hz)⟩

theorem exp_ne_neg_one (t : Arc) : Circle.exp t.val ≠ -1 := by
  intro h
  have ha := congrArg (fun z : Circle ↦ arg (z : ℂ)) h
  rw [Circle.arg_exp t.property.1 t.property.2.le] at ha
  have ht : t.val = Real.pi := by simpa using ha
  exact t.property.2.ne ht

/-- The argument chart is continuous for the original circle subtype topology. -/
theorem continuous_arg_first : Continuous (fun z : firstOpen ↦ arg (z.val : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (continuousAt_arg ?_).comp
    (continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt)
  exact mem_slitPlane_iff_arg.mpr ⟨arg_ne_pi z.val z.property, z.val.coe_ne_zero⟩

/-- The actual first punctured-circle chart, with both inverse identities proved. -/
def firstHomeomorph : firstOpen ≃ₜ Arc where
  toFun z := ⟨arg (z.val : ℂ), arg_mem_arc z.val z.property⟩
  invFun t := ⟨Circle.exp t.val, exp_ne_neg_one t⟩
  left_inv z := Subtype.ext (Circle.exp_arg z.val)
  right_inv t := Subtype.ext (Circle.arg_exp t.property.1 t.property.2.le)
  continuous_toFun := continuous_arg_first.subtype_mk _
  continuous_invFun := (Circle.exp.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem firstHomeomorph_apply (z : firstOpen) :
    (firstHomeomorph z : ℝ) = arg (z.val : ℂ) := rfl

@[simp]
theorem firstHomeomorph_symm_apply (t : Arc) :
    (firstHomeomorph.symm t : Space) = Circle.exp t.val := rfl

/-- Native negation exchanges the two punctures. -/
def negateCharts : secondOpen ≃ₜ firstOpen where
  toFun z := ⟨-z.val, by
    intro h
    apply z.property
    have hn := congrArg Neg.neg h
    simpa using hn⟩
  invFun z := ⟨-z.val, by
    intro h
    apply z.property
    have hn := congrArg Neg.neg h
    simpa using hn⟩
  left_inv z := Subtype.ext (neg_neg z.val)
  right_inv z := Subtype.ext (neg_neg z.val)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk (fun z ↦ by
    change -z.val ≠ -1
    simpa only [ne_eq, neg_inj] using (show z.val ≠ 1 from z.property))
  continuous_invFun := continuous_subtype_val.neg.subtype_mk (fun z ↦ by
    change -z.val ≠ 1
    simpa only [ne_eq, neg_eq_iff_eq_neg] using (show z.val ≠ -1 from z.property))

/-- The actual second punctured-circle chart. -/
def secondHomeomorph : secondOpen ≃ₜ Arc := negateCharts.trans firstHomeomorph

instance arcContractibleSpace : ContractibleSpace Arc :=
  (convex_Ioo (-Real.pi) Real.pi).contractibleSpace ⟨0, by simpa using Real.pi_pos⟩

instance firstContractibleSpace : ContractibleSpace firstOpen := firstHomeomorph.contractibleSpace

instance secondContractibleSpace : ContractibleSpace secondOpen := secondHomeomorph.contractibleSpace

/-- The actual intersection of the two punctured-circle opens. -/
def overlap : Set Space := firstOpen ∩ secondOpen

/-- The argument interval with its zero coordinate removed. -/
def puncturedArc : Set ℝ := {t | t ∈ Arc ∧ t ≠ 0}

/-- Regard an overlap point as a point in the first actual chart. -/
def overlapToFirst (z : overlap) : firstOpen := ⟨z.val, z.property.1⟩

/-- Regard an overlap point as a point in the second actual chart. -/
def overlapToSecond (z : overlap) : secondOpen := ⟨z.val, z.property.2⟩

theorem continuous_overlapToFirst : Continuous overlapToFirst :=
  continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)

theorem continuous_overlapToSecond : Continuous overlapToSecond :=
  continuous_subtype_val.subtype_mk (fun z ↦ z.property.2)

theorem arg_ne_zero (z : overlap) : arg (z.val : ℂ) ≠ 0 := by
  intro hz
  exact z.property.2 (Circle.arg_eq_zero.mp hz)

theorem exp_ne_one (t : puncturedArc) : Circle.exp t.val ≠ 1 := by
  intro h
  have ha := congrArg (fun z : Circle ↦ arg (z : ℂ)) h
  rw [Circle.arg_exp t.property.1.1 t.property.1.2.le] at ha
  apply t.property.2
  simpa using ha

/-- The overlap is the original argument interval with zero removed. -/
def overlapArgumentHomeomorph : overlap ≃ₜ puncturedArc where
  toFun z := ⟨arg (z.val : ℂ), arg_mem_arc z.val z.property.1, arg_ne_zero z⟩
  invFun t := ⟨Circle.exp t.val, exp_ne_neg_one ⟨t.val, t.property.1⟩, exp_ne_one t⟩
  left_inv z := Subtype.ext (Circle.exp_arg z.val)
  right_inv t := Subtype.ext (Circle.arg_exp t.property.1.1 t.property.1.2.le)
  continuous_toFun :=
    (continuous_arg_first.comp continuous_overlapToFirst).subtype_mk _
  continuous_invFun := (Circle.exp.continuous.comp continuous_subtype_val).subtype_mk _

/-- The negative-argument component in the original punctured interval topology. -/
def negativePart : Set puncturedArc := {t | (t : ℝ) < 0}

theorem negativePart_isOpen : IsOpen negativePart :=
  isOpen_lt continuous_subtype_val continuous_const

theorem negativePart_compl : negativePartᶜ = {t : puncturedArc | 0 < (t : ℝ)} := by
  ext t
  change (¬ t.val < 0) ↔ 0 < t.val
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm t.property.2)
  · exact fun h ↦ not_lt_of_ge h.le

theorem negativePart_compl_isOpen : IsOpen negativePartᶜ := by
  rw [negativePart_compl]
  exact isOpen_lt continuous_const continuous_subtype_val

/-- The actual punctured argument interval is the topological disjoint union of its sign pieces. -/
def signSplitHomeomorph : puncturedArc ≃ₜ ↥negativePart ⊕ ↥(negativePartᶜ) := by
  classical
  exact ((Equiv.Set.sumCompl negativePart).toHomeomorphOfContinuousOpen
    (continuous_subtype_val.sumElim continuous_subtype_val)
    (negativePart_isOpen.isOpenMap_subtype_val.sumElim
      negativePart_compl_isOpen.isOpenMap_subtype_val)).symm

/-- The lower argument interval, with the usual real subtype topology. -/
abbrev NegativeArc := Ioo (-Real.pi) (0 : ℝ)

/-- The upper argument interval, with the usual real subtype topology. -/
abbrev PositiveArc := Ioo (0 : ℝ) Real.pi

/-- Dropping the redundant punctured-interval conditions on the negative component. -/
def negativeHomeomorph : negativePart ≃ₜ NegativeArc where
  toFun t := ⟨t.val.val, t.val.property.1.1, t.property⟩
  invFun t := ⟨⟨t.val, ⟨t.property.1, t.property.2.trans Real.pi_pos⟩, t.property.2.ne⟩,
    t.property.2⟩
  left_inv t := rfl
  right_inv t := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Dropping the redundant punctured-interval conditions on the positive component. -/
def positiveHomeomorph : ↥(negativePartᶜ) ≃ₜ PositiveArc where
  toFun t := ⟨t.val.val,
    (Set.ext_iff.mp negativePart_compl t.val).mp t.property, t.val.property.1.2⟩
  invFun t := ⟨⟨t.val, ⟨(neg_lt_zero.mpr Real.pi_pos).trans t.property.1, t.property.2⟩,
    t.property.1.ne'⟩, not_lt_of_ge t.property.1.le⟩
  left_inv t := rfl
  right_inv t := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The original two-chart overlap splits into its two actual open-interval components. -/
def overlapHomeomorph : overlap ≃ₜ NegativeArc ⊕ PositiveArc :=
  overlapArgumentHomeomorph.trans
    (signSplitHomeomorph.trans (Homeomorph.sumCongr negativeHomeomorph positiveHomeomorph))

instance negativeArcContractibleSpace : ContractibleSpace NegativeArc :=
  (convex_Ioo (-Real.pi) 0).contractibleSpace
    ⟨-Real.pi / 2, by constructor <;> linarith [Real.pi_pos]⟩

instance positiveArcContractibleSpace : ContractibleSpace PositiveArc :=
  (convex_Ioo (0 : ℝ) Real.pi).contractibleSpace
    ⟨Real.pi / 2, by constructor <;> linarith [Real.pi_pos]⟩

/-- The lower component as an actual subset of the original overlap. -/
def negativeComponent : Set overlap := {z | arg (z.val : ℂ) < 0}

/-- The upper component as an actual subset of the original overlap. -/
def positiveComponent : Set overlap := {z | 0 < arg (z.val : ℂ)}

/-- The lower actual component has its native open-interval topology. -/
def negativeComponentHomeomorph : negativeComponent ≃ₜ NegativeArc :=
  (overlapArgumentHomeomorph.subtype
    (p := fun z ↦ z ∈ negativeComponent) (q := fun t ↦ t ∈ negativePart)
    (fun _ ↦ Iff.rfl)).trans negativeHomeomorph

/-- The upper actual component has its native open-interval topology. -/
def positiveComponentHomeomorph : positiveComponent ≃ₜ PositiveArc :=
  (overlapArgumentHomeomorph.subtype
    (p := fun z ↦ z ∈ positiveComponent) (q := fun t ↦ t ∈ negativePartᶜ)
    (fun z ↦ by
      change 0 < arg (z.val : ℂ) ↔ ¬ arg (z.val : ℂ) < 0
      exact ⟨fun h ↦ not_lt_of_ge h.le,
        fun h ↦ lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (arg_ne_zero z))⟩)).trans
    positiveHomeomorph

instance negativeComponentContractibleSpace : ContractibleSpace negativeComponent :=
  negativeComponentHomeomorph.contractibleSpace

instance positiveComponentContractibleSpace : ContractibleSpace positiveComponent :=
  positiveComponentHomeomorph.contractibleSpace

theorem negativeComponent_isOpen : IsOpen negativeComponent :=
  negativePart_isOpen.preimage overlapArgumentHomeomorph.continuous

theorem positiveComponent_isOpen : IsOpen positiveComponent := by
  exact isOpen_lt continuous_const
    (continuous_arg_first.comp continuous_overlapToFirst)

theorem components_cover : negativeComponent ∪ positiveComponent = Set.univ := by
  ext z
  change (arg (z.val : ℂ) < 0 ∨ 0 < arg (z.val : ℂ)) ↔ True
  exact ⟨fun _ ↦ trivial, fun _ ↦ lt_or_gt_of_ne (arg_ne_zero z)⟩

theorem components_disjoint : Disjoint negativeComponent positiveComponent := by
  rw [Set.disjoint_left]
  intro z hn hp
  change arg (z.val : ℂ) < 0 at hn
  change 0 < arg (z.val : ℂ) at hp
  exact lt_asymm hn hp

/-- Include a lower-interval coordinate as its original circle overlap point. -/
def negativeInclusion (t : NegativeArc) : overlap :=
  (negativeComponentHomeomorph.symm t).val

/-- Include an upper-interval coordinate as its original circle overlap point. -/
def positiveInclusion (t : PositiveArc) : overlap :=
  (positiveComponentHomeomorph.symm t).val

theorem continuous_negativeInclusion : Continuous negativeInclusion :=
  continuous_subtype_val.comp negativeComponentHomeomorph.symm.continuous

theorem continuous_positiveInclusion : Continuous positiveInclusion :=
  continuous_subtype_val.comp positiveComponentHomeomorph.symm.continuous

@[simp]
theorem negativeInclusion_coe (t : NegativeArc) :
    (negativeInclusion t : Space) = Circle.exp t.val := rfl

@[simp]
theorem positiveInclusion_coe (t : PositiveArc) :
    (positiveInclusion t : Space) = Circle.exp t.val := rfl

@[simp]
theorem arg_negativeInclusion (t : NegativeArc) :
    arg ((negativeInclusion t : Space) : ℂ) = t.val :=
  Circle.arg_exp t.property.1 (t.property.2.trans Real.pi_pos).le

@[simp]
theorem arg_positiveInclusion (t : PositiveArc) :
    arg ((positiveInclusion t : Space) : ℂ) = t.val :=
  Circle.arg_exp ((neg_lt_zero.mpr Real.pi_pos).trans t.property.1) t.property.2.le

/-- The sign component is a continuous map on the actual overlap. -/
def overlapLabel : C(overlap, Bool) :=
  ⟨fun z ↦ (overlapHomeomorph z).isRight,
    continuous_isRight.comp overlapHomeomorph.continuous⟩

/-- A distinguished coordinate of the lower actual component. -/
def negativePoint : NegativeArc :=
  ⟨-Real.pi / 2, by constructor <;> linarith [Real.pi_pos]⟩

/-- A distinguished coordinate of the upper actual component. -/
def positivePoint : PositiveArc :=
  ⟨Real.pi / 2, by constructor <;> linarith [Real.pi_pos]⟩

/-- The original overlap point in each component: false is lower, true is upper. -/
def overlapPoint (i : Bool) : overlap :=
  overlapHomeomorph.symm (if i then Sum.inr positivePoint else Sum.inl negativePoint)

@[simp]
theorem overlapPoint_false_coe :
    (overlapPoint false : Space) = Circle.exp (-Real.pi / 2) := rfl

@[simp]
theorem overlapPoint_true_coe :
    (overlapPoint true : Space) = Circle.exp (Real.pi / 2) := rfl

@[simp]
theorem overlapLabel_point (i : Bool) : overlapLabel (overlapPoint i) = i := by
  cases i <;> simp [overlapLabel, overlapPoint]

/-- Each actual overlap point is joined to the chosen point in its actual sign component. -/
theorem joined_overlapPoint (z : overlap) : Joined z (overlapPoint (overlapLabel z)) := by
  let point : Bool → NegativeArc ⊕ PositiveArc :=
    fun i ↦ if i then Sum.inr positivePoint else Sum.inl negativePoint
  have hjoined : ∀ x : NegativeArc ⊕ PositiveArc, Joined x (point x.isRight) := by
    intro x
    cases x with
    | inl x => exact (PathConnectedSpace.joined x negativePoint).map continuous_inl
    | inr x => exact (PathConnectedSpace.joined x positivePoint).map continuous_inr
  change Joined z (overlapHomeomorph.symm (point (overlapHomeomorph z).isRight))
  have h := (hjoined (overlapHomeomorph z)).map overlapHomeomorph.symm.continuous
  rw [overlapHomeomorph.symm_apply_apply] at h
  exact h

/-- Labels classify actual paths, so the overlap has exactly two path components. -/
theorem joined_iff_label_eq (x y : overlap) : Joined x y ↔ overlapLabel x = overlapLabel y := by
  constructor
  · intro h
    have heq := PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval)
      (overlapLabel.continuous.comp h.somePath.continuous) (x := 0) (y := 1)
    simpa using heq
  · intro h
    have hy := joined_overlapPoint y
    rw [← h] at hy
    exact (joined_overlapPoint x).trans hy.symm

/-- The two chosen actual overlap points lie in distinct path components. -/
theorem overlapPoints_not_joined : ¬ Joined (overlapPoint false) (overlapPoint true) := by
  rw [joined_iff_label_eq]
  simp

/-- The original first-chart inclusion sends both overlap components into one path component. -/
theorem joined_firstOverlapPoints (i j : Bool) :
    Joined (overlapToFirst (overlapPoint i)) (overlapToFirst (overlapPoint j)) :=
  PathConnectedSpace.joined _ _

/-- The original second-chart inclusion sends both overlap components into one path component. -/
theorem joined_secondOverlapPoints (i j : Bool) :
    Joined (overlapToSecond (overlapPoint i)) (overlapToSecond (overlapPoint j)) :=
  PathConnectedSpace.joined _ _

end HodgeConjecture.CircleTopology
