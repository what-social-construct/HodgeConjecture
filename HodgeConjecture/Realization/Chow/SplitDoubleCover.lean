module

public import HodgeConjecture.Geometry.SplitDoubleCover
public import HodgeConjecture.Cycles.RationalChowOpenRestriction
public import HodgeConjecture.Cycles.RationalChowPushforward
public import HodgeConjecture.Cycles.FiniteFlatChowPullback
public import HodgeConjecture.Cycles.RationalFiniteChowPushforward
public import HodgeConjecture.Cycles.FinitePushforwardComposition
public import HodgeConjecture.Cycles.FiniteFiberClosedBaseChange

@[expose] public section

/-!
# Ordinary Chow groups of the actual split double cover

The upstairs group is the original rational Chow quotient of `X ⨿ X`,
with the structural dimension function of the actual fold followed by `p`.
The two components are original open restrictions, with their proved grading
identifications. Their inverse is the sum of the two original closed
pushforwards. All identities are proved on the unchanged actual cycle
representatives before passage to the ordinary Chow quotients.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SplitDoubleCoverChow

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeCycles
open SplitDoubleCover

universe u

private theorem dimensionFunction_ext {X : Scheme.{u}}
    {δ ε : DimensionFunction X} (h : ∀ x, δ x = ε x) : δ = ε := by
  cases δ with
  | mk f hf hc =>
    cases ε with
    | mk g hg hd =>
      have hfg : f = g := funext h
      subst g
      rfl

def regradeCycle {X : Scheme.{u}} {δ ε : DimensionFunction X}
    (h : δ = ε) (n : ℤ) (c : cyclesOfDegree ℚ δ n) : cyclesOfDegree ℚ ε n :=
  ⟨c.val, by cases h; exact c.property⟩

def regrade {X : Scheme.{u}} [IsNoetherian X]
    {δ ε : DimensionFunction X} (h : δ = ε) (n : ℤ) :
    RationalChowGroup δ n ≃ₗ[ℚ] RationalChowGroup ε n :=
  LinearEquiv.cast (R := ℚ) (M := fun d : DimensionFunction X ↦ RationalChowGroup d n) h

private theorem regrade_classMap {X : Scheme.{u}} [IsNoetherian X]
    {δ ε : DimensionFunction X} (h : δ = ε) (n : ℤ)
    (c : cyclesOfDegree ℚ δ n) :
    regrade h n (rationalClassMap δ n c) =
      rationalClassMap ε n (regradeCycle h n c) := by
  cases h
  rfl

private theorem openClosure_eq_closedImage {U Y : Scheme.{u}}
    (i : U ⟶ Y) [IsOpenImmersion i] [IsClosedImmersion i]
    (W : IntegralClosedSubscheme U) :
    openClosureSubscheme i W = closedImageSubscheme i W := by
  rw [openClosureSubscheme, ← ambientGenericPoint_closedImageSubscheme i W,
    pointSupport_ambientGenericPoint]

private theorem restriction_push_self {U Y : Scheme.{u}}
    (i : U ⟶ Y) [IsOpenImmersion i] [IsClosedImmersion i] (c : Cycles U ℚ) :
    openRestriction ℚ i (closedImmersionPushforward ℚ i c) = c := by
  ext W
  rw [openRestriction_apply, openClosure_eq_closedImage,
    closedImmersionPushforward_apply_image]

private theorem inl_not_inr_range (X : Scheme.{u}) (x : X) :
    (inl X).base x ∉ Set.range (inr X).base := by
  rintro ⟨y, hy⟩
  exact inr_ne_inl X X x y hy

private theorem inr_not_inl_range (X : Scheme.{u}) (x : X) :
    (inr X).base x ∉ Set.range (inl X).base := by
  rintro ⟨y, hy⟩
  exact inl_ne_inr X X y x hy

private theorem restriction_inl_push_inr (X : Scheme.{u}) (c : Cycles X ℚ) :
    openRestriction ℚ (inl X) (closedImmersionPushforward ℚ (inr X) c) = 0 := by
  ext W
  rw [openRestriction_apply]
  exact closedImmersionPushforward_apply_point_of_not_mem_range ℚ (inr X) c
    ((inl X).base (ambientGenericPoint W)) (inl_not_inr_range X _)

private theorem restriction_inr_push_inl (X : Scheme.{u}) (c : Cycles X ℚ) :
    openRestriction ℚ (inr X) (closedImmersionPushforward ℚ (inl X) c) = 0 := by
  ext W
  rw [openRestriction_apply]
  exact closedImmersionPushforward_apply_point_of_not_mem_range ℚ (inl X) c
    ((inr X).base (ambientGenericPoint W)) (inr_not_inl_range X _)

private theorem cycles_reconstruct (X : Scheme.{u}) (c : Cycles (X ⨿ X) ℚ) :
    closedImmersionPushforward ℚ (inl X) (openRestriction ℚ (inl X) c) +
      closedImmersionPushforward ℚ (inr X) (openRestriction ℚ (inr X) c) = c := by
  have hp (x : (X ⨿ X : Scheme)) :
      (closedImmersionPushforward ℚ (inl X) (openRestriction ℚ (inl X) c) +
        closedImmersionPushforward ℚ (inr X) (openRestriction ℚ (inr X) c))
          (pointSupport (X ⨿ X) x) = c (pointSupport (X ⨿ X) x) := by
    obtain ⟨x | x, rfl⟩ := (coprodMk X X).surjective x
    · rw [coprodMk_inl, Finsupp.add_apply,
        ← closedImage_pointSupport (inl X) x, closedImmersionPushforward_apply_image,
        openRestriction_apply]
      rw [closedImage_pointSupport]
      rw [closedImmersionPushforward_apply_point_of_not_mem_range ℚ (inr X) _ _
        (inl_not_inr_range X x), add_zero]
      simp only [openClosureSubscheme, ambientGenericPoint_pointSupport]
    · rw [coprodMk_inr, Finsupp.add_apply]
      rw [closedImmersionPushforward_apply_point_of_not_mem_range ℚ (inl X) _ _
        (inr_not_inl_range X x), zero_add]
      rw [← closedImage_pointSupport (inr X) x, closedImmersionPushforward_apply_image,
        openRestriction_apply, closedImage_pointSupport]
      simp only [openClosureSubscheme, ambientGenericPoint_pointSupport]
  ext W
  simpa only [pointSupport_ambientGenericPoint] using hp (ambientGenericPoint W)

/-- The actual fold is locally an isomorphism, so its original fiber length is one. -/
theorem fold_finiteFiberMultiplicity (X : Scheme.{u}) (x : (X ⨿ X : Scheme)) :
    finiteFiberMultiplicity (fold X) x = 1 := by
  rw [finiteFiberMultiplicity_eq_length_quotient,
    IsLocalRing.map_maximalIdeal_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((fold X).stalkMap x)).surjective]
  change (Module.length ((X ⨿ X).presheaf.stalk x)
    (IsLocalRing.ResidueField ((X ⨿ X).presheaf.stalk x))).toNat = 1
  rw [Module.length_eq_of_surjective
    (IsLocalRing.residue_surjective (R := (X ⨿ X).presheaf.stalk x)),
    Module.length_eq_one]
  rfl

private theorem restriction_inl_foldPull (X : Scheme.{u}) (c : Cycles X ℚ) :
    openRestriction ℚ (inl X) (finiteFiberPullback (fold X) ℚ c) = c := by
  ext W
  rw [openRestriction_apply, finiteFiberPullback_apply,
    openClosureSubscheme_ambientGenericPoint, fold_finiteFiberMultiplicity,
    Nat.cast_one, mul_one]
  change c (pointSupport X ((inl X ≫ fold X).base (ambientGenericPoint W))) = c W
  rw [inl_fold]
  change c (pointSupport X (ambientGenericPoint W)) = c W
  rw [pointSupport_ambientGenericPoint]

private theorem restriction_inr_foldPull (X : Scheme.{u}) (c : Cycles X ℚ) :
    openRestriction ℚ (inr X) (finiteFiberPullback (fold X) ℚ c) = c := by
  ext W
  rw [openRestriction_apply, finiteFiberPullback_apply,
    openClosureSubscheme_ambientGenericPoint, fold_finiteFiberMultiplicity,
    Nat.cast_one, mul_one]
  change c (pointSupport X ((inr X ≫ fold X).base (ambientGenericPoint W))) = c W
  rw [inr_fold]
  change c (pointSupport X (ambientGenericPoint W)) = c W
  rw [pointSupport_ambientGenericPoint]

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsNoetherian X]
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

/-- The original downstairs structural grading. -/
abbrev baseDimension := DimensionFunction.ofLocallyOfFiniteType k X p

/-- The exact original grading of the actual double cover over the base field. -/
abbrev sourceDimension :=
  DimensionFunction.ofLocallyOfFiniteType k (X ⨿ X) (sourceStructure p)

abbrev BaseChow (n : ℤ) := RationalChowGroup (baseDimension k p) n
abbrev CoverChow (n : ℤ) := RationalChowGroup (sourceDimension k p) n

omit [AlgebraicGeometry.IsNoetherian X] in
private theorem sourceDimension_inl (x : X) :
    sourceDimension k p ((inl X).base x) = baseDimension k p x := by
  change DimensionFunction.ofLocallyOfFiniteType k (X ⨿ X) (fold X ≫ p)
    ((inl X).base x) = _
  rw [DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p (fold X)]
  change baseDimension k p ((inl X ≫ fold X).base x) = baseDimension k p x
  rw [inl_fold]
  rfl

omit [AlgebraicGeometry.IsNoetherian X] in
private theorem sourceDimension_inr (x : X) :
    sourceDimension k p ((inr X).base x) = baseDimension k p x := by
  change DimensionFunction.ofLocallyOfFiniteType k (X ⨿ X) (fold X ≫ p)
    ((inr X).base x) = _
  rw [DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p (fold X)]
  change baseDimension k p ((inr X ≫ fold X).base x) = baseDimension k p x
  rw [inr_fold]
  rfl

omit [AlgebraicGeometry.IsNoetherian X] in
theorem leftDimension_eq :
    (sourceDimension k p).comapOpenImmersion (inl X) = baseDimension k p :=
  dimensionFunction_ext (sourceDimension_inl k p)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem rightDimension_eq :
    (sourceDimension k p).comapOpenImmersion (inr X) = baseDimension k p :=
  dimensionFunction_ext (sourceDimension_inr k p)

variable (n : ℤ)

/-- The original open restriction with its proved structural grading comparison. -/
def leftRestriction : CoverChow k p n →ₗ[ℚ] BaseChow k p n :=
  (regrade (leftDimension_eq k p) n).toLinearMap.comp
    (rationalChowOpenRestriction (sourceDimension k p) (inl X) n)

/-- The second original open restriction, preserving the same actual representatives. -/
def rightRestriction : CoverChow k p n →ₗ[ℚ] BaseChow k p n :=
  (regrade (rightDimension_eq k p) n).toLinearMap.comp
    (rationalChowOpenRestriction (sourceDimension k p) (inr X) n)

def leftCycle (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    cyclesOfDegree ℚ (baseDimension k p) n :=
  regradeCycle (leftDimension_eq k p) n
    (gradedOpenRestriction ℚ (sourceDimension k p) (inl X) n c)

def rightCycle (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    cyclesOfDegree ℚ (baseDimension k p) n :=
  regradeCycle (rightDimension_eq k p) n
    (gradedOpenRestriction ℚ (sourceDimension k p) (inr X) n c)

@[simp] theorem leftCycle_val (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    (leftCycle k p n c).val = openRestriction ℚ (inl X) c.val := rfl

@[simp] theorem rightCycle_val (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    (rightCycle k p n c).val = openRestriction ℚ (inr X) c.val := rfl

@[simp] theorem leftRestriction_classMap
    (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    leftRestriction k p n (rationalClassMap _ n c) =
      rationalClassMap _ n (leftCycle k p n c) := by
  change regrade (leftDimension_eq k p) n
    (rationalChowOpenRestriction _ (inl X) n (rationalClassMap _ n c)) = _
  simp only [rationalChowOpenRestriction_classMap, regrade_classMap, leftCycle]

@[simp] theorem rightRestriction_classMap
    (c : cyclesOfDegree ℚ (sourceDimension k p) n) :
    rightRestriction k p n (rationalClassMap _ n c) =
      rationalClassMap _ n (rightCycle k p n c) := by
  change regrade (rightDimension_eq k p) n
    (rationalChowOpenRestriction _ (inr X) n (rationalClassMap _ n c)) = _
  simp only [rationalChowOpenRestriction_classMap, regrade_classMap, rightCycle]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem leftPush_degree (W : IntegralClosedSubscheme X) :
    supportDegree (sourceDimension k p) (closedImageSubscheme (inl X) W) =
      supportDegree (baseDimension k p) W := by
  rw [supportDegree_closedImageSubscheme]
  exact sourceDimension_inl k p (ambientGenericPoint W)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem rightPush_degree (W : IntegralClosedSubscheme X) :
    supportDegree (sourceDimension k p) (closedImageSubscheme (inr X) W) =
      supportDegree (baseDimension k p) W := by
  rw [supportDegree_closedImageSubscheme]
  exact sourceDimension_inr k p (ambientGenericPoint W)

/-- Original ordinary Chow pushforward along the first actual closed inclusion. -/
def leftPush : BaseChow k p n →ₗ[ℚ] CoverChow k p n :=
  rationalChowClosedImmersionPushforward (baseDimension k p) (sourceDimension k p)
    (inl X) (leftPush_degree k p) n

/-- Original ordinary Chow pushforward along the second actual closed inclusion. -/
def rightPush : BaseChow k p n →ₗ[ℚ] CoverChow k p n :=
  rationalChowClosedImmersionPushforward (baseDimension k p) (sourceDimension k p)
    (inr X) (rightPush_degree k p) n

theorem leftRestriction_leftPush (z : BaseChow k p n) :
    leftRestriction k p n (leftPush k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [leftPush, rationalChowClosedImmersionPushforward_classMap,
    leftRestriction_classMap]
  congr 1
  apply Subtype.ext
  exact restriction_push_self (inl X) c.val

theorem rightRestriction_rightPush (z : BaseChow k p n) :
    rightRestriction k p n (rightPush k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [rightPush, rationalChowClosedImmersionPushforward_classMap,
    rightRestriction_classMap]
  congr 1
  apply Subtype.ext
  exact restriction_push_self (inr X) c.val

theorem leftRestriction_rightPush (z : BaseChow k p n) :
    leftRestriction k p n (rightPush k p n z) = 0 := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [rightPush, rationalChowClosedImmersionPushforward_classMap,
    leftRestriction_classMap]
  have hz : leftCycle k p n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ (baseDimension k p)
        (sourceDimension k p) (inr X) (rightPush_degree k p) n c) = 0 := by
    apply Subtype.ext
    exact restriction_inl_push_inr X c.val
  rw [hz, map_zero]

theorem rightRestriction_leftPush (z : BaseChow k p n) :
    rightRestriction k p n (leftPush k p n z) = 0 := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [leftPush, rationalChowClosedImmersionPushforward_classMap,
    rightRestriction_classMap]
  have hz : rightCycle k p n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ (baseDimension k p)
        (sourceDimension k p) (inl X) (leftPush_degree k p) n c) = 0 := by
    apply Subtype.ext
    exact restriction_inr_push_inl X c.val
  rw [hz, map_zero]

theorem chow_reconstruct (z : CoverChow k p n) :
    leftPush k p n (leftRestriction k p n z) +
      rightPush k p n (rightRestriction k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [leftRestriction_classMap, rightRestriction_classMap,
    leftPush, rightPush, rationalChowClosedImmersionPushforward_classMap,
    rationalChowClosedImmersionPushforward_classMap, ← map_add]
  congr 1
  apply Subtype.ext
  exact cycles_reconstruct X c.val

/-- A decomposition of the original upstairs ordinary Chow group, with
original geometric restrictions and inclusion pushforwards as its two directions. -/
def chowEquiv : CoverChow k p n ≃ₗ[ℚ] BaseChow k p n × BaseChow k p n where
  toFun z := (leftRestriction k p n z, rightRestriction k p n z)
  invFun z := leftPush k p n z.1 + rightPush k p n z.2
  left_inv := chow_reconstruct k p n
  right_inv z := by
    apply Prod.ext <;>
      simp only [map_add, leftRestriction_leftPush, leftRestriction_rightPush,
        rightRestriction_leftPush, rightRestriction_rightPush, add_zero, zero_add]
  map_add' z w := Prod.ext ((leftRestriction k p n).map_add z w)
    ((rightRestriction k p n).map_add z w)
  map_smul' r z := Prod.ext ((leftRestriction k p n).map_smul r z)
    ((rightRestriction k p n).map_smul r z)

/-- The first original inclusion has only its original first component. -/
theorem chowEquiv_leftPush (z : BaseChow k p n) :
    chowEquiv k p n (leftPush k p n z) = (z, 0) :=
  Prod.ext (leftRestriction_leftPush k p n z) (rightRestriction_leftPush k p n z)

/-- The second original inclusion has only its original second component. -/
theorem chowEquiv_rightPush (z : BaseChow k p n) :
    chowEquiv k p n (rightPush k p n z) = (0, z) :=
  Prod.ext (leftRestriction_rightPush k p n z) (rightRestriction_rightPush k p n z)

/-- Original finite flat pullback along the fold, with its exact original source grading. -/
def actualPull : BaseChow k p n →ₗ[ℚ] CoverChow k p n :=
  rationalChowFiniteFlatPullback k p (fold X) n

/-- Original finite pushforward along the same fold. -/
def actualPush : CoverChow k p n →ₗ[ℚ] BaseChow k p n :=
  rationalChowFinitePushforward k p (fold X) n

theorem leftRestriction_actualPull (z : BaseChow k p n) :
    leftRestriction k p n (actualPull k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [actualPull, rationalChowFiniteFlatPullback_classMap, leftRestriction_classMap]
  congr 1
  apply Subtype.ext
  exact restriction_inl_foldPull X c.val

theorem rightRestriction_actualPull (z : BaseChow k p n) :
    rightRestriction k p n (actualPull k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [actualPull, rationalChowFiniteFlatPullback_classMap, rightRestriction_classMap]
  congr 1
  apply Subtype.ext
  exact restriction_inr_foldPull X c.val

/-- The original fold pullback is diagonal in the actual Chow decomposition. -/
theorem chowEquiv_pull (z : BaseChow k p n) :
    chowEquiv k p n (actualPull k p n z) = (z, z) :=
  Prod.ext (leftRestriction_actualPull k p n z) (rightRestriction_actualPull k p n z)

theorem actualPush_leftPush (z : BaseChow k p n) :
    actualPush k p n (leftPush k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [leftPush, rationalChowClosedImmersionPushforward_classMap,
    actualPush, rationalChowFinitePushforward_classMap]
  congr 1
  apply Subtype.ext
  have h : (finitePushforward ℚ (fold X)).comp
      (closedImmersionPushforward ℚ (inl X)) = LinearMap.id := by
    rw [← finitePushforward_eq_closedImmersionPushforward (inl X) ℚ,
      finitePushforward_comp]
    simp only [inl_fold, finitePushforward_id]
  exact LinearMap.congr_fun h c.val

theorem actualPush_rightPush (z : BaseChow k p n) :
    actualPush k p n (rightPush k p n z) = z := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective _ n z
  rw [rightPush, rationalChowClosedImmersionPushforward_classMap,
    actualPush, rationalChowFinitePushforward_classMap]
  congr 1
  apply Subtype.ext
  have h : (finitePushforward ℚ (fold X)).comp
      (closedImmersionPushforward ℚ (inr X)) = LinearMap.id := by
    rw [← finitePushforward_eq_closedImmersionPushforward (inr X) ℚ,
      finitePushforward_comp]
    simp only [inr_fold, finitePushforward_id]
  exact LinearMap.congr_fun h c.val

/-- The original fold pushforward sums the two original restriction components. -/
theorem actualPush_eq_sum (z : CoverChow k p n) :
    actualPush k p n z = (chowEquiv k p n z).1 + (chowEquiv k p n z).2 := by
  have h := congrArg (actualPush k p n) (chow_reconstruct k p n z)
  simp only [map_add, actualPush_leftPush, actualPush_rightPush] at h
  exact h.symm

end HodgeConjecture.SplitDoubleCoverChow

end
