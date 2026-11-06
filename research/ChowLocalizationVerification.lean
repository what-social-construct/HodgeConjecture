module

import HodgeConjecture.Inputs.ChowLocalization
import HodgeConjecture.Realization.Chow.MarkedCycleMap
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP110: actual Chow localization, without a supplied exactness hypothesis.
Run with `lake env lean research/ChowLocalizationVerification.lean`.

The checks include empty/full opens, a nonzero cycle on the boundary of an
arbitrary (possibly nonreduced) scheme, trivial coefficients, the actual
Chow two-lift consumer, and boundary ambiguity for the marked cycle recipe.
All twenty new public declarations receive a standard-three axiom audit.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory HodgeConjecture HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable (X : Scheme.{u})

-- Full open: the reduced boundary is empty.
example : openComplementIdeal (𝟙 X) = ⊤ := by
  simp [openComplementIdeal]
  change Scheme.IdealSheafData.vanishingIdeal (⊥ : TopologicalSpace.Closeds X) = ⊤
  exact Scheme.IdealSheafData.vanishingIdeal_bot

-- Empty open: the boundary is the reduction of X, even if X is nonreduced.
example : openComplementIdeal (⊥ : X.Opens).ι = X.nilradical := by
  simp [openComplementIdeal]
  change Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X) = X.nilradical
  exact Scheme.IdealSheafData.vanishingIdeal_top

-- Every boundary point supplies a genuinely nonzero cycle in the kernel
-- and an actual boundary preimage. No ambient reducedness is assumed.
example {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (x : X) (hx : x ∉ Set.range j.base) :
    fundamentalCycle ℚ (pointSupport X x) ≠ 0 ∧
      openRestriction ℚ j (fundamentalCycle ℚ (pointSupport X x)) = 0 ∧
      ∃ b : Cycles (openComplementIdeal j).subscheme ℚ,
        closedImmersionPushforward ℚ (openComplementIdeal j).subschemeι b =
          fundamentalCycle ℚ (pointSupport X x) := by
  have hc : fundamentalCycle ℚ (pointSupport X x) ∈
      LinearMap.ker (openRestriction ℚ j) := by
    rw [ker_openRestriction]
    apply Finsupp.single_mem_supported
    simpa using hx
  refine ⟨?_, hc, ?_⟩
  · intro h
    have hcoeff := congrArg (fun c : Cycles X ℚ ↦ c (pointSupport X x)) h
    simp at hcoeff
  · rw [← range_closedPushforward_eq_ker_openRestriction ℚ
      (openComplementIdeal j).subschemeι j (range_openComplement j)] at hc
    exact hc

-- Degenerate coefficients are accepted in the actual homogeneous sequence.
example (δ : DimensionFunction X) {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℤ) :
    LinearMap.range (gradedClosedImmersionPushforwardWithCoefficients (ZMod 1)
      (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
      (openComplementIdeal j).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n) =
      LinearMap.ker (gradedOpenRestriction (ZMod 1) δ j n) :=
  range_openComplementPushforward_eq_ker (ZMod 1) δ j n

variable [IsNoetherian X]

-- The integral full-open sequence has zero kernel.
example (δ : DimensionFunction X) (n : ℤ) :
    LinearMap.range (chowClosedImmersionPushforward
      (δ.comapClosedImmersion (openComplementIdeal (𝟙 X)).subschemeι) δ
      (openComplementIdeal (𝟙 X)).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n) = ⊥ := by
  rw [range_chowOpenComplementPushforward_eq_ker, chowOpenRestriction_id]
  exact LinearMap.ker_id

-- The existing two-lift consumer now obtains its package from the actual
-- scheme maps, without a caller supplying ChowLocalizationHypotheses.
example (δ : DimensionFunction X) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    ∀ z₁ z₂ : RationalChowGroup δ n,
      rationalChowOpenRestriction δ j n z₁ = rationalChowOpenRestriction δ j n z₂ →
      ∃ b : RationalChowGroup
          (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) n,
        rationalChowClosedImmersionPushforward
          (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
          (openComplementIdeal j).subschemeι
          (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n b = z₁ - z₂ := by
  letI := openImmersion_isNoetherian j
  letI := ChowLocalization.ofOpenComplement δ j n
  intro z₁ z₂ h
  exact ChowLocalization.two_lifts_differ_by_boundary _ _ h rfl

-- Supplied cycle families that agree in open Chow give marked recipes
-- differing by an actual boundary class, with no claim that this class vanishes.
example {G : Type v} [Group G] [Finite G] (H : Subgroup G)
    (δ : DimensionFunction X) {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℤ)
    (C C' : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n)
    (x : MarkedSheetProjector.Residual H) :
    letI := openImmersion_isNoetherian j
    (∀ s, rationalClassMap (δ.comapOpenImmersion j) n (gradedOpenRestriction ℚ δ j n (C s)) =
      rationalClassMap (δ.comapOpenImmersion j) n (gradedOpenRestriction ℚ δ j n (C' s))) →
    ∃ b : RationalChowGroup
        (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) n,
      rationalChowClosedImmersionPushforward
        (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
        (openComplementIdeal j).subschemeι
        (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n b =
      MarkedSheetChow.chowMap H δ n C x - MarkedSheetChow.chowMap H δ n C' x := by
  letI := openImmersion_isNoetherian j
  letI := ChowLocalization.ofOpenComplement δ j n
  intro h
  apply ChowLocalization.two_lifts_differ_by_boundary _ _ (a :=
    rationalChowOpenRestriction δ j n (MarkedSheetChow.chowMap H δ n C' x)) _ rfl
  simp only [MarkedSheetChow.chowMap_apply, map_sum, map_smul,
    rationalChowOpenRestriction_classMap, h]

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.openComplementIdeal,
    `HodgeConjecture.SchemeCycles.openComplement_isReduced,
    `HodgeConjecture.SchemeCycles.range_openComplement,
    `HodgeConjecture.SchemeCycles.closedImageSubscheme_injective,
    `HodgeConjecture.SchemeCycles.closedImmersionPushforward_apply_image,
    `HodgeConjecture.SchemeCycles.range_closedImmersionPushforward,
    `HodgeConjecture.SchemeCycles.ker_openRestriction,
    `HodgeConjecture.SchemeCycles.range_closedPushforward_eq_ker_openRestriction,
    `HodgeConjecture.SchemeCycles.range_gradedClosedPushforward_eq_ker_gradedOpenRestriction,
    `HodgeConjecture.SchemeCycles.range_openComplementPushforward_eq_ker,
    `HodgeConjecture.SchemeCycles.exists_openRestriction_principalRelationData,
    `HodgeConjecture.SchemeCycles.exists_principalRelation_openLift,
    `HodgeConjecture.SchemeCycles.principalRelations_map_openRestriction,
    `HodgeConjecture.SchemeCycles.rationalPrincipalRelations_map_openRestriction,
    `HodgeConjecture.SchemeCycles.closedImmersion_isNoetherian,
    `HodgeConjecture.SchemeCycles.range_chowClosedPushforward_eq_ker_chowOpenRestriction,
    `HodgeConjecture.SchemeCycles.range_rationalChowClosedPushforward_eq_ker_rationalChowOpenRestriction,
    `HodgeConjecture.SchemeCycles.range_chowOpenComplementPushforward_eq_ker,
    `HodgeConjecture.SchemeCycles.range_rationalChowOpenComplementPushforward_eq_ker,
    `HodgeConjecture.ChowLocalization.ofOpenComplement]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
