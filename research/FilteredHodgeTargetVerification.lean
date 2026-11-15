module

public import HodgeConjecture.Realization.FilteredHodgeTarget
public import HodgeConjecture.Realization.DeRham.BettiHodgeTarget
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The proper-subspace control checks that the general construction does not
declare every rational vector Hodge. The scheme test retains the actual
singular group and derived filtration with the comparison supplied explicitly.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture

namespace FilteredHodgeTargetVerification

/-- A proper complex subspace of the genuine two-dimensional complexification.
This is a filtration test, not a claim of purity for a constant filtration. -/
def coordinateFiltration (_ : ℤ) :
    Submodule ℂ (RationalComplexification.Space (ℚ × ℚ)) :=
  LinearMap.ker (RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ))

theorem coordinateTarget (p : ℤ) (x : ℚ × ℚ) :
    x ∈ HodgeFiltration.rationalHodgeClasses coordinateFiltration p ↔ x.2 = 0 := by
  rw [HodgeFiltration.mem_rationalHodgeClasses_iff]
  change RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ)
    (RationalComplexification.embedding (ℚ × ℚ) x) = 0 ↔ x.2 = 0
  rw [RationalComplexification.map_embedding]
  change RationalComplexification.embedding ℚ x.2 = 0 ↔ x.2 = 0
  constructor
  · intro h
    apply RationalComplexification.embedding_injective ℚ
    simpa using h
  · intro h
    simp [h]

example : ((1, 0) : ℚ × ℚ) ∈
    HodgeFiltration.rationalHodgeClasses coordinateFiltration 1 :=
  (coordinateTarget 1 (1, 0)).mpr rfl

example : ((0, 1) : ℚ × ℚ) ∉
    HodgeFiltration.rationalHodgeClasses coordinateFiltration 1 := by
  rw [coordinateTarget]
  norm_num

example {H K : Type*} [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K]
    {F : ℤ → Submodule ℂ (RationalComplexification.Space H)}
    {G : ℤ → Submodule ℂ (RationalComplexification.Space K)}
    {f : H →ₗ[ℚ] K} (hf : HodgeFiltration.IsFilteredMap F G f)
    (p : ℤ) (x : H) (hx : x ∈ HodgeFiltration.rationalHodgeClasses F p) :
    f x ∈ HodgeFiltration.rationalHodgeClasses G p :=
  HodgeFiltration.map_mem_rationalHodgeClasses hf p hx

open CategoryTheory AlgebraicGeometry in
example {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (T : TopCat.{0}) (p : ℤ)
    (comparison : SchemeDeRham.hypercohomology ℂ X f 2 ≃ₗ[ℂ]
      RationalComplexification.Space (SingularCochains.Cohomology T 2))
    (α : SingularCochains.Cohomology T 2) :
    α ∈ SchemeDeRham.rationalBettiHodgeClasses f T 2 comparison p ↔
      comparison.symm (RationalComplexification.embedding _ α) ∈
        SchemeDeRham.hodgeFiltration ℂ X f 2 p :=
  SchemeDeRham.mem_rationalBettiHodgeClasses f T 2 comparison p α

end FilteredHodgeTargetVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.RationalComplexification.embedding_injective,
      `HodgeConjecture.RationalComplexification.conjugation_smul,
      `HodgeConjecture.RationalComplexification.conjugation_involutive,
      `HodgeConjecture.RationalComplexification.conjugation_map,
      `HodgeConjecture.HodgeFiltration.rationalHodgeClasses,
      `HodgeConjecture.HodgeFiltration.mem_rationalHodgeClasses_iff,
      `HodgeConjecture.HodgeFiltration.map_mem_rationalHodgeClasses,
      `HodgeConjecture.PureRationalHodgeStructure.piece,
      `HodgeConjecture.PureRationalHodgeStructure.mem_rationalHodgeClasses,
      `HodgeConjecture.HodgeFiltration.target_iff,
      `HodgeConjecture.PureRationalHodgeStructure.cycleClassModel,
      `HodgeConjecture.SchemeDeRham.bettiHodgeFiltration,
      `HodgeConjecture.SchemeDeRham.bettiHodgeFiltration_antitone,
      `HodgeConjecture.SchemeDeRham.mem_rationalBettiHodgeClasses,
      `FilteredHodgeTargetVerification.coordinateTarget] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
