module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.SingularOpenRestriction
public import HodgeConjecture.Realization.Betti.SingularSheafAcyclicity
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace OpenSingularSheafVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HodgeConjecture

/-- Arbitrary sheafified sections on any real open have original ambient cochain lifts. -/
theorem real_open_lift (U : Opens (TopCat.of ℝ)) (n : ℕ)
    (s : (SingularCochains.cochainSheaf (TopCat.of ℝ) n).obj.obj (op U)) :
    ∃ φ : SingularCochains.Cochain (TopCat.of ℝ) n,
      (SingularCochains.cochainSheaf (TopCat.of ℝ) n).obj.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        ((SingularCochains.globalCochainsToSheaf (TopCat.of ℝ)).f n φ) = s :=
  SingularCochains.exists_global_cochain_open_lift _ U n s

theorem real_restrictions {V U : Opens (TopCat.of ℝ)} (hVU : V ≤ U) (n : ℕ) :
    Function.Surjective ((SingularCochains.cochainSheaf (TopCat.of ℝ) n).obj.map
      (homOfLE hVU).op) :=
  SingularCochains.cochainSheaf_restriction_surjective _ hVU n

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

/-- All dimensions use the existing point topology and existing cochain sheaf. -/
theorem affine_flasque (d n : ℕ) :
    (SingularCochains.cochainSheaf (SchemeBetti.space (affineBase d)) n).IsFlasque := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : LocallyCompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.locallyCompactSpace d
  let : SecondCountableTopology (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.secondCountableTopology d
  exact Scheme.ComplexPoints.singularCochainSheaf_isFlasque n

theorem affine_restrictions (d n : ℕ) {V U : Opens (SchemeBetti.space (affineBase d))}
    (hVU : V ≤ U) :
    Function.Surjective ((SingularCochains.cochainSheaf (SchemeBetti.space (affineBase d)) n).obj.map
      (homOfLE hVU).op) := by
  let : (SingularCochains.cochainSheaf (SchemeBetti.space (affineBase d)) n).IsFlasque :=
    affine_flasque d n
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

abbrev projectiveSpace := SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ))

/-- The same original glued P¹ has flasque singular cochain sheaves in every degree. -/
theorem projectiveLine_flasque (n : ℕ) :
    (SingularCochains.cochainSheaf projectiveSpace n).IsFlasque := by
  let : T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalT2Space
  let : LocallyCompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
  let : SecondCountableTopology (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalSecondCountableTopology
  exact Scheme.ComplexPoints.singularCochainSheaf_isFlasque n

theorem projectiveLine_restrictions (n : ℕ) {V U : Opens projectiveSpace} (hVU : V ≤ U) :
    Function.Surjective ((SingularCochains.cochainSheaf projectiveSpace n).obj.map
      (homOfLE hVU).op) := by
  let : (SingularCochains.cochainSheaf projectiveSpace n).IsFlasque := projectiveLine_flasque n
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The actual canonical affine chart is an open subspace of the compact projective line. -/
def projectiveZeroChart : Opens projectiveSpace :=
  ⟨Set.range ProjectiveLineComplexPoints.canonicalXChart,
    ProjectiveLineComplexPoints.isOpenEmbedding_canonicalXChart.isOpen_range⟩

/-- Restriction is tested on a genuinely noncompact open, rather than only compact subspaces. -/
theorem projectiveZeroChart_not_compact : ¬ IsCompact (projectiveZeroChart : Set projectiveSpace) := by
  intro h
  have hchart : (projectiveZeroChart : Set projectiveSpace) =
      Set.range ProjectiveLineComplexPoints.canonicalXChart := rfl
  rw [hchart] at h
  have ha : IsCompact (Set.univ : Set AffineLineComplexPoints.Point) :=
    ProjectiveLineComplexPoints.isOpenEmbedding_canonicalXChart.isEmbedding.isCompact_iff.mpr
      (by simpa only [Set.image_univ] using h)
  apply noncompact_univ ℂ
  simpa only [Set.image_univ, AffineLineComplexPoints.coordinateHomeomorph.surjective.range_eq] using
    ha.image AffineLineComplexPoints.coordinateHomeomorph.continuous

theorem projectiveZeroChart_restriction (n : ℕ) :
    Function.Surjective ((SingularCochains.cochainSheaf projectiveSpace n).obj.map
      (homOfLE (show projectiveZeroChart ≤ ⊤ from le_top)).op) :=
  projectiveLine_restrictions n le_top

theorem empty_flasque (n : ℕ) :
    (SingularCochains.cochainSheaf (TopCat.of Empty) n).IsFlasque :=
  SingularCochains.cochainSheaf_isFlasque_of_locallyCompact_secondCountable _ n

example : (SingularCochains.cochainSheaf (SchemeBetti.space (affineBase 0)) 0).IsFlasque :=
  affine_flasque 0 0

end OpenSingularSheafVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.openEmbedding_isCocontinuous,
      `HodgeConjecture.SheafCohomology.sheafifyOpenIso,
      `HodgeConjecture.SheafCohomology.toSheafify_sheafifyOpenIso,
      `HodgeConjecture.SheafCohomology.toSheafify_app_surjective_of_iso,
      `HodgeConjecture.SheafCohomology.toSheafify_app_surjective_of_restrict,
      `HodgeConjecture.SingularCochains.openPresheafIso,
      `HodgeConjecture.SingularCochains.toSheafify_open_surjective,
      `HodgeConjecture.SingularCochains.exists_global_cochain_open_lift,
      `HodgeConjecture.SingularCochains.cochainSheaf_restriction_surjective,
      `HodgeConjecture.SingularCochains.cochainSheaf_isFlasque,
      `HodgeConjecture.SingularCochains.cochainSheaf_isFlasque_of_locallyCompact_secondCountable,
      `HodgeConjecture.PolynomialComplexPoints.locallyCompactSpace,
      `HodgeConjecture.PolynomialComplexPoints.secondCountableTopology,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalCharts_isOpenQuotientMap,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalLocallyCompactSpace,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalSecondCountableTopology,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCochainSheaf_isFlasque,
      `OpenSingularSheafVerification.real_open_lift,
      `OpenSingularSheafVerification.real_restrictions,
      `OpenSingularSheafVerification.affine_flasque,
      `OpenSingularSheafVerification.affine_restrictions,
      `OpenSingularSheafVerification.projectiveLine_flasque,
      `OpenSingularSheafVerification.projectiveLine_restrictions,
      `OpenSingularSheafVerification.projectiveZeroChart_not_compact,
      `OpenSingularSheafVerification.projectiveZeroChart_restriction,
      `OpenSingularSheafVerification.empty_flasque] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

/-! The same noncompact canonical chart tests actual positive derived sections. -/
namespace SingularSheafAcyclicityConcreteVerification

open CategoryTheory CategoryTheory.Limits HodgeConjecture OpenSingularSheafVerification

/-- The original sheaf term has zero positive cohomology on this same noncompact chart. -/
theorem projectiveZeroChart_higher_cohomology (q n : ℕ) (hn : 0 < n) :
    IsZero (SheafCohomology.TwoOpenModules.Hobj ℚ (𝟭 _) projectiveZeroChart n
      (SingularCochains.cochainSheaf projectiveSpace q)) := by
  let : (SingularCochains.cochainSheaf projectiveSpace q).IsFlasque := projectiveLine_flasque q
  exact SheafCohomology.LinearCoefficients.isZero_cohomology_of_isFlasque ℚ projectiveSpace _
    projectiveZeroChart n hn

end SingularSheafAcyclicityConcreteVerification

open Lean Elab Command in
run_cmd do
  let declaration := `SingularSheafAcyclicityConcreteVerification.projectiveZeroChart_higher_cohomology
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let env ← Lean.getEnv
  unless (env.find? declaration).isSome do
    throwError "Missing declaration {declaration}"
  let axioms ← Lean.collectAxioms declaration
  for axiomName in axioms.toList do
    unless permitted.contains axiomName do
      throwError "Unexpected axiom {axiomName} in {declaration}"
  logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
