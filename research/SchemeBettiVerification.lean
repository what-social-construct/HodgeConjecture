module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The scheme topology is defined from regular functions, independently of
the affine and P¹ models. Controls check actual base compatibility and
separate affine coordinates. The P¹ tests retain the original scheme
sections, cohomology pullbacks, geometric filtration and Chern period.
No general comparison or purity premise is introduced by these tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SchemeBettiVerification

open HodgeConjecture AlgebraicGeometry CategoryTheory
open scoped Polynomial TensorProduct

/-- Being over the identity base leaves exactly the identity scheme section. -/
theorem complexBase_subsingleton :
    Subsingleton (Scheme.ComplexPoints (𝟙 (Spec (.of ℂ)))) := by
  constructor
  intro p q
  apply Scheme.ComplexPoints.ext
  have hp : p.hom = 𝟙 _ := by simpa using p.hom_comp
  have hq : q.hom = 𝟙 _ := by simpa using q.hom_comp
  exact hp.trans hq.symm

/-- A ring map must fix the complex base: conjugation is excluded. -/
theorem conjugation_not_baseSection :
    Spec.map (CommRingCat.ofHom Complex.conjAe.toRingEquiv.toRingHom) ≫
      𝟙 (Spec (.of ℂ)) ≠ 𝟙 _ := by
  intro h
  have hc := congrArg Spec.preimage h
  simp only [Category.comp_id, Spec.preimage_map, Spec.preimage_id] at hc
  have hi := congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ (f Complex.I).im) hc
  change (-Complex.I).im = Complex.I.im at hi
  norm_num at hi

/-- The canonical affine point space retains distinct complex coordinate values. -/
theorem affine_zero_ne_one :
    AffineComplexPoints.ofAlgHom ℂ[X] (AffineLineComplexPoints.evalPoint 0) ≠
      AffineComplexPoints.ofAlgHom ℂ[X] (AffineLineComplexPoints.evalPoint 1) := by
  intro h
  have hc := congrArg (fun p ↦ AffineComplexPoints.toAlgHom ℂ[X] p Polynomial.X) h
  simp at hc

/-- A proper filtration, used only as a transport control and not asserted to be pure. -/
def coordinateFiltration (_ : ℤ) :
    Submodule ℂ (RationalComplexification.Space (ℚ × ℚ)) :=
  LinearMap.ker (RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ))

/-- A nonidentity rational equivalence changes which coordinate belongs to the target. -/
theorem swappedFiltration_excludes_firstCoordinate :
    ((1, 0) : ℚ × ℚ) ∉ HodgeFiltration.rationalHodgeClasses
      (fun k ↦ (coordinateFiltration k).map
        (LinearEquiv.baseChange ℚ ℂ _ _ (LinearEquiv.prodComm ℚ ℚ ℚ)).toLinearMap) 1 := by
  rw [HodgeFiltration.mem_rationalHodgeClasses_map,
    HodgeFiltration.mem_rationalHodgeClasses_iff]
  change ¬ RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ)
    (RationalComplexification.embedding (ℚ × ℚ) (0, 1)) = 0
  rw [RationalComplexification.map_embedding]
  intro h
  exact one_ne_zero (RationalComplexification.embedding_injective ℚ (by simpa using h))

/-- Every original finite P¹ point keeps its actual scheme morphism. -/
example (z : ℂ) :
    (ProjectiveLineComplexPoints.canonicalHomeomorph (ProjectiveLineComplexPoints.finite z)).hom =
      ProjectiveLineComplexPoints.schemeMorphism (ProjectiveLineComplexPoints.finite z) := rfl

/-- The actual infinity section is retained too. -/
example :
    (ProjectiveLineComplexPoints.canonicalHomeomorph ProjectiveLineComplexPoints.infinity).hom =
      ProjectiveLineComplexPoints.schemeMorphism ProjectiveLineComplexPoints.infinity := rfl

/-- The rational equivalence is induced by the original continuous inverse homeomorphism. -/
example (n : ℕ) : (ProjectiveLineCanonicalComparison.bettiEquiv n).toLinearMap =
    (SingularCochains.cohomologyPullback
      (TopCat.ofHom ProjectiveLineComplexPoints.canonicalHomeomorph.symm) n).hom := rfl

/-- The new target adapter contains the proved geometric P¹ pure structure. -/
example : ProjectiveLineCanonicalComparison.rationalHodgeClasses =
    PureRationalHodgeStructure.rationalHodgeClasses 1
      ProjectiveLineCanonicalComparison.pureHodgeStructure :=
  ProjectiveLineCanonicalComparison.rationalHodgeClasses_eq_pureStructure

/-- The actual unnormalized Chern period is still 2πi, not coefficient one. -/
example :
    ProjectiveLineCanonicalComparison.comparison (ProjectiveLineDeRham.schemeChernCoordinate ℂ) =
      (2 * Real.pi * Complex.I) ⊗ₜ[ℚ]
        ProjectiveLineCanonicalComparison.bettiEquiv 2 ProjectiveLineBettiCohomology.coverGenerator :=
  ProjectiveLineCanonicalComparison.comparison_chernCoordinate

end SchemeBettiVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `AlgebraicGeometry.Scheme.ComplexPoints.instTopologicalSpace,
      `AlgebraicGeometry.Scheme.ComplexPoints.isOpen_setOf_mem,
      `AlgebraicGeometry.Scheme.ComplexPoints.eval_constHom,
      `AlgebraicGeometry.Scheme.ComplexPoints.eval_ofRingHom,
      `AlgebraicGeometry.Scheme.ComplexPoints.isClosedEmbedding_evalMap,
      `AlgebraicGeometry.Scheme.ComplexPoints.continuous_eval_of_isOpen,
      `AlgebraicGeometry.Scheme.ComplexPoints.continuous_map,
      `AlgebraicGeometry.Scheme.ComplexPoints.isOpenEmbedding_map_of_isOpenImmersion,
      `AlgebraicGeometry.Scheme.ComplexPoints.isClosedEmbedding_map_of_isClosedImmersion,
      `AlgebraicGeometry.Scheme.ComplexPoints.homeomorphZeroLocus,
      `HodgeConjecture.AffineComplexPoints.eval_ofAlgHom,
      `HodgeConjecture.AffineComplexPoints.homeomorph,
      `HodgeConjecture.SchemeBetti.complexPointsFunctor,
      `HodgeConjecture.SchemeBetti.pullback_id,
      `HodgeConjecture.SchemeBetti.pullback_comp,
      `HodgeConjecture.SchemeBetti.cohomologyFunctor,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalHomeomorph,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalHomeomorph_schemeMorphism,
      `HodgeConjecture.RationalComplexification.conjugateSubmodule_map,
      `HodgeConjecture.HodgeFiltration.mem_rationalHodgeClasses_map,
      `HodgeConjecture.PureRationalHodgeStructure.transport,
      `HodgeConjecture.PureRationalHodgeStructure.mem_rationalHodgeClasses_transport,
      `HodgeConjecture.SchemeDeRham.mem_complexPointsRationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.bettiEquiv,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.comparison,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.boundaryPeriod_comparison,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.comparison_chernCoordinate,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.geometricFiltration_eq_map,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.pureHodgeStructure,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.pureHodgeStructure_filtration,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.rationalHodgeClasses_eq_pureStructure,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.mem_rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.normalizedComparison_cycleClass,
      `HodgeConjecture.ProjectiveLineCanonicalComparison.comparison_cycleClass,
      `SchemeBettiVerification.complexBase_subsingleton,
      `SchemeBettiVerification.conjugation_not_baseSection,
      `SchemeBettiVerification.affine_zero_ne_one,
      `SchemeBettiVerification.swappedFiltration_excludes_firstCoordinate] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
