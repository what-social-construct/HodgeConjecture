module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace GlobalSingularSheafVerification

open AlgebraicGeometry CategoryTheory HodgeConjecture

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

/-- All canonical affine dimensions use the original proved coordinate topology. -/
theorem affine_surjective (d n : ℕ) :
    Function.Surjective ((SingularCochains.globalCochainsToSheaf (SchemeBetti.space (affineBase d))).f n) := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : ParacompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.paracompactSpace d
  exact Scheme.ComplexPoints.singularGlobalCochainsToSheaf_surjective n

theorem affine_comparison (d : ℕ) :
    QuasiIso (SingularCochains.globalCochainsToSheaf (SchemeBetti.space (affineBase d))) := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : ParacompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.paracompactSpace d
  exact Scheme.ComplexPoints.singularGlobalCochainsToSheaf_quasiIso

/-- The original glued projective line satisfies the actual topological hypotheses. -/
theorem projectiveLine_surjective (n : ℕ) :
    Function.Surjective ((SingularCochains.globalCochainsToSheaf
      (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ)))).f n) := by
  let : T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalT2Space
  let : ParacompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalParacompactSpace
  exact Scheme.ComplexPoints.singularGlobalCochainsToSheaf_surjective n

theorem projectiveLine_comparison :
    QuasiIso (SingularCochains.globalCochainsToSheaf
      (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ)))) := by
  let : T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalT2Space
  let : ParacompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalParacompactSpace
  exact Scheme.ComplexPoints.singularGlobalCochainsToSheaf_quasiIso

/-- The construction also covers the empty-space boundary without choosing a global index. -/
theorem empty_comparison :
    QuasiIso (SingularCochains.globalCochainsToSheaf (TopCat.of Empty)) :=
  SingularCochains.globalCochainsToSheaf_quasiIso _

example : QuasiIso (SingularCochains.globalCochainsToSheaf (SchemeBetti.space (affineBase 0))) :=
  affine_comparison 0

end GlobalSingularSheafVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.toSheafify_exists_local_lift,
      `HodgeConjecture.SheafCohomology.toSheafify_germ_eq_iff,
      `HodgeConjecture.SheafCohomology.ComplexKernel.quasiIso_of_surjective_of_acyclic,
      `HodgeConjecture.SingularCochains.openExtension,
      `HodgeConjecture.SingularCochains.pullback_openExtension,
      `HodgeConjecture.SingularCochains.exists_locallyFinite_closed_refinement,
      `HodgeConjecture.SingularCochains.exists_cochain_locally_eq_of_closed_cover,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_restrict,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_germ_eq_iff,
      `HodgeConjecture.SingularCochains.exists_global_cochain_local_lift,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_surjective,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_quasiIso,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_homologyIso,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularGlobalCochainsToSheaf_surjective,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularGlobalCochainsToSheaf_quasiIso,
      `HodgeConjecture.PolynomialComplexPoints.t2Space,
      `HodgeConjecture.PolynomialComplexPoints.paracompactSpace,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalT2Space,
      `HodgeConjecture.ProjectiveLineComplexPoints.canonicalParacompactSpace,
      `GlobalSingularSheafVerification.affine_surjective,
      `GlobalSingularSheafVerification.affine_comparison,
      `GlobalSingularSheafVerification.projectiveLine_surjective,
      `GlobalSingularSheafVerification.projectiveLine_comparison,
      `GlobalSingularSheafVerification.empty_comparison] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
