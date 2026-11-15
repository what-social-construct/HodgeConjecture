module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace SheafificationKernelVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace HodgeConjecture

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

/-- All dimensions, including zero, use the same original canonical point topology. -/
theorem affine_kernel (d : ℕ) :
    (Scheme.ComplexPoints.singularSheafificationKernel (x := affineBase d)).Acyclic :=
  Scheme.ComplexPoints.singularSheafificationKernel_acyclic

/-- The original glued projective line uses that same native categorical kernel. -/
theorem projectiveLine_kernel :
    (Scheme.ComplexPoints.singularSheafificationKernel
      (x := projectiveLine ℂ ↘ Spec (.of ℂ))).Acyclic :=
  Scheme.ComplexPoints.singularSheafificationKernel_acyclic

/-- The map retains nonzero constants; its kernel is not the whole singular complex. -/
theorem constant_survives :
    (SingularCochains.globalCochainsToSheaf (TopCat.of ℝ)).f 0
      (SingularCochains.constantCochain (TopCat.of ℝ) 1) ≠ 0 := by
  intro h
  have hzero := SingularCochains.LocallyZero.eq_zero (TopCat.of ℝ)
    ((SingularCochains.globalCochainsToSheaf_eq_zero_iff (TopCat.of ℝ) 0 _).mp h)
  have he : SingularCochains.constantCochain (TopCat.of ℝ) 1 =
      SingularCochains.constantCochain (TopCat.of ℝ) 0 := by simpa only [map_zero] using hzero
  exact one_ne_zero (SingularCochains.constantCochain_injective (TopCat.of ℝ) he)

/-- Local witnesses require no nonempty-space or nonempty-cover hypothesis. -/
theorem empty_locallyZero (n : ℕ) (φ : SingularCochains.Cochain (TopCat.of Empty) n) :
    SingularCochains.LocallyZero (TopCat.of Empty) n φ := fun x ↦ x.elim

example : (Scheme.ComplexPoints.singularSheafificationKernel (x := affineBase 0)).Acyclic :=
  affine_kernel 0

end SheafificationKernelVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.toSheafify_app_eq_zero_iff,
      `HodgeConjecture.SheafCohomology.ComplexKernel.degree_exact,
      `HodgeConjecture.SheafCohomology.ComplexKernel.range_inclusion,
      `HodgeConjecture.SheafCohomology.ComplexKernel.exists_preimage,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_apply,
      `HodgeConjecture.SingularCochains.restrict_top_cochain,
      `HodgeConjecture.SingularCochains.LocallyZero,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_eq_zero_iff,
      `HodgeConjecture.SingularCochains.restrict_open_eq_zero_iff_subset,
      `HodgeConjecture.SingularCochains.locallyZero_of_cover,
      `HodgeConjecture.SingularCochains.exists_point_cover_of_locallyZero,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_eq_zero_iff_cover,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf_ker_eq_iSup,
      `HodgeConjecture.SingularCochains.LocallyZero.differential,
      `HodgeConjecture.SingularCochains.LocallyZero.eq_zero,
      `HodgeConjecture.SingularCochains.exists_locallyZero_primitive,
      `HodgeConjecture.SingularCochains.kernelInclusion_locallyZero,
      `HodgeConjecture.SingularCochains.mem_range_kernelInclusion_iff,
      `HodgeConjecture.SingularCochains.exists_kernel_preimage,
      `HodgeConjecture.SingularCochains.kernel_zero_isZero,
      `HodgeConjecture.SingularCochains.exists_kernel_primitive,
      `HodgeConjecture.SingularCochains.sheafificationKernel_acyclic,
      `HodgeConjecture.SingularCochains.kernel_homology_isZero,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularSheafificationKernel_acyclic,
      `SheafificationKernelVerification.affine_kernel,
      `SheafificationKernelVerification.projectiveLine_kernel,
      `SheafificationKernelVerification.constant_survives,
      `SheafificationKernelVerification.empty_locallyZero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
