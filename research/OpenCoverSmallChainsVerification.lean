module

public import HodgeConjecture.Realization.Betti.CoverSmallCochains
public import HodgeConjecture.Realization.Betti.SingularSheafificationKernel
public import HodgeConjecture.Realization.Betti.SingularSheafGlobalSections
public import Mathlib.Topology.EMetricSpace.Paracompact
public import HodgeConjecture.Realization.Betti.AffineSingularRealization
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace OpenCoverSmallChainsVerification

open CategoryTheory Opposite Convexity HodgeConjecture SingularSubcomplexes
open scoped Simplicial

abbrev realSpace := TopCat.of ℝ

/-- A genuinely infinite open cover: unit balls centered at all real numbers. -/
def unitBalls (r : ℝ) : Set realSpace := Metric.ball r 1

theorem unitBalls_open (r : ℝ) : IsOpen (unitBalls r) := Metric.isOpen_ball

theorem unitBalls_cover : ⋃ r, unitBalls r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨x, by simp [unitBalls]⟩

/-- The cover cannot be replaced by a finite subcover of the entire space. -/
theorem unitBalls_no_finite_subcover (F : Finset ℝ) :
    (⋃ r ∈ F, unitBalls r) ≠ Set.univ := by
  intro hcover
  let x := F.sum (fun r ↦ |r|) + 2
  have hx : x ∈ ⋃ r ∈ F, unitBalls r := by rw [hcover]; trivial
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hrF, hxr⟩ := Set.mem_iUnion.mp hr
  have hsum : |r| ≤ F.sum (fun r ↦ |r|) :=
    Finset.single_le_sum (fun r _ ↦ abs_nonneg r) hrF
  have hdist : |x - r| < 1 := by simpa only [unitBalls, Metric.mem_ball, Real.dist_eq] using hxr
  have hlin := lt_of_le_of_lt (le_abs_self (x - r)) hdist
  have hrle := le_abs_self r
  dsimp only [x] at hlin
  linarith

def longEdge : SingularCochains.Simplex realSpace 1 :=
  AffineSingularRealization.simplex 1 ![0, 3]

def triangle : SingularCochains.Simplex realSpace 2 :=
  AffineSingularRealization.simplex 2 ![0, 3, 6]

/-- The original long simplex is not small for this actual cover. -/
theorem longEdge_not_small : longEdge ∉ (coverSingular realSpace unitBalls).obj (op ⦋1⦌) := by
  rw [mem_coverSingular_iff_range]
  rintro ⟨r, hr⟩
  have hv (j : Fin 2) : dist (![0, 3] j : ℝ) r < 1 := by
    have h := hr ⟨StdSimplex.single j, rfl⟩
    change dist ((TopCat.toSSetObjEquiv (TopCat.of ℝ) (op ⦋1⦌))
      (AffineSingularRealization.simplex (E := ℝ) 1 ![0, 3]) (StdSimplex.single j)) r < 1 at h
    rwa [AffineSingularRealization.simplex_continuous,
      SubdivisionGeometry.realization_single] at h
  have h0 : dist (0 : ℝ) r < 1 := hv 0
  have h3 : dist (3 : ℝ) r < 1 := hv 1
  have hd : dist (0 : ℝ) 3 < 2 := calc
    dist (0 : ℝ) 3 ≤ dist 0 r + dist r 3 := dist_triangle _ _ _
    _ < 1 + 1 := add_lt_add h0 (by rwa [dist_comm])
    _ = 2 := by norm_num
  norm_num at hd

def edgeChain : (SingularSubdivision.complex realSpace).X 1 :=
  SingularChainCoordinates.coordinates (TopCat.toSSet.obj realSpace) 1 (Finsupp.single longEdge 1)

theorem edgeChain_not_small : edgeChain ∉ coverChains realSpace unitBalls 1 := by
  intro h
  have hs := (SubcomplexChainCoordinates.mem_chainSubmodule_iff_support
    (coverSingular realSpace unitBalls) 1 edgeChain).mp h
  change ∀ σ ∈ ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj realSpace) 1).symm
    ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj realSpace) 1)
      (Finsupp.single longEdge 1))).support, σ ∈ _ at hs
  rw [LinearEquiv.symm_apply_apply] at hs
  exact longEdge_not_small (hs longEdge (by simp))

/-- A positive number of genuine subdivision steps is necessary and sufficient here. -/
theorem actual_positive_iteration :
    ∃ k : ℕ, 0 < k ∧ SingularSubdivisionSmallness.iteration realSpace 1 k edgeChain ∈
      coverChains realSpace unitBalls 1 := by
  obtain ⟨k, hk⟩ := CoverSubdivision.exists_iteration_small realSpace unitBalls
    unitBalls_open unitBalls_cover 1 edgeChain
  refine ⟨k, ?_, hk⟩
  by_contra h
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
  subst k
  exact edgeChain_not_small hk

theorem infinite_cover_chain_comparison : QuasiIso (coverInclusion realSpace unitBalls) :=
  CoverSmallChains.inclusion_quasiIso realSpace unitBalls unitBalls_open unitBalls_cover

theorem infinite_cover_cochain_comparison :
    QuasiIso (CoverSmallCochains.restriction realSpace unitBalls) :=
  CoverSmallCochains.restriction_quasiIso realSpace unitBalls unitBalls_open unitBalls_cover

def edgeDetector : SingularCochains.Cochain realSpace 1 := by
  classical
  exact fun σ ↦ if σ = longEdge then 1 else 0

theorem detector_nonzero : edgeDetector ≠ 0 := by
  intro h
  have he := congrFun h longEdge
  simp [edgeDetector] at he

theorem detector_restrict_zero :
    (CoverSmallCochains.restriction realSpace unitBalls).f 1 edgeDetector = 0 := by
  classical
  funext σ
  have hne : σ.val ≠ longEdge := by
    intro he
    exact longEdge_not_small (he ▸ σ.property)
  change (if σ.val = longEdge then (1 : ℚ) else 0) = 0
  exact ite_eq_right hne

theorem triangle_face (i : Fin 3) : SingularCochains.face realSpace triangle i =
    AffineSingularRealization.simplex 1 (AffineSimplexChains.face ![0, 3, 6] i) :=
  AffineSingularRealization.simplex_face 1 ![0, 3, 6] i

/-- The actual differential of the vanishing detector is nonzero. -/
theorem detector_differential_value :
    SingularCochains.differential realSpace 1 edgeDetector triangle = 1 := by
  have hf0 : SingularCochains.face realSpace triangle 0 ≠ longEdge := by
    rw [triangle_face]
    intro h
    have hv := (AffineSingularRealization.simplex_injective (E := ℝ) 1) h
    have he := congrFun hv 0
    norm_num [AffineSimplexChains.face, Fin.removeNth] at he
  have hf1 : SingularCochains.face realSpace triangle 1 ≠ longEdge := by
    rw [triangle_face]
    intro h
    have hv := (AffineSingularRealization.simplex_injective (E := ℝ) 1) h
    have he := congrFun hv 1
    norm_num [AffineSimplexChains.face, Fin.removeNth] at he
  have hf2 : SingularCochains.face realSpace triangle 2 = longEdge := by
    rw [triangle_face]
    have hv : AffineSimplexChains.face (![0, 3, 6] : Fin 3 → ℝ) 2 = ![0, 3] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    rfl
  rw [SingularCochains.differential_apply, Fin.sum_univ_three]
  norm_num [edgeDetector, hf0, hf1, hf2]


def vanishingDetector : RelativeCochains.Cochain (coverSingular realSpace unitBalls) 1 :=
  ⟨edgeDetector, detector_restrict_zero⟩

def closedVanishingDetector : RelativeCochains.Cochain (coverSingular realSpace unitBalls) 2 :=
  RelativeCochains.differential _ 1 vanishingDetector

theorem closedVanishingDetector_nonzero : closedVanishingDetector ≠ 0 := by
  intro h
  have he := congrArg (fun z : RelativeCochains.Cochain (coverSingular realSpace unitBalls) 2 ↦
    z.val triangle) h
  change SingularCochains.differential realSpace 1 edgeDetector triangle = 0 at he
  rw [detector_differential_value] at he
  exact one_ne_zero he

/-- The comparison supplies a primitive still vanishing on the same infinite cover. -/
theorem actual_vanishing_primitive :
    ∃ b : RelativeCochains.Cochain (coverSingular realSpace unitBalls) 1,
      RelativeCochains.differential _ 1 b = closedVanishingDetector := by
  apply CoverSmallCochains.exists_vanishing_primitive realSpace unitBalls
    unitBalls_open unitBalls_cover 1 closedVanishingDetector
  exact LinearMap.congr_fun (RelativeCochains.differential_squared _ 1) vanishingDetector

/-- An empty indexed cover is allowed on the empty space, including degree zero. -/
theorem empty_space_comparison : QuasiIso (CoverSmallCochains.restriction (TopCat.of Empty)
    (fun i : Empty ↦ i.elim)) := by
  apply CoverSmallCochains.restriction_quasiIso
  · intro i; exact i.elim
  · ext x; exact x.elim

end OpenCoverSmallChainsVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.NativeSimplexGeometry.lebesgue_number_diam,
      `HodgeConjecture.SubcomplexChainCoordinates.map_mem_chainSubmodule,
      `HodgeConjecture.SubcomplexChainCoordinates.restrictOperator,
      `HodgeConjecture.SubcomplexChainCoordinates.restrictMap,
      `HodgeConjecture.SubcomplexChainCoordinates.restrictHomotopy,
      `HodgeConjecture.SingularSubdivision.realize_mem_chainSubmodule,
      `HodgeConjecture.SingularSubcomplexes.coverSingular,
      `HodgeConjecture.SingularSubcomplexes.coverSingular_bool,
      `HodgeConjecture.SingularSubcomplexes.zeroSimplex_mem_coverSingular,
      `HodgeConjecture.CoverSubdivision.exists_iteration_small,
      `HodgeConjecture.CoverSubdivision.subdivisionHomotopy,
      `HodgeConjecture.CoverSmallChains.inclusion_quasiIso,
      `HodgeConjecture.CoverSmallChains.homologyIso,
      `HodgeConjecture.CoverSmallChains.refinementMap_inclusion,
      `HodgeConjecture.CoverSmallChains.refinementMap_quasiIso,
      `HodgeConjecture.CoverSmallCochains.restriction_quasiIso,
      `HodgeConjecture.CoverSmallCochains.restriction_surjective,
      `HodgeConjecture.CoverSmallCochains.vanishingComplex_acyclic,
      `HodgeConjecture.CoverSmallCochains.exists_vanishing_primitive,
      `HodgeConjecture.CoverSmallCochains.refinementRestriction_quasiIso,
      `OpenCoverSmallChainsVerification.unitBalls_no_finite_subcover,
      `OpenCoverSmallChainsVerification.longEdge_not_small,
      `OpenCoverSmallChainsVerification.edgeChain_not_small,
      `OpenCoverSmallChainsVerification.actual_positive_iteration,
      `OpenCoverSmallChainsVerification.infinite_cover_chain_comparison,
      `OpenCoverSmallChainsVerification.infinite_cover_cochain_comparison,
      `OpenCoverSmallChainsVerification.detector_nonzero,
      `OpenCoverSmallChainsVerification.detector_restrict_zero,
      `OpenCoverSmallChainsVerification.detector_differential_value,
      `OpenCoverSmallChainsVerification.closedVanishingDetector_nonzero,
      `OpenCoverSmallChainsVerification.actual_vanishing_primitive,
      `OpenCoverSmallChainsVerification.empty_space_comparison] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

/-! The same infinite-cover fixtures now test the actual native global kernel. -/
namespace SheafificationKernelConcreteVerification

open CategoryTheory HodgeConjecture OpenCoverSmallChainsVerification

theorem detector_locallyZero : SingularCochains.LocallyZero realSpace 1 edgeDetector :=
  SingularCochains.locallyZero_of_cover realSpace
    (fun r ↦ ⟨unitBalls r, unitBalls_open r⟩) unitBalls_cover 1 edgeDetector detector_restrict_zero

theorem detector_unit_zero : (SingularCochains.globalCochainsToSheaf realSpace).f 1 edgeDetector = 0 :=
  (SingularCochains.globalCochainsToSheaf_eq_zero_iff realSpace 1 edgeDetector).mpr detector_locallyZero

def nativeDetector : (SingularCochains.sheafificationKernel realSpace).X 1 :=
  Classical.choose (SingularCochains.exists_kernel_preimage realSpace 1 edgeDetector detector_locallyZero)

theorem nativeDetector_inclusion :
    (SingularCochains.sheafificationKernelInclusion realSpace).f 1 nativeDetector = edgeDetector :=
  Classical.choose_spec (SingularCochains.exists_kernel_preimage realSpace 1 edgeDetector detector_locallyZero)

theorem nativeDetector_nonzero : nativeDetector ≠ 0 := by
  intro h
  apply detector_nonzero
  rw [← nativeDetector_inclusion, h, map_zero]

def nativeClosedDetector : (SingularCochains.sheafificationKernel realSpace).X 2 :=
  (SingularCochains.sheafificationKernel realSpace).d 1 2 nativeDetector

theorem nativeClosedDetector_inclusion :
    (SingularCochains.sheafificationKernelInclusion realSpace).f 2 nativeClosedDetector =
      SingularCochains.differential realSpace 1 edgeDetector := by
  change (SingularCochains.sheafificationKernelInclusion realSpace).f 2
    ((SingularCochains.sheafificationKernel realSpace).d 1 2 nativeDetector) = _
  rw [SheafCohomology.ComplexKernel.inclusion_d, nativeDetector_inclusion, SingularCochains.complex_d]
  rfl

theorem nativeClosedDetector_nonzero : nativeClosedDetector ≠ 0 := by
  intro h
  have he := congrArg (fun z : (SingularCochains.sheafificationKernel realSpace).X 2 ↦
    (SingularCochains.sheafificationKernelInclusion realSpace).f 2 z triangle) h
  rw [nativeClosedDetector_inclusion, map_zero] at he
  change SingularCochains.differential realSpace 1 edgeDetector triangle = 0 at he
  rw [detector_differential_value] at he
  exact one_ne_zero he

theorem nativeClosedDetector_closed :
    (SingularCochains.sheafificationKernel realSpace).d 2 3 nativeClosedDetector = 0 := by
  change ((SingularCochains.sheafificationKernel realSpace).d 2 3).hom
    (((SingularCochains.sheafificationKernel realSpace).d 1 2).hom nativeDetector) = 0
  have h := congrArg (fun q ↦ q.hom nativeDetector)
    ((SingularCochains.sheafificationKernel realSpace).d_comp_d 1 2 3)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

theorem actual_native_primitive :
    ∃ b : (SingularCochains.sheafificationKernel realSpace).X 1,
      (SingularCochains.sheafificationKernel realSpace).d 1 2 b = nativeClosedDetector :=
  SingularCochains.exists_kernel_primitive realSpace 1 nativeClosedDetector nativeClosedDetector_closed

end SheafificationKernelConcreteVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `SheafificationKernelConcreteVerification.detector_locallyZero,
      `SheafificationKernelConcreteVerification.detector_unit_zero,
      `SheafificationKernelConcreteVerification.nativeDetector_inclusion,
      `SheafificationKernelConcreteVerification.nativeDetector_nonzero,
      `SheafificationKernelConcreteVerification.nativeClosedDetector_inclusion,
      `SheafificationKernelConcreteVerification.nativeClosedDetector_nonzero,
      `SheafificationKernelConcreteVerification.nativeClosedDetector_closed,
      `SheafificationKernelConcreteVerification.actual_native_primitive] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

/-! The same noncompact infinite-cover example checks the actual global unit. -/
namespace GlobalSingularSheafConcreteVerification

open CategoryTheory HodgeConjecture OpenCoverSmallChainsVerification
open SheafificationKernelConcreteVerification

/-- The original real line needs no finite-cover assumption. -/
theorem real_global_comparison : QuasiIso (SingularCochains.globalCochainsToSheaf realSpace) :=
  SingularCochains.globalCochainsToSheaf_quasiIso _

/-- The actual unit still kills a nonzero cochain; the comparison is on cohomology. -/
theorem real_unit_not_injective :
    ¬ Function.Injective ((SingularCochains.globalCochainsToSheaf realSpace).f 1) := by
  intro h
  apply detector_nonzero
  apply h
  simpa only [map_zero] using detector_unit_zero

end GlobalSingularSheafConcreteVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `GlobalSingularSheafConcreteVerification.real_global_comparison,
      `GlobalSingularSheafConcreteVerification.real_unit_not_injective] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
