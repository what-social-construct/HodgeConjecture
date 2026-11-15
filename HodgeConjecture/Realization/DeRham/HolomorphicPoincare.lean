module

public import HodgeConjecture.Realization.DeRham.HolomorphicComplex
public import HodgeConjecture.Geometry.Holomorphic.Poincare
public import HodgeConjecture.Geometry.Holomorphic.Dimension
public import HodgeConjecture.SheafCohomology.LocalExactness
public import HodgeConjecture.SheafCohomology.AugmentedComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

/-!
# The actual constant-to-holomorphic local comparison

The augmentation is exact in degree zero and the actual complex is exact
in every positive degree in every coordinate dimension. The radial
homotopy proves the full local Poincaré comparison for the existing
holomorphic forms. Identification with scheme analytic atlases remains
a separate construction.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HolomorphicForms

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The original constant augmentation followed by the actual exterior derivative. -/
def augmentedSequence := ShortComplex.mk (augmentation E) (differential E 0)
  (augmentation_differential E)

omit [IsScalarTower ℝ ℂ E] in
/-- The augmentation kernel comparison is proved using actual locally constant sections. -/
theorem augmentation_exact : (augmentedSequence E).Exact := by
  apply SheafCohomology.LocalExactness.exact_of_exists_local_preimage
  intro U η hη x hx
  obtain ⟨V, hVU, hxV, c, hc⟩ := locally_constant_zero η hη ⟨x, hx⟩
  let σ := toSheafify (Opens.grothendieckTopology (TopCat.of E)) (constantPresheaf E)
  refine ⟨V, hVU, hxV, (σ.app (op V)) c, ?_⟩
  have he : (constant V c : Sections V 0) = restrict hVU 0 η := by
    apply (functionsEquiv V).injective
    apply ContMDiffMap.ext
    intro y
    exact (hc y).symm
  change (augmentation E).hom.app (op V) ((σ.app (op V)) c) = _
  have hh := congrArg (fun f : constantPresheaf E ⟶ (formsSheaf E 0).obj ↦
    (f.app (op V)) c) (toSheafify_augmentation E)
  exact hh.trans he

/-- Constants remain injective after the actual constant presheaf is sheafified. -/
instance augmentation_mono : Mono (augmentation E) := by
  have hinj : ∀ U : Opens (TopCat.of E), (U : Set E).Nonempty →
      Function.Injective ((constantPresheafMap E).app (op U)) := by
    intro U hU a b hab
    obtain ⟨x, hx⟩ := hU
    exact congrArg (fun η : Sections U 0 ↦ zeroCoeffEquiv (η ⟨x, hx⟩)) hab
  exact SheafCohomology.ConstantLift.mono (formsSheaf E 0) (constantPresheafMap E) hinj

/-- Local exactness for the actual sheaf complex in every positive degree. -/
theorem exact_positive (n : ℕ) : (ShortComplex.mk (differential E n) (differential E (n + 1))
    (differential_comp E n)).Exact := by
  apply SheafCohomology.LocalExactness.exact_of_exists_local_preimage
  intro U η hη x hx
  exact locally_exact_positive n η hη ⟨x, hx⟩

/-- Compatibility with the original degree-one local comparison. -/
theorem exact_one : (ShortComplex.mk (differential E 0) (differential E 1)
    (differential_comp E 0)).Exact := exact_positive E 0

/-- The comparison is a genuine map out of the constant sheaf concentrated in degree zero. -/
def comparison : (CochainComplex.single₀ _).obj (constantSheaf E) ⟶ complex E :=
  SheafCohomology.AugmentedComplex.comparison (constantSheaf E) (complex E)
    (augmentation E) (by simpa using augmentation_differential E)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
@[simp]
theorem comparison_zero : (comparison E).f 0 = augmentation E :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

omit [IsScalarTower ℝ ℂ E] in
/-- The constant comparison is a quasi-isomorphism in degree zero in every dimension. -/
theorem comparison_quasiIsoAt_zero : QuasiIsoAt (comparison E) 0 := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIsoAt_zero
  simpa only [complex_d, augmentedSequence] using augmentation_exact E

theorem complex_exactAt_positive (n : ℕ) : (complex E).ExactAt (n + 1) := by
  rw [(complex E).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((complex E).d n (n + 1)) ((complex E).d (n + 1) (n + 2)) _).Exact
  simpa only [complex_d] using exact_positive E n

theorem complex_exactAt_one : (complex E).ExactAt 1 := complex_exactAt_positive E 0

theorem comparison_quasiIsoAt_positive (n : ℕ) : QuasiIsoAt (comparison E) (n + 1) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIsoAt_positive
  exact complex_exactAt_positive E n

theorem comparison_quasiIsoAt_one : QuasiIsoAt (comparison E) 1 :=
  comparison_quasiIsoAt_positive E 0

/-- The full local holomorphic de Rham comparison in every coordinate dimension. -/
theorem comparison_quasiIso : QuasiIso (comparison E) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIso
  · simpa only [complex_d, augmentedSequence] using augmentation_exact E
  · exact complex_exactAt_positive E

/-- All the actual holomorphic sheaves above degree one vanish on the complex line. -/
theorem complexLine_formsSheaf_isZero (n : ℕ) (hn : 2 ≤ n) : IsZero (formsSheaf ℂ n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro η
  exact complexLine_section_eq_zero hn η

/-- Compatibility with the original complex-line comparison. -/
theorem complexLine_comparison_quasiIso : QuasiIso (comparison ℂ) := comparison_quasiIso ℂ

end HodgeConjecture.HolomorphicDeRham
