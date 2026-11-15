module

public import HodgeConjecture.Realization.DeRham.HolomorphicAtlasComplex
public import HodgeConjecture.Geometry.Holomorphic.AtlasPoincare
public import HodgeConjecture.SheafCohomology.LocalExactness
public import HodgeConjecture.SheafCohomology.ConstantLift
public import HodgeConjecture.SheafCohomology.AugmentedComplex

@[expose] public section

/-!
# Intrinsic holomorphic de Rham comparison

The actual constant-sheaf augmentation is exact in degree zero and the
descended complex is exact in every positive degree. These follow from
the proved chart equivalence and the existing coordinate local Poincaré
lemmas. The same augmentation gives a full sheaf quasi-isomorphism.
No singular-cochain or proper algebraic/analytic comparison is assumed.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicAtlas

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The native constant presheaf, independent of the manifold atlas. -/
abbrev constantPresheaf (M : Type) [TopologicalSpace M] :=
  SheafCohomology.ConstantLift.presheaf ℂ (TopCat.of M)

/-- The native constant sheaf on the original topology. -/
abbrev constantSheaf (M : Type) [TopologicalSpace M] :=
  SheafCohomology.ConstantLift.sheaf ℂ (TopCat.of M)

def constantPresheafMap : constantPresheaf M ⟶ (formsSheaf E M 0).obj where
  app U := ModuleCat.ofHom (constant U.unop)
  naturality _ _ i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (restrict_constant (leOfHom i.unop) c).symm

/-- The actual augmentation, constructed by native sheafification. -/
def augmentation : constantSheaf M ⟶ formsSheaf E M 0 :=
  SheafCohomology.ConstantLift.lift (formsSheaf E M 0) (constantPresheafMap E M)

theorem toSheafify_augmentation :
    toSheafify _ _ ≫ (augmentation E M).hom = constantPresheafMap E M :=
  SheafCohomology.ConstantLift.toSheafify_lift (formsSheaf E M 0) (constantPresheafMap E M)

theorem augmentation_differential : augmentation E M ≫ sheafDifferential 0 = 0 := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (formsSheaf E M 1).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, toSheafify_augmentation]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact differential_constant U.unop c

instance augmentation_mono : Mono (augmentation E M) := by
  apply SheafCohomology.ConstantLift.mono
  intro U hU
  exact constant_injective U hU

def augmentedSequence := ShortComplex.mk (augmentation E M) (sheafDifferential 0)
  (augmentation_differential E M)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem augmentation_exact : (augmentedSequence E M).Exact := by
  apply SheafCohomology.LocalExactness.exact_of_exists_local_preimage
  intro U η hη p hp
  obtain ⟨W, hWU, hpW, c, hc⟩ := locally_constant_zero η hη ⟨p, hp⟩
  let σ := toSheafify (Opens.grothendieckTopology (TopCat.of M)) (constantPresheaf M)
  refine ⟨W, hWU, hpW, (σ.app (op W)) c, ?_⟩
  have h := congrArg (fun f : constantPresheaf M ⟶ (formsSheaf E M 0).obj ↦
    (f.app (op W)) c) (toSheafify_augmentation E M)
  exact h.trans hc.symm

/-- Intrinsic local exactness in every positive degree. -/
theorem exact_positive (n : ℕ) : (ShortComplex.mk
    (sheafDifferential (E := E) (M := M) n) (sheafDifferential (n + 1))
      (sheafDifferential_comp n)).Exact := by
  apply SheafCohomology.LocalExactness.exact_of_exists_local_preimage
  intro U η hη p hp
  exact locally_exact_positive n η hη ⟨p, hp⟩

/-- A genuine map from the native constant sheaf in degree zero. -/
def comparison : (CochainComplex.single₀ _).obj (constantSheaf M) ⟶ complex E M :=
  SheafCohomology.AugmentedComplex.comparison (constantSheaf M) (complex E M)
    (augmentation E M) (by simpa using augmentation_differential E M)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
@[simp]
theorem comparison_zero : (comparison E M).f 0 = augmentation E M :=
  SheafCohomology.AugmentedComplex.comparison_zero _ _ _ _

omit [IsScalarTower ℝ ℂ E] in
theorem comparison_quasiIsoAt_zero : QuasiIsoAt (comparison E M) 0 := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIsoAt_zero
  simpa only [complex_d, augmentedSequence] using augmentation_exact E M

theorem complex_exactAt_positive (n : ℕ) : (complex E M).ExactAt (n + 1) := by
  rw [(complex E M).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((complex E M).d n (n + 1)) ((complex E M).d (n + 1) (n + 2)) _).Exact
  simpa only [complex_d] using exact_positive E M n

theorem comparison_quasiIsoAt_positive (n : ℕ) : QuasiIsoAt (comparison E M) (n + 1) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIsoAt_positive
  exact complex_exactAt_positive E M n

/-- The intrinsic holomorphic de Rham comparison is a full sheaf quasi-isomorphism. -/
theorem comparison_quasiIso : QuasiIso (comparison E M) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIso
  · simpa only [complex_d, augmentedSequence] using augmentation_exact E M
  · exact complex_exactAt_positive E M

end HodgeConjecture.HolomorphicAtlas
