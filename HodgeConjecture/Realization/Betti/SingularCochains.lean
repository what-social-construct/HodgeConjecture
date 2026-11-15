module

public import HodgeConjecture.Realization.Betti.SingularDegreeZero
public import HodgeConjecture.Realization.Betti.SimplicialCochains
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

/-!
# Rational singular cochains in all degrees

The cochains are rational functions on Mathlib's actual singular simplicial
set. Precomposition makes these modules a cosimplicial object, whose
alternating coface complex is the singular cochain complex. Thus the
differential and its square-zero identity come from the singular face maps.
These constructions specialize the shared `SimplicialCochains` implementation.

The cohomology objects below are the categorical homology of this constructed
complex. Continuous maps induce cochain maps and cohomology pullbacks. No
calculation of the cohomology of a particular space is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SingularCochains

open CategoryTheory Simplicial Opposite

noncomputable section

universe u

/-- Compatibility name for the shared contravariant rational-function module. -/
def functionModule : (Type u)ᵒᵖ ⥤ ModuleCat.{u} ℚ :=
  SimplicialCochains.functionModule

/-- Actual singular simplices, including Mathlib's universe lift. -/
abbrev Simplex (X : TopCat.{u}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (op ⦋n⦌)

/-- Singular simplices are continuous maps from the standard real simplex. -/
def simplexEquivContinuous (X : TopCat.{u}) (n : ℕ) :
    Simplex X n ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv X (op ⦋n⦌)

/-- Unrestricted rational singular cochains in degree `n`. -/
abbrev Cochain (X : TopCat.{u}) (n : ℕ) :=
  SimplicialCochains.Cochain (TopCat.toSSet.obj X) n

/-- Rational functions on the singular set, as a genuine cosimplicial module. -/
def cosimplicial (X : TopCat.{u}) : CosimplicialObject (ModuleCat.{u} ℚ) :=
  SimplicialCochains.cosimplicial (TopCat.toSSet.obj X)

/-- The actual rational singular cochain complex. -/
def complex (X : TopCat.{u}) : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  SimplicialCochains.complex (TopCat.toSSet.obj X)

/-- The singular face restriction supplied by the singular simplicial set. -/
def face (X : TopCat.{u}) {n : ℕ} (σ : Simplex X (n + 1))
    (i : Fin (n + 2)) : Simplex X n :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ

/-- The differential is the alternating coface differential, on elements. -/
def differential (X : TopCat.{u}) (n : ℕ) : Cochain X n →ₗ[ℚ] Cochain X (n + 1) :=
  SimplicialCochains.differential (TopCat.toSSet.obj X) n

@[simp]
theorem complex_d (X : TopCat.{u}) (n : ℕ) :
    (complex X).d n (n + 1) = ModuleCat.ofHom (differential X n) :=
  SimplicialCochains.complex_d (TopCat.toSSet.obj X) n

/-- The coboundary evaluates as the alternating sum over the actual faces. -/
theorem differential_apply (X : TopCat.{u}) (n : ℕ)
    (φ : Cochain X n) (σ : Simplex X (n + 1)) :
    differential X n φ σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (face X σ i) :=
  SimplicialCochains.differential_apply (TopCat.toSSet.obj X) n φ σ

/-- The square-zero relation follows from the singular simplicial identities. -/
theorem differential_squared (X : TopCat.{u}) (n : ℕ) (φ : Cochain X n) :
    differential X (n + 1) (differential X n φ) = 0 :=
  SimplicialCochains.differential_squared (TopCat.toSSet.obj X) n φ

/-- Pullback of the cosimplicial module by an actual continuous map. -/
def cosimplicialPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    cosimplicial Y ⟶ cosimplicial X :=
  SimplicialCochains.cosimplicialPullback (TopCat.toSSet.map f)

/-- Continuous pullback on the actual singular cochain complex. -/
def pullback {X Y : TopCat.{u}} (f : X ⟶ Y) : complex Y ⟶ complex X :=
  SimplicialCochains.pullback (TopCat.toSSet.map f)

@[simp]
theorem pullback_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain Y n) (σ : Simplex X n) :
    (pullback f).f n φ σ = φ ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) := rfl

@[simp]
theorem pullback_id (X : TopCat.{u}) : pullback (𝟙 X) = 𝟙 (complex X) := by
  change SimplicialCochains.pullback (TopCat.toSSet.map (𝟙 X)) =
    𝟙 (SimplicialCochains.complex (TopCat.toSSet.obj X))
  rw [TopCat.toSSet.map_id]
  exact SimplicialCochains.pullback_id (TopCat.toSSet.obj X)

@[simp]
theorem pullback_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = pullback g ≫ pullback f := by
  simpa only [pullback, Functor.map_comp] using
    SimplicialCochains.pullback_comp (TopCat.toSSet.map f) (TopCat.toSSet.map g)

/-- Actual continuous pullback commutes with the singular coboundary. -/
theorem differential_pullback {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain Y n) :
    differential X n ((pullback f).f n φ) =
      (pullback f).f (n + 1) (differential Y n φ) :=
  SimplicialCochains.differential_pullback (TopCat.toSSet.map f) n φ

/-- Rational singular cohomology, as homology of the constructed cochain complex. -/
abbrev Cohomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℚ :=
  (complex X).homology n

/-- Continuous pullback on rational singular cohomology in every degree. -/
def cohomologyPullback {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    Cohomology Y n ⟶ Cohomology X n :=
  HomologicalComplex.homologyMap (pullback f) n

@[simp]
theorem cohomologyPullback_id (X : TopCat.{u}) (n : ℕ) :
    cohomologyPullback (𝟙 X) n = 𝟙 (Cohomology X n) := by
  simp [cohomologyPullback]

@[simp]
theorem cohomologyPullback_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    cohomologyPullback (f ≫ g) n = cohomologyPullback g n ≫ cohomologyPullback f n := by
  simp [cohomologyPullback, HomologicalComplex.homologyMap_comp]

/-- Continuous-map coordinates on all singular cochains. -/
def continuousCochainEquiv (X : Type u) [TopologicalSpace X] (n : ℕ) :
    Cochain (TopCat.of X) n ≃ₗ[ℚ] (SingularDegreeZero.Simplex X n → ℚ) where
  toFun φ σ := φ (SingularDegreeZero.simplexEquivSingularSet X n σ)
  invFun φ σ := φ ((SingularDegreeZero.simplexEquivSingularSet X n).symm σ)
  left_inv φ := by
    funext σ
    exact congrArg φ ((SingularDegreeZero.simplexEquivSingularSet X n).apply_symm_apply σ)
  right_inv φ := by
    funext σ
    exact congrArg φ ((SingularDegreeZero.simplexEquivSingularSet X n).symm_apply_apply σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The new pullback is ordinary precomposition on continuous singular simplices. -/
theorem continuousCochainEquiv_pullback {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (φ : Cochain (TopCat.of Y) n) (σ : SingularDegreeZero.Simplex X n) :
    continuousCochainEquiv X n ((pullback (TopCat.ofHom f)).f n φ) σ =
      continuousCochainEquiv Y n φ (f.comp σ) := rfl

/-- In degree zero the all-degree differential agrees with the existing one. -/
theorem differential_zero_coordinates (X : Type u) [TopologicalSpace X]
    (φ : Cochain (TopCat.of X) 0) :
    continuousCochainEquiv X 1 (differential (TopCat.of X) 0 φ) =
      SingularDegreeZero.coboundary X (continuousCochainEquiv X 0 φ) := by
  funext σ
  change differential (TopCat.of X) 0 φ
      (SingularDegreeZero.simplexEquivSingularSet X 1 σ) =
    φ (SingularDegreeZero.simplexEquivSingularSet X 0 (SingularDegreeZero.face X σ 0)) -
      φ (SingularDegreeZero.simplexEquivSingularSet X 0 (SingularDegreeZero.face X σ 1))
  rw [differential_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [SingularDegreeZero.simplexEquivSingularSet_face,
    SingularDegreeZero.simplexEquivSingularSet_face]
  simp only [face, sub_eq_add_neg]

/-- The kernel in degree zero recovers the established singular `H0`. -/
def kernelZeroCoordinates (X : Type u) [TopologicalSpace X] :
    LinearMap.ker (differential (TopCat.of X) 0) ≃ₗ[ℚ] SingularDegreeZero.H0 X where
  toFun φ := ⟨continuousCochainEquiv X 0 φ.val, by
    change SingularDegreeZero.coboundary X (continuousCochainEquiv X 0 φ.val) = 0
    rw [← differential_zero_coordinates, LinearMap.mem_ker.mp φ.property, map_zero]⟩
  invFun a := ⟨(continuousCochainEquiv X 0).symm a.val, by
    apply (continuousCochainEquiv X 1).injective
    rw [differential_zero_coordinates, map_zero, LinearEquiv.apply_symm_apply]
    exact a.property⟩
  left_inv φ := Subtype.ext ((continuousCochainEquiv X 0).symm_apply_apply φ.val)
  right_inv a := Subtype.ext ((continuousCochainEquiv X 0).apply_symm_apply a.val)
  map_add' φ ψ := Subtype.ext (map_add _ _ _)
  map_smul' r φ := Subtype.ext (LinearMap.map_smul_of_tower _ r _)

/-- The established degree-zero model is the homology of the full singular complex. -/
def cohomologyZeroIso (X : Type u) [TopologicalSpace X] :
    Cohomology (TopCat.of X) 0 ≅ ModuleCat.of ℚ (SingularDegreeZero.H0 X) := by
  refine (CochainComplex.isoHomologyπ₀ (complex (TopCat.of X))).symm ≪≫
    (complex (TopCat.of X)).cyclesIsoSc' 0 0 1 (by simp)
      ((ComplexShape.up ℕ).next_eq' (by decide)) ≪≫
    ((complex (TopCat.of X)).sc' 0 0 1).moduleCatCyclesIso ≪≫ ?_
  change ModuleCat.of ℚ (LinearMap.ker (((complex (TopCat.of X)).d 0 (0 + 1)).hom)) ≅ _
  rw [complex_d]
  exact (kernelZeroCoordinates X).toModuleIso

/-- Actual singular cocycles, with closedness imposed by the constructed differential. -/
abbrev Cocycle (X : TopCat.{u}) (n : ℕ) := LinearMap.ker (differential X n)

/-- The incoming coboundary lands in cocycles by the proved square-zero identity. -/
def differentialToCocycles (X : TopCat.{u}) (n : ℕ) :
    Cochain X n →ₗ[ℚ] Cocycle X (n + 1) :=
  (differential X n).codRestrict _ (differential_squared X n)

/-- Singular coboundaries inside singular cocycles; there is no incoming degree at zero. -/
def coboundaries (X : TopCat.{u}) (n : ℕ) : Submodule ℚ (Cocycle X n) :=
  match n with
  | 0 => ⊥
  | n + 1 => LinearMap.range (differentialToCocycles X n)

/-- The explicit quotient of actual closed singular cochains by actual coboundaries. -/
abbrev QuotientCohomology (X : TopCat.{u}) (n : ℕ) :=
  Cocycle X n ⧸ coboundaries X n

/-- The actual cohomology class of a singular cocycle. -/
def quotientClass (X : TopCat.{u}) (n : ℕ) :
    Cocycle X n →ₗ[ℚ] QuotientCohomology X n := (coboundaries X n).mkQ

@[simp]
theorem quotientClass_eq_zero_iff (X : TopCat.{u}) (n : ℕ) (φ : Cocycle X n) :
    quotientClass X n φ = 0 ↔ φ ∈ coboundaries X n := Submodule.Quotient.mk_eq_zero _

/-- A positive-degree singular cocycle vanishes in cohomology exactly when it has a primitive. -/
theorem quotientClass_succ_eq_zero_iff (X : TopCat.{u}) (n : ℕ) (φ : Cocycle X (n + 1)) :
    quotientClass X (n + 1) φ = 0 ↔
      ∃ ψ : Cochain X n, differential X n ψ = φ.val := by
  rw [quotientClass_eq_zero_iff, coboundaries, LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, hψ⟩
    exact ⟨ψ, congrArg Subtype.val hψ⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨ψ, Subtype.ext hψ⟩

/-- The two consecutive constructed singular coboundaries form a short complex. -/
def differentialShortComplex (X : TopCat.{u}) (n : ℕ) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.moduleCatMk (differential X n) (differential X (n + 1)) (by
    ext φ σ
    exact congrFun (differential_squared X n φ) σ)

/-- This short complex is the corresponding window of the genuine singular complex. -/
def differentialShortComplexIso (X : TopCat.{u}) (n : ℕ) :
    (complex X).sc' n (n + 1) ((n + 1) + 1) ≅ differentialShortComplex X n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [differentialShortComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', complex_d, Category.id_comp, Category.comp_id])
    (by simp [differentialShortComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', complex_d, Category.id_comp, Category.comp_id])

/-- Categorical singular cohomology is the concrete cocycle/coboundary quotient. -/
def cohomologyQuotientIso (X : TopCat.{u}) (n : ℕ) :
    Cohomology X n ≅ ModuleCat.of ℚ (QuotientCohomology X n) :=
  match n with
  | 0 =>
    (cohomologyZeroIso X) ≪≫ (kernelZeroCoordinates X).symm.toModuleIso ≪≫
      ((coboundaries X 0).quotEquivOfEqBot rfl).symm.toModuleIso
  | n + 1 =>
    (complex X).homologyIsoSc' n (n + 1) ((n + 1) + 1)
        (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)) ≪≫
      ShortComplex.homologyMapIso (differentialShortComplexIso X n) ≪≫
        (differentialShortComplex X n).moduleCatHomologyIso

/-- An actual singular cocycle determines a class in categorical singular cohomology. -/
def cohomologyClass (X : TopCat.{u}) (n : ℕ) :
    Cocycle X n →ₗ[ℚ] Cohomology X n :=
  (cohomologyQuotientIso X n).toLinearEquiv.symm.toLinearMap.comp (quotientClass X n)

theorem cohomologyClass_surjective (X : TopCat.{u}) (n : ℕ) :
    Function.Surjective (cohomologyClass X n) :=
  (cohomologyQuotientIso X n).toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective _)

@[simp]
theorem cohomologyClass_eq_zero_iff (X : TopCat.{u}) (n : ℕ) (φ : Cocycle X n) :
    cohomologyClass X n φ = 0 ↔ φ ∈ coboundaries X n := by
  change (cohomologyQuotientIso X n).toLinearEquiv.symm (quotientClass X n φ) = 0 ↔ _
  simp

/-- The cochain pullback restricts to the actual singular cocycles. -/
def cocyclePullback {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    Cocycle Y n →ₗ[ℚ] Cocycle X n where
  toFun φ := ⟨(pullback f).f n φ.val, by
    rw [LinearMap.mem_ker, differential_pullback,
      LinearMap.mem_ker.mp φ.property, map_zero]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    funext σ
    rfl

/-- Pullback carries the actual coboundary of a cochain to the coboundary of its pullback. -/
theorem cocyclePullback_differentialToCocycles {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) (φ : Cochain Y n) :
    cocyclePullback f (n + 1) (differentialToCocycles Y n φ) =
      differentialToCocycles X n ((pullback f).f n φ) :=
  Subtype.ext (differential_pullback f n φ).symm

/-- Continuous pullback on the explicit cocycle/coboundary quotient. -/
def quotientPullback {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    QuotientCohomology Y n →ₗ[ℚ] QuotientCohomology X n :=
  (coboundaries Y n).mapQ (coboundaries X n) (cocyclePullback f n) (by
    intro φ hφ
    change cocyclePullback f n φ ∈ coboundaries X n
    cases n with
    | zero =>
      have hzero : φ = 0 := hφ
      simp [hzero, coboundaries]
    | succ n =>
      rcases hφ with ⟨ψ, rfl⟩
      exact ⟨(pullback f).f n ψ, (cocyclePullback_differentialToCocycles f n ψ).symm⟩)

/-- Pulling back a quotient class is represented by the actual pulled-back cocycle. -/
@[simp]
theorem quotientPullback_class {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) (φ : Cocycle Y n) :
    quotientPullback f n (quotientClass Y n φ) =
      quotientClass X n (cocyclePullback f n φ) := rfl

end

end HodgeConjecture.SingularCochains
