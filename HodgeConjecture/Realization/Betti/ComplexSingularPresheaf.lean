module

public import HodgeConjecture.Realization.Betti.CoefficientChange
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.SheafCohomology.CochainPresheaf
public import HodgeConjecture.SheafCohomology.ConstantLift

@[expose] public noncomputable section

/-!
# The existing complex-valued singular cochains on opens

Native precomposition on the original rational chains supplies all
pullbacks. The shared cochain-presheaf construction supplies the original
complex coefficient objects on opens and their native sheafification.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace Opposite Simplicial

namespace HodgeConjecture.SingularCoefficientChange

/-- Native singular chains, opposite complexes and the existing exact functional functor. -/
def functor : TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).op ⋙
    HomologicalComplex.opFunctor _ (.down ℕ) ⋙
      (HomCoefficients.functor ℚ ℂ).mapHomologicalComplex (.up ℕ)

def pullback {X Y : TopCat.{0}} (f : X ⟶ Y) : complexCochains Y ⟶ complexCochains X :=
  functor.map f.op

theorem pullback_coordinates {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : (complexCochains Y).X n) (σ : SingularCochains.Simplex X n) :
    complexCoordinates X n ((pullback f).f n φ) σ =
      complexCoordinates Y n φ ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) := by
  change (show chains Y |>.X n →ₗ[ℚ] ℂ from φ)
    ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n
      (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ 1))) = _
  rw [SubcomplexChainCoordinates.coordinates_map]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem differential_coordinates (X : TopCat.{0}) (n : ℕ)
    (φ : (complexCochains X).X n) (σ : SingularCochains.Simplex X (n + 1)) :
    complexCoordinates X (n + 1) ((complexCochains X).d n (n + 1) φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        complexCoordinates X n φ ((TopCat.toSSet.obj X).δ i σ) := by
  change (show chains X |>.X n →ₗ[ℚ] ℂ from φ)
    ((chains X).d (n + 1) n
      (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) (n + 1) (Finsupp.single σ 1))) = _
  rw [SingularChainCoordinates.coordinates_boundary, SingularChainCoordinates.boundary_single]
  simp only [map_sum, map_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

variable (X : TopCat.{0})

def constantCochain : ℂ →ₗ[ℂ] (complexCochains X).X 0 :=
  (complexCoordinates X 0).symm.toLinearMap.comp (LinearMap.pi (fun _ ↦ LinearMap.id))

@[simp]
theorem constantCochain_coordinates (c : ℂ) :
    complexCoordinates X 0 (constantCochain X c) = fun _ ↦ c :=
  (complexCoordinates X 0).apply_symm_apply _

theorem differential_constantCochain (c : ℂ) :
    (complexCochains X).d 0 1 (constantCochain X c) = 0 := by
  apply (complexCoordinates X 1).injective
  funext σ
  rw [differential_coordinates]
  rw [Fin.sum_univ_two, constantCochain_coordinates]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    add_neg_cancel, map_zero, Pi.zero_apply]

theorem constantCochain_injective [Nonempty X] : Function.Injective (constantCochain X) := by
  intro a b h
  let σ := SingularDegreeZero.simplexEquivSingularSet X 0
    (SingularDegreeZero.pointSimplex X (Classical.choice ‹Nonempty X›))
  have he := congrArg (fun z ↦ complexCoordinates X 0 z σ) h
  simpa only [constantCochain_coordinates] using he

theorem pullback_constantCochain {Y : TopCat.{0}} (f : Y ⟶ X) (c : ℂ) :
    (pullback f).f 0 (constantCochain X c) = constantCochain Y c := by
  apply (complexCoordinates Y 0).injective
  funext σ
  rw [pullback_coordinates, constantCochain_coordinates, constantCochain_coordinates]

abbrev presheaf := SheafCohomology.CochainPresheaf.presheaf ℂ functor X
abbrev presheafDifferential := SheafCohomology.CochainPresheaf.differential ℂ functor X
abbrev presheafComplex := SheafCohomology.CochainPresheaf.complex ℂ functor X
abbrev cochainSheaf := SheafCohomology.CochainPresheaf.sheaf ℂ functor X
abbrev sheafDifferential := SheafCohomology.CochainPresheaf.sheafDifferential ℂ functor X
abbrev sheafComplex := SheafCohomology.CochainPresheaf.sheafComplex ℂ functor X
abbrev globalCochainsToSheaf := SheafCohomology.CochainPresheaf.globalUnit ℂ functor X

def constantPresheafMap : SheafCohomology.ConstantLift.presheaf ℂ X ⟶ presheaf X 0 where
  app U := ModuleCat.ofHom (constantCochain ((Opens.toTopCat X).obj U.unop))
  naturality U V i := by
    change 𝟙 _ ≫ ModuleCat.ofHom (constantCochain ((Opens.toTopCat X).obj V.unop)) = _
    rw [Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (pullback_constantCochain _ ((Opens.toTopCat X).map i.unop) c).symm

theorem constantPresheafMap_differential : constantPresheafMap X ≫ presheafDifferential X 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact differential_constantCochain _

/-- Existing rational vanishing and the proved coefficient map supply complex primitives. -/
theorem exists_primitive [ContractibleSpace X] (n : ℕ) (z : (complexCochains X).X (n + 1))
    (hz : (complexCochains X).d (n + 1) (n + 2) z = 0) :
    ∃ b : (complexCochains X).X n, (complexCochains X).d n (n + 1) b = z := by
  have hQ := SingularContractible.isZero_cohomology X (n + 1) (by omega)
  have : Subsingleton (SingularCochains.Cohomology X (n + 1)) := ModuleCat.isZero_iff_subsingleton.mp hQ
  have : FiniteDimensional ℚ (SingularCochains.Cohomology X (n + 1)) := inferInstance
  have hC : IsZero (ComplexCohomology X (n + 1)) :=
    IsZero.of_iso ((HomCoefficients.tensorFunctor ℚ ℂ).map_isZero hQ) (cohomologyIso X (n + 1)).symm
  have hex : (complexCochains X).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
    exact hC
  rw [(complexCochains X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)] at hex
  rw [ShortComplex.moduleCat_exact_iff] at hex
  exact hex z hz

/-- The existing path simplex and endpoint identities prove literal complex constancy. -/
theorem closed_zero_constant [PathConnectedSpace X] (x : X) (z : (complexCochains X).X 0)
    (hz : (complexCochains X).d 0 1 z = 0) :
    ∃ c : ℂ, constantCochain X c = z := by
  let e := SingularDegreeZero.simplexEquivSingularSet X 0
  let φ := complexCoordinates X 0 z
  let c := φ (e (SingularDegreeZero.pointSimplex X x))
  have hface (γ : SingularDegreeZero.Simplex X 1) :
      φ (e (SingularDegreeZero.face X γ 0)) = φ (e (SingularDegreeZero.face X γ 1)) := by
    have he := congrArg (fun w ↦ complexCoordinates X 1 w
      (SingularDegreeZero.simplexEquivSingularSet X 1 γ)) hz
    rw [differential_coordinates] at he
    rw [Fin.sum_univ_two] at he
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_smul, neg_smul, map_zero, Pi.zero_apply, ← sub_eq_add_neg] at he
    change φ ((TopCat.toSSet.obj X).δ 0 _) - φ ((TopCat.toSSet.obj X).δ 1 _) = 0 at he
    apply sub_eq_zero.mp
    change φ (SingularDegreeZero.simplexEquivSingularSet X 0 (SingularDegreeZero.face X γ 0)) -
      φ (SingularDegreeZero.simplexEquivSingularSet X 0 (SingularDegreeZero.face X γ 1)) = 0
    rw [SingularDegreeZero.simplexEquivSingularSet_face,
      SingularDegreeZero.simplexEquivSingularSet_face]
    exact he
  have hpoint (y : X) : φ (e (SingularDegreeZero.pointSimplex X y)) = c := by
    have he := hface (SingularDegreeZero.pathSimplex ((PathConnectedSpace.joined x y).somePath))
    simpa only [SingularDegreeZero.face_pathSimplex_zero, SingularDegreeZero.face_pathSimplex_one] using he
  refine ⟨c, (complexCoordinates X 0).injective ?_⟩
  rw [constantCochain_coordinates]
  funext σ
  let γ := e.symm σ
  have he : e (SingularDegreeZero.pointSimplex X (γ default)) = σ := by
    rw [SingularDegreeZero.pointSimplex_eq]
    exact e.apply_symm_apply σ
  exact (he ▸ hpoint (γ default)).symm

end HodgeConjecture.SingularCoefficientChange
