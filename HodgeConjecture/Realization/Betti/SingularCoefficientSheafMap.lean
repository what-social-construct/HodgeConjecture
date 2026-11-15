module

public import HodgeConjecture.LinearAlgebra.HomCoefficientInclusion
public import HodgeConjecture.Realization.Betti.ComplexSingularResolution
public import HodgeConjecture.Realization.Betti.SingularSheafResolution
public import HodgeConjecture.SheafCohomology.ScalarSheafificationComplex

@[expose] public noncomputable section

/-!
# The original cochain coefficient map on the native sheaf resolutions

Postcomposition with ℚ → ℂ supplies the coefficient map before
sheafification. Native coefficient/sheafification compatibility gives its
map on the original sheaf complexes, retaining the original constant maps.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor TopologicalSpace Opposite Simplicial
open scoped TensorProduct

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

def coefficientMap : SingularCochains.complex X ⟶
    ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex (.up ℕ)).obj (complexCochains X) :=
  (rationalComplexIso X).hom ≫ HomCoefficients.coefficientComplexMap ℚ ℂ (chains X)

theorem coefficientMap_coordinates (n : ℕ) (φ : SingularCochains.Cochain X n)
    (σ : SingularCochains.Simplex X n) :
    complexCoordinates X n ((coefficientMap X).f n φ) σ = (φ σ : ℂ) := by
  change algebraMap ℚ ℂ ((CochainDualCoordinates.coordinates (TopCat.toSSet.obj X) n).symm φ
    (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ 1))) = _
  rw [CochainDualCoordinates.coordinates_symm_coordinates_single, one_mul]
  simp

/-- This is the same coefficient map whose tensor extension was proved invertible in 0054. -/
theorem coefficientMap_eq_one_tmul (n : ℕ) (φ : SingularCochains.Cochain X n) :
    (coefficientMap X).f n φ = (cochainComparison X).f n (1 ⊗ₜ[ℚ] φ) := by
  apply (complexCoordinates X n).injective
  funext σ
  rw [coefficientMap_coordinates, cochainComparison_apply, one_mul]

theorem coefficientMap_naturality {Y : TopCat.{0}} (f : Y ⟶ X) (n : ℕ) :
    (SingularCochains.pullback f).f n ≫ (coefficientMap Y).f n =
      (coefficientMap X).f n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map ((pullback f).f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (complexCoordinates Y n).injective
  funext σ
  change complexCoordinates Y n ((coefficientMap Y).f n ((SingularCochains.pullback f).f n φ)) σ =
    complexCoordinates Y n ((pullback f).f n ((coefficientMap X).f n φ)) σ
  rw [coefficientMap_coordinates, pullback_coordinates, coefficientMap_coordinates]
  rfl

def presheafCoefficientMap (n : ℕ) : SingularCochains.presheaf X n ⟶
    presheaf X n ⋙ ModuleCat.restrictScalars (algebraMap ℚ ℂ) where
  app U := (coefficientMap ((Opens.toTopCat X).obj U.unop)).f n
  naturality _ _ i := coefficientMap_naturality _ ((Opens.toTopCat X).map i.unop) n

def presheafComplexCoefficientMap : SingularCochains.presheafComplex X ⟶
    ((SheafCohomology.ScalarRestriction.presheaves (algebraMap ℚ ℂ) X).mapHomologicalComplex (.up ℕ)).obj
      (presheafComplex X) where
  f n := presheafCoefficientMap X n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    change presheafCoefficientMap X i ≫
        (SheafCohomology.ScalarRestriction.presheaves (algebraMap ℚ ℂ) X).map
          ((presheafComplex X).d i (i + 1)) =
      (SingularCochains.presheafComplex X).d i (i + 1) ≫ presheafCoefficientMap X (i + 1)
    rw [SheafCohomology.CochainPresheaf.complex_d, SingularCochains.presheafComplex_d]
    apply NatTrans.ext
    funext U
    change (coefficientMap ((Opens.toTopCat X).obj U.unop)).f i ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          ((complexCochains ((Opens.toTopCat X).obj U.unop)).d i (i + 1)) =
      (SingularCochains.complex ((Opens.toTopCat X).obj U.unop)).d i (i + 1) ≫
        (coefficientMap ((Opens.toTopCat X).obj U.unop)).f (i + 1)
    exact (coefficientMap ((Opens.toTopCat X).obj U.unop)).comm i (i + 1)

theorem constantPresheafMap_coefficient :
    SingularCochains.constantPresheafMap X ≫ presheafCoefficientMap X 0 =
      SheafCohomology.ScalarRestriction.constantPresheafMap (algebraMap ℚ ℂ) X ≫
        whiskerRight (constantPresheafMap X) (ModuleCat.restrictScalars (algebraMap ℚ ℂ)) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply (complexCoordinates ((Opens.toTopCat X).obj U.unop) 0).injective
  funext σ
  change complexCoordinates _ 0 ((coefficientMap _).f 0 (SingularCochains.constantCochain _ q)) σ =
    complexCoordinates _ 0 (constantCochain _ (algebraMap ℚ ℂ q)) σ
  rw [coefficientMap_coordinates, constantCochain_coordinates]
  rfl

def sheafCoefficientMap : SingularCochains.sheafComplex X ⟶
    ((SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).mapHomologicalComplex (.up ℕ)).obj
      (sheafComplex X) :=
  SheafCohomology.ScalarRestriction.sheafifyComplexMap (algebraMap ℚ ℂ) X
    (presheafComplexCoefficientMap X)

/-- The original native constant-sheaf coefficient inclusion commutes with both augmentations. -/
@[reassoc]
theorem augmentation_coefficient :
    SingularCochains.augmentation X ≫ (sheafCoefficientMap X).f 0 =
      SheafCohomology.ScalarRestriction.constantMap (algebraMap ℚ ℂ) X ≫
        (SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).map (augmentation X) :=
  SheafCohomology.ScalarRestriction.sheafifyMap_constant_naturality (algebraMap ℚ ℂ) X
    (SingularCochains.constantPresheafMap X) (constantPresheafMap X) (presheafCoefficientMap X 0)
    (constantPresheafMap_coefficient X)

/-- Native scalar restriction on the same constant sheaf placed in degree zero. -/
def constantCoefficientMap : (CochainComplex.single₀ _).obj (SingularCochains.constantSheaf X) ⟶
    ((SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).mapHomologicalComplex (.up ℕ)).obj
      ((CochainComplex.single₀ _).obj (constantSheaf X)) :=
  (CochainComplex.single₀ _).map (SheafCohomology.ScalarRestriction.constantMap (algebraMap ℚ ℂ) X) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X) (.up ℕ) 0).inv.app (constantSheaf X)

theorem constantCoefficientMap_zero : (constantCoefficientMap X).f 0 =
    SheafCohomology.ScalarRestriction.constantMap (algebraMap ℚ ℂ) X := by
  simp [constantCoefficientMap]

/-- The coefficient map is a map of the original native constant-sheaf resolutions. -/
@[reassoc]
theorem comparison_coefficient :
    SingularCochains.comparison X ≫ sheafCoefficientMap X =
      constantCoefficientMap X ≫
        ((SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).mapHomologicalComplex (.up ℕ)).map
          (comparison X) := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (SingularCochains.comparison X).f 0 ≫ (sheafCoefficientMap X).f 0 =
    (constantCoefficientMap X).f 0 ≫ _
  rw [SingularCochains.comparison_zero, constantCoefficientMap_zero]
  change _ = _ ≫ (SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).map ((comparison X).f 0)
  rw [comparison_zero]
  exact augmentation_coefficient X

end HodgeConjecture.SingularCoefficientChange
