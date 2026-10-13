import HodgeConjecture.Cycles.PointSupport
import HodgeConjecture.Cycles.FunctionFieldMap
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!
# Function fields of supports and actual ambient residue fields

The function field of an integral closed support is its generic-point
residue field, and the closed inclusion identifies this with the ambient
residue field. These canonical maps compare the weights of the existing
finite cycle pushforward with the local norm sum in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- A surjection on stalks induces a bijection on the actual residue fields. -/
theorem residueFieldMap_bijective_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨Y.residue (f.base x) c, rfl⟩

/-- The actual residue map of a morphism surjective on stalks, as a field equivalence. -/
def residueFieldEquivOfSurjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Y.residueField (f.base x) ≃+* X.residueField x :=
  RingEquiv.ofBijective (f.residueFieldMap x).hom
    (residueFieldMap_bijective_of_surjectiveOnStalks f x)

/-- The generic stalk is a field, so its residue map is an equivalence. -/
def functionFieldResidueEquiv (X : Scheme.{u}) [IsIntegral X] :
    X.functionField ≃+* X.residueField (genericPoint X) :=
  RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

/-- The actual ambient residue field is the function field of its integral support. -/
def supportFunctionFieldResidueEquiv {X : Scheme.{u}} (W : IntegralClosedSubscheme X) :
    letI := W.property
    X.residueField (ambientGenericPoint W) ≃+* W.val.subscheme.functionField := by
  letI := W.property
  exact (residueFieldEquivOfSurjectiveOnStalks W.val.subschemeι
    (genericPoint W.val.subscheme)).trans (functionFieldResidueEquiv W.val.subscheme).symm

/-- The generic field pullback is compatible with the actual generic residue maps. -/
theorem functionFieldMapOfDominant_residue {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    functionFieldMapOfDominant f ≫ X.residue (genericPoint X) =
      Y.residue (genericPoint Y) ≫
        (Y.residueFieldCongr (genericPoint_eq_of_isDominant f).symm).hom ≫
          f.residueFieldMap (genericPoint X) := by
  rw [functionFieldMapOfDominant, Category.assoc, ← Scheme.residue_residueFieldMap,
    Scheme.residue_residueFieldCongr_assoc]

/-- The degree of the actual residue-field map. Its value is used only in
finite-extension settings when interpreting it as a pushforward weight. -/
def residueFieldDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact Module.finrank (Y.residueField (f.base x)) (X.residueField x)

/-- The generic degree uses the same field extension as the actual generic residue map. -/
theorem functionField_finrank_eq_residueFieldDegree {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    letI : Algebra Y.functionField X.functionField :=
      (functionFieldMapOfDominant f).hom.toAlgebra
    Module.finrank Y.functionField X.functionField = residueFieldDegree f (genericPoint X) := by
  letI : Algebra Y.functionField X.functionField :=
    (functionFieldMapOfDominant f).hom.toAlgebra
  letI : Algebra (Y.residueField (f.base (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    ((functionFieldResidueEquiv Y).trans
      (Y.residueFieldCongr (genericPoint_eq_of_isDominant f).symm).commRingCatIsoToRingEquiv)
    (functionFieldResidueEquiv X)
  exact congrArg CommRingCat.Hom.hom (functionFieldMapOfDominant_residue f).symm

/-- A map surjective on stalks does not change a residue degree when placed on the source. -/
theorem residueFieldDegree_comp_of_source_surjectiveOnStalks {X Y Z : Scheme.{u}}
    (i : X ⟶ Y) [SurjectiveOnStalks i] (f : Y ⟶ Z) (x : X) :
    residueFieldDegree (i ≫ f) x = residueFieldDegree f (i.base x) := by
  letI : Algebra (Z.residueField (f.base (i.base x))) (Y.residueField (i.base x)) :=
    (f.residueFieldMap (i.base x)).hom.toAlgebra
  letI : Algebra (Z.residueField (f.base (i.base x))) (X.residueField x) :=
    ((i ≫ f).residueFieldMap x).hom.toAlgebra
  symm
  apply Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.refl (Z.residueField (f.base (i.base x))))
    (residueFieldEquivOfSurjectiveOnStalks i x)
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i f x)

/-- A map surjective on stalks does not change a residue degree when placed on the target. -/
theorem residueFieldDegree_comp_of_target_surjectiveOnStalks {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (i : Y ⟶ Z) [SurjectiveOnStalks i] (x : X) :
    residueFieldDegree (f ≫ i) x = residueFieldDegree f x := by
  letI : Algebra (Z.residueField (i.base (f.base x))) (X.residueField x) :=
    ((f ≫ i).residueFieldMap x).hom.toAlgebra
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    (residueFieldEquivOfSurjectiveOnStalks i (f.base x)) (RingEquiv.refl (X.residueField x))
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f i x).symm

end

end HodgeConjecture.SchemeCycles
