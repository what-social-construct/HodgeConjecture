module

public import HodgeConjecture.Cycles.IntegralCodimension
public import HodgeConjecture.Cycles.PrincipalRelations

@[expose] public section

/-!
# Actual codimension indexing of principal relations

On an integral scheme locally of finite type over a field, relations in
degree d-(n+1) use the same actual codimension-n carriers and function-field
units as the existing degree-indexed construction. The equivalence below
changes only the proof of the carrier's degree condition. Its inverse
still gives the literal existing ambient principal divisor.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Relations in codimension n+1 are indexed by codimension-n carriers
with units in their unchanged actual function fields. -/
def principalRelationDataEquivCodimension
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ) :
    PrincipalRelationData (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - ((n : ℤ) + 1)) ≃
      ((W : {W : IntegralClosedSubscheme X // supportCodimension W = (n : ℕ∞)}) ×
        (letI := W.val.property; W.val.val.subscheme.functionFieldˣ)) where
  toFun d := ⟨⟨d.1.val,
    (supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
      k X p d.1.val n).mp (by have h := d.1.property; omega)⟩, d.2⟩
  invFun d := ⟨⟨d.1.val, by
    have h :=
      (supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
        k X p d.1.val n).mpr d.1.property
    omega⟩, d.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

/-- Forward reindexing retains the actual closed carrier. -/
@[simp]
theorem principalRelationDataEquivCodimension_apply_carrier
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (d : PrincipalRelationData (DimensionFunction.ofLocallyOfFiniteType k X p)
      (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - ((n : ℤ) + 1))) :
    ((principalRelationDataEquivCodimension k X p n) d).1.val = d.1.val := rfl

/-- Forward reindexing retains the rational function literally. -/
@[simp]
theorem principalRelationDataEquivCodimension_apply_function
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (d : PrincipalRelationData (DimensionFunction.ofLocallyOfFiniteType k X p)
      (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - ((n : ℤ) + 1))) :
    ((principalRelationDataEquivCodimension k X p n) d).2 = d.2 := rfl

/-- Inverse reindexing retains the actual closed carrier. -/
@[simp]
theorem principalRelationDataEquivCodimension_symm_apply_carrier
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (d : (W : {W : IntegralClosedSubscheme X // supportCodimension W = (n : ℕ∞)}) ×
      (letI := W.val.property; W.val.val.subscheme.functionFieldˣ)) :
    ((principalRelationDataEquivCodimension k X p n).symm d).1.val = d.1.val := rfl

/-- Inverse reindexing retains the rational function literally. -/
@[simp]
theorem principalRelationDataEquivCodimension_symm_apply_function
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (d : (W : {W : IntegralClosedSubscheme X // supportCodimension W = (n : ℕ∞)}) ×
      (letI := W.val.property; W.val.val.subscheme.functionFieldˣ)) :
    ((principalRelationDataEquivCodimension k X p n).symm d).2 = d.2 := rfl

/-- Reindexing a generator gives the same ambient principal divisor,
not a new relation map or a transported rational function. -/
@[simp]
theorem principalRelation_equivCodimension_symm_coe
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℕ)
    (d : (W : {W : IntegralClosedSubscheme X // supportCodimension W = (n : ℕ∞)}) ×
      (letI := W.val.property; W.val.val.subscheme.functionFieldˣ)) :
    letI := d.1.val.property
    (principalRelation (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - ((n : ℤ) + 1))
        ((principalRelationDataEquivCodimension k X p n).symm d) : Cycles X ℤ) =
      ambientPrincipalDivisor d.1.val d.2 := rfl

end

end HodgeConjecture.SchemeCycles
