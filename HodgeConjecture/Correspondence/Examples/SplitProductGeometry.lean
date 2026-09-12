import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
import HodgeConjecture.Correspondence.Examples.SplitIntegralSubschemes
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Products of actual finite split schemes

The split scheme indexed by pairs is canonically isomorphic to the scheme
fiber product over the field. The isomorphism respects both projections,
the rational point inclusions, and the diagonal.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K] (I J : Type u)

/-- A rational component inclusion is a section of the structure map. -/
@[simp, reassoc]
theorem pointInclusion_toBase (i : I) :
    pointInclusion K I i ≫ toBase K I = 𝟙 (Spec (.of K)) := by
  unfold pointInclusion toBase
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of K) using 1

/-- The canonical comparison from pair labels to the actual scheme product. -/
def productComparison :
    scheme K (I × J) ⟶ pullback (toBase K I) (toBase K J) :=
  pullback.lift (mapOfFunction K (Prod.fst : I × J → I))
    (mapOfFunction K (Prod.snd : I × J → J)) (by simp)

@[simp, reassoc]
theorem productComparison_fst :
    productComparison K I J ≫ pullback.fst _ _ =
      mapOfFunction K (Prod.fst : I × J → I) := by
  simp [productComparison]

@[simp, reassoc]
theorem productComparison_snd :
    productComparison K I J ≫ pullback.snd _ _ =
      mapOfFunction K (Prod.snd : I × J → J) := by
  simp [productComparison]

private def pairEquivFiber :
    I × J ≃ Fiber (fun _ : I ↦ (PUnit.unit : PUnit.{u+1}))
      (fun _ : J ↦ PUnit.unit) where
  toFun p := ⟨p, rfl⟩
  invFun p := p.val
  left_inv _ := rfl
  right_inv _ := rfl

private def productBaseComparison :
    pullback (mapOfFunction K (fun _ : I ↦ (PUnit.unit : PUnit.{u+1})))
      (mapOfFunction K (fun _ : J ↦ PUnit.unit)) ⟶
      pullback (toBase K I) (toBase K J) :=
  pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (singletonIso K).hom (by
    change mapOfFunction K _ ≫ toBase K PUnit = 𝟙 _ ≫ _
    simp) (by
    change mapOfFunction K _ ≫ toBase K PUnit = 𝟙 _ ≫ _
    simp)

private instance : IsIso (productBaseComparison K I J) := by
  unfold productBaseComparison
  infer_instance

instance [Finite I] [Finite J] : IsIso (productComparison K I J) := by
  have h : (isoOfEquiv K (pairEquivFiber I J)).hom ≫
      (fiberIso K (fun _ : I ↦ (PUnit.unit : PUnit.{u+1}))
        (fun _ : J ↦ PUnit.unit)).hom ≫ productBaseComparison K I J =
      productComparison K I J := by
    apply pullback.hom_ext <;>
      simp [productBaseComparison, fiberIso, isoOfEquiv, pairEquivFiber,
        Function.comp_def]
  rw [← h]
  infer_instance

/-- The scheme product over the field is the split scheme indexed by pairs. -/
def productIso [Finite I] [Finite J] :
    scheme K (I × J) ≅ pullback (toBase K I) (toBase K J) :=
  asIso (productComparison K I J)

@[simp, reassoc]
theorem productIso_hom_fst [Finite I] [Finite J] :
    (productIso K I J).hom ≫ pullback.fst _ _ =
      mapOfFunction K (Prod.fst : I × J → I) :=
  productComparison_fst K I J

@[simp, reassoc]
theorem productIso_hom_snd [Finite I] [Finite J] :
    (productIso K I J).hom ≫ pullback.snd _ _ =
      mapOfFunction K (Prod.snd : I × J → J) :=
  productComparison_snd K I J

/-- The actual rational point with the specified two component projections. -/
def pointPairInclusion (i : I) (j : J) :
    Spec (.of K) ⟶ pullback (toBase K I) (toBase K J) :=
  pullback.lift (pointInclusion K I i) (pointInclusion K J j) (by simp)

@[simp, reassoc]
theorem pointPairInclusion_fst (i : I) (j : J) :
    pointPairInclusion K I J i j ≫ pullback.fst _ _ = pointInclusion K I i := by
  simp [pointPairInclusion]

@[simp, reassoc]
theorem pointPairInclusion_snd (i : I) (j : J) :
    pointPairInclusion K I J i j ≫ pullback.snd _ _ = pointInclusion K J j := by
  simp [pointPairInclusion]

@[simp, reassoc]
theorem pointInclusion_productIso [Finite I] [Finite J] (i : I) (j : J) :
    pointInclusion K (I × J) (i, j) ≫ (productIso K I J).hom =
      pointPairInclusion K I J i j := by
  apply pullback.hom_ext <;> simp

/-- The label diagonal is the actual diagonal of the structure morphism. -/
@[simp, reassoc]
theorem diagonal_productIso [Finite I] :
    mapOfFunction K (fun i : I ↦ (i, i)) ≫ (productIso K I I).hom =
      pullback.diagonal (toBase K I) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, productIso_hom_fst, productIso_hom_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, mapOfFunction_comp] <;>
    exact mapOfFunction_id K

/-- The actual split diagonal is open, so its flat pullback is the
zero-dimensional specialization of diagonal Gysin pullback. -/
instance diagonalMap_isOpenImmersion [Finite I] :
    IsOpenImmersion (mapOfFunction K (fun i : I ↦ (i, i))) := by
  apply (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion
    (mapOfFunction K (fun i : I ↦ (i, i))) (productIso K I I).hom).mp
  rw [diagonal_productIso]
  infer_instance

/-- The same diagonal is closed, as required for intersection by a diagonal. -/
instance diagonalMap_isClosedImmersion [Finite I] :
    IsClosedImmersion (mapOfFunction K (fun i : I ↦ (i, i))) := by
  apply (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
    (mapOfFunction K (fun i : I ↦ (i, i))) (productIso K I I).hom).mp
  rw [diagonal_productIso]
  infer_instance

/-- A constant map of labels factors through the field-valued point. -/
@[simp, reassoc]
theorem toBase_pointInclusion (i : I) :
    toBase K J ≫ pointInclusion K I i = mapOfFunction K (fun _ : J ↦ i) := by
  unfold toBase pointInclusion mapOfFunction
  rw [← Spec.map_comp]
  rfl

variable {I J}

/-- The actual scheme fiber over a rational point receives the split scheme
indexed by the set-theoretic fiber. -/
def pointFiberComparison (f : J → I) (i : I) :
    scheme K {j // f j = i} ⟶
      pullback (mapOfFunction K f) (pointInclusion K I i) :=
  pullback.lift (mapOfFunction K (Subtype.val : {j // f j = i} → J))
    (toBase K {j // f j = i}) (by
      rw [mapOfFunction_comp, toBase_pointInclusion]
      congr 1
      funext j
      exact j.property)

@[simp, reassoc]
theorem pointFiberComparison_fst (f : J → I) (i : I) :
    pointFiberComparison K f i ≫ pullback.fst _ _ =
      mapOfFunction K (Subtype.val : {j // f j = i} → J) := by
  simp [pointFiberComparison]

@[simp, reassoc]
theorem pointFiberComparison_snd (f : J → I) (i : I) :
    pointFiberComparison K f i ≫ pullback.snd _ _ = toBase K {j // f j = i} := by
  simp [pointFiberComparison]

private def pointFiberEquiv (f : J → I) (i : I) :
    {j // f j = i} ≃ Fiber f (fun _ : PUnit.{u+1} ↦ i) where
  toFun j := ⟨(j.val, PUnit.unit), j.property⟩
  invFun p := ⟨p.val.1, p.property⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Subsingleton.elim _ _)

private def pointFiberBaseComparison (f : J → I) (i : I) :
    pullback (mapOfFunction K f) (mapOfFunction K (fun _ : PUnit.{u+1} ↦ i)) ⟶
      pullback (mapOfFunction K f) (pointInclusion K I i) :=
  pullback.map _ _ _ _ (𝟙 _) (singletonIso K).hom (𝟙 _) (by simp) (by
    change _ ≫ 𝟙 _ = toBase K PUnit ≫ pointInclusion K I i
    simp)

private instance (f : J → I) (i : I) :
    IsIso (pointFiberBaseComparison K f i) := by
  unfold pointFiberBaseComparison
  infer_instance

instance [Finite I] [Finite J] (f : J → I) (i : I) :
    IsIso (pointFiberComparison K f i) := by
  have h : (isoOfEquiv K (pointFiberEquiv f i)).hom ≫
      (fiberIso K f (fun _ : PUnit.{u+1} ↦ i)).hom ≫
        pointFiberBaseComparison K f i = pointFiberComparison K f i := by
    apply pullback.hom_ext <;>
      simp [pointFiberBaseComparison, fiberIso, isoOfEquiv, pointFiberEquiv,
        singletonIso, Function.comp_def, fiberComparison_snd_assoc]
  rw [← h]
  infer_instance

/-- The scheme-theoretic fiber of an induced map over a rational point is
the finite split scheme on the actual set-theoretic fiber. -/
def pointFiberIso [Finite I] [Finite J] (f : J → I) (i : I) :
    scheme K {j // f j = i} ≅
      pullback (mapOfFunction K f) (pointInclusion K I i) :=
  asIso (pointFiberComparison K f i)

@[simp, reassoc]
theorem pointFiberIso_hom_fst [Finite I] [Finite J] (f : J → I) (i : I) :
    (pointFiberIso K f i).hom ≫ pullback.fst _ _ =
      mapOfFunction K (Subtype.val : {j // f j = i} → J) :=
  pointFiberComparison_fst K f i

@[simp, reassoc]
theorem pointFiberIso_hom_snd [Finite I] [Finite J] (f : J → I) (i : I) :
    (pointFiberIso K f i).hom ≫ pullback.snd _ _ = toBase K {j // f j = i} :=
  pointFiberComparison_snd K f i

/-- The scheme-theoretic inverse image of a point is precisely the closed
subscheme cut out by the inclusion of its set-theoretic fiber. -/
theorem pointIdealSheaf_comap_mapOfFunction [Finite I] [Finite J]
    (f : J → I) (i : I) :
    (pointIdealSheaf K I i).comap (mapOfFunction K f) =
      (mapOfFunction K (Subtype.val : {j // f j = i} → J)).ker := by
  unfold pointIdealSheaf
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_comp_of_isIso (pointFiberIso K f i).hom,
    pointFiberIso_hom_fst]

end SplitPointGeometry

end

end HodgeConjecture
