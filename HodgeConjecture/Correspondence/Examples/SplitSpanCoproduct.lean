import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry

/-!
# Disjoint unions of split scheme spans

The sum of finite indexing sets is identified with the actual scheme
coproduct. The two legs are respected, so additive relations can be imposed
on geometric correspondence classes, not only on a presentation by labels.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]
variable {S T I J : Type u}

/-- The canonical map from the actual coproduct to the sum-indexed split scheme. -/
def sumDesc (S T : Type u) : scheme K S ⨿ scheme K T ⟶ scheme K (S ⊕ T) :=
  coprod.desc (mapOfFunction K Sum.inl) (mapOfFunction K Sum.inr)

theorem sumDesc_eq (S T : Type u) :
    sumDesc K S T = coprodSpec (S → K) (T → K) ≫
      Spec.map (CommRingCat.ofHom
        (RingEquiv.sumArrowEquivProdArrow S T K).toRingHom) := by
  apply coprod.hom_ext
  · simp only [sumDesc, coprod.inl_desc]
    rw [← Category.assoc, coprodSpec_inl]
    unfold mapOfFunction
    rw [← Spec.map_comp]
    rfl
  · simp only [sumDesc, coprod.inr_desc]
    rw [← Category.assoc, coprodSpec_inr]
    unfold mapOfFunction
    rw [← Spec.map_comp]
    rfl

instance (S T : Type u) : IsIso (sumDesc K S T) := by
  rw [sumDesc_eq]
  haveI : IsIso (CommRingCat.ofHom
      (RingEquiv.sumArrowEquivProdArrow S T K).toRingHom) :=
    (RingEquiv.sumArrowEquivProdArrow S T K).toCommRingCatIso.isIso_hom
  infer_instance

/-- The sum-indexed split scheme is the actual scheme coproduct. -/
def sumSchemeIso (S T : Type u) : scheme K (S ⊕ T) ≅ scheme K S ⨿ scheme K T :=
  (asIso (sumDesc K S T)).symm

@[simp]
theorem sumSchemeIso_inv (S T : Type u) :
    (sumSchemeIso K S T).inv = sumDesc K S T := rfl

@[simp, reassoc]
theorem sumSchemeIso_hom_desc (f : S → I) (g : T → I) :
    (sumSchemeIso K S T).hom ≫
      coprod.desc (mapOfFunction K f) (mapOfFunction K g) =
        mapOfFunction K (Sum.elim f g) := by
  apply (cancel_epi (sumSchemeIso K S T).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  change coprod.desc (mapOfFunction K f) (mapOfFunction K g) =
    sumDesc K S T ≫ mapOfFunction K (Sum.elim f g)
  apply coprod.hom_ext
  · simp [sumDesc, mapOfFunction_comp]
  · simp [sumDesc, mapOfFunction_comp]

/-- Disjoint-union labels present the actual coproduct of the two scheme spans. -/
def span_sum_iso (leftS : S → I) (rightS : S → J)
    (leftT : T → I) (rightT : T → J) :
    SchemeCorrespondence.Isom
      (span K (Sum.elim leftS leftT) (Sum.elim rightS rightT))
      (SchemeCorrespondence.coprod (span K leftS rightS) (span K leftT rightT)) where
  carrierIso := sumSchemeIso K S T
  hom_left := sumSchemeIso_hom_desc K leftS leftT
  hom_right := sumSchemeIso_hom_desc K rightS rightT

end SplitPointGeometry

end

end HodgeConjecture
