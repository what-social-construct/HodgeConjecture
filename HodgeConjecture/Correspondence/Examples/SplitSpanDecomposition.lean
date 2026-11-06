module

public import HodgeConjecture.Correspondence.Examples.SplitSpanCoproduct
public import HodgeConjecture.Correspondence.FiniteCoproduct

@[expose] public section

/-!
# Actual finite point decomposition of split scheme spans

The finite point-decomposition relations used in the additive quotient come
from an isomorphism with the actual indexed coproduct of singleton scheme
spans. This includes the empty indexing set. No Chow theory is assumed here.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]
variable {S I J : Type u} [Finite S]

/-- A finite split scheme is the actual coproduct of its singleton schemes. -/
def pointDecompositionIso :
    scheme K S ≅ ∐ (fun _ : S ↦ scheme K PUnit.{u+1}) :=
  (asIso (sigmaSpec (fun _ : S ↦ CommRingCat.of K))).symm ≪≫
    (Sigma.mapIso (fun _ : S ↦ singletonIso K)).symm

@[simp, reassoc]
theorem singletonIso_hom_pointInclusion (i : I) :
    (singletonIso K).hom ≫ pointInclusion K I i =
      mapOfFunction K (fun _ : PUnit.{u+1} ↦ i) := by
  unfold singletonIso toBase pointInclusion mapOfFunction
  rw [← Spec.map_comp]
  rfl

@[simp, reassoc]
theorem pointDecompositionIso_hom_desc (f : S → I) :
    (pointDecompositionIso K (S := S)).hom ≫
      Sigma.desc (fun s : S ↦ mapOfFunction K (fun _ : PUnit.{u+1} ↦ f s)) =
        mapOfFunction K f := by
  apply (cancel_epi (pointDecompositionIso K (S := S)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply Sigma.hom_ext
  intro s
  simp [pointDecompositionIso, Sigma.mapIso, sigmaSpec_comp_mapOfFunction]

/-- Both legs respect the actual finite coproduct decomposition into point spans. -/
def span_pointDecomposition_iso (left : S → I) (right : S → J) :
    SchemeCorrespondence.Isom (span K left right)
      (SchemeCorrespondence.indexedCoprod (fun s : S ↦
        span K (fun _ : PUnit.{u+1} ↦ left s) (fun _ : PUnit.{u+1} ↦ right s))) where
  carrierIso := pointDecompositionIso K
  hom_left := pointDecompositionIso_hom_desc K left
  hom_right := pointDecompositionIso_hom_desc K right

/-- The actual indexed coproduct in the point decomposition has finite étale legs. -/
theorem pointDecomposition_hasFiniteEtaleLegs (left : S → I) (right : S → J) :
    SchemeCorrespondence.HasFiniteEtaleLegs
      (SchemeCorrespondence.indexedCoprod (fun s : S ↦
        span K (fun _ : PUnit.{u+1} ↦ left s) (fun _ : PUnit.{u+1} ↦ right s))) :=
  SchemeCorrespondence.HasFiniteEtaleLegs.of_isom
    (span_pointDecomposition_iso K left right) (span_hasFiniteEtaleLegs K left right)

end SplitPointGeometry

end

end HodgeConjecture
