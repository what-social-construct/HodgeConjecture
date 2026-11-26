module

public import HodgeConjecture.Correspondence.Examples.SplitProductGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Actual finite split covers of constant geometric rank

The projection from pair labels induces an actual finite étale morphism
`Spec ((I × J) → K) ⟶ Spec (I → K)`. Its geometric rank is the number
of sheets `J`, by the proved scheme product comparison and base change
of the original finite flat rank function. In particular, two sheets over
two points give an actual rank-two morphism from four points to two points.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]

/-- The actual scheme morphism forgetting the sheet label. -/
def coverProjection (I J : Type u) : scheme K (I × J) ⟶ scheme K I :=
  mapOfFunction K (Prod.fst : I × J → I)

instance (I J : Type u) [Finite I] [Finite J] :
    IsFinite (coverProjection K I J) := by
  unfold coverProjection
  infer_instance

instance (I J : Type u) [Finite I] [Finite J] :
    Etale (coverProjection K I J) := by
  unfold coverProjection
  infer_instance

instance (I J : Type u) [Finite I] [Finite J] :
    Flat (coverProjection K I J) := by
  unfold coverProjection
  infer_instance

/-- Every downstairs scheme point has a genuine point on any chosen sheet. -/
instance (I J : Type u) [Finite I] [Finite J] [Nonempty J] :
    Surjective (coverProjection K I J) where
  surj := by
    intro x
    obtain ⟨i, rfl⟩ := (labelEquivScheme K I).surjective x
    refine ⟨labelEquivScheme K (I × J) (i, Classical.choice inferInstance), ?_⟩
    exact labelEquivScheme_natural K Prod.fst _

@[simp, reassoc]
theorem coverProjection_toBase (I J : Type u) :
    coverProjection K I J ≫ toBase K I = toBase K (I × J) :=
  mapOfFunction_toBase K Prod.fst

/-- The structural finite split morphism has its actual vector-space rank. -/
theorem toBase_finrank (J : Type u) [Fintype J] (x : Spec (.of K)) :
    (toBase K J).finrank x = Fintype.card J := by
  change (Spec.map (CommRingCat.ofHom (algebraMap K (J → K)))).finrank x = _
  rw [Scheme.Hom.finrank_SpecMap_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free, Module.finrank_pi]
  simp

/-- The projection's rank is computed by the actual scheme product and
base change, independently of any cycle or cohomology coordinates. -/
theorem coverProjection_finrank (I J : Type u) [Finite I] [Fintype J]
    (x : scheme K I) :
    (coverProjection K I J).finrank x = Fintype.card J := by
  change (mapOfFunction K (Prod.fst : I × J → I)).finrank x = _
  rw [← productIso_hom_fst K I J,
    Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_fst]
  exact toBase_finrank K J _

/-- The concrete finite étale cover from four split points to two split points. -/
abbrev twoSheetCover (k : Type) [Field k] :
    scheme k (Fin 2 × Fin 2) ⟶ scheme k (Fin 2) :=
  coverProjection k (Fin 2) (Fin 2)

/-- The actual geometric degree of the concrete cover is two. -/
@[simp]
theorem twoSheetCover_finrank (k : Type) [Field k] (x : scheme k (Fin 2)) :
    (twoSheetCover k).finrank x = 2 := by
  simpa only [Fintype.card_fin] using
    coverProjection_finrank k (Fin 2) (Fin 2) x

/-- The concrete morphism carries all the geometric finite-cover properties. -/
theorem twoSheetCover_isFiniteEtaleSurjective (k : Type) [Field k] :
    IsFinite (twoSheetCover k) ∧ Etale (twoSheetCover k) ∧
      Flat (twoSheetCover k) ∧ Surjective (twoSheetCover k) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end SplitPointGeometry

end

end HodgeConjecture
