module

public import HodgeConjecture.Correspondence.GraphCycles
public import HodgeConjecture.Cycles.FieldSupportDimension
public import HodgeConjecture.Cycles.RationalChow

@[expose] public section

/-!
# Actual rational Chow classes of closed graphs

The existing field dimension function makes every closed graph homogeneous
of the dimension of its integral source. This degree is derived from the
actual graph-subscheme isomorphism. Linear graph assembly therefore lands
in homogeneous cycles and then in their existing principal-relation
quotient. No multiplication on Chow classes is assumed or defined here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u

variable (k : Type u) [Field k] {X S : Scheme.{u}}
variable (p : X ⟶ S) (b : S ⟶ Spec (CommRingCat.of k))

/-- The actual structural morphism of the relative pair product over the field. -/
def graphPairStructure : pullback p p ⟶ Spec (CommRingCat.of k) :=
  pullback.fst p p ≫ p ≫ b

/-- The existing field-induced dimension function on the relative pair product. -/
def graphPairDimensionFunction [LocallyOfFiniteType (graphPairStructure k p b)] :
    DimensionFunction (pullback p p) :=
  DimensionFunction.ofLocallyOfFiniteType k (pullback p p) (graphPairStructure k p b)

/-- The field-induced dimension of the actual integral source, at its generic point. -/
def graphChowDimension [IsIntegral X] [LocallyOfFiniteType (p ≫ b)] : ℤ :=
  DimensionFunction.ofLocallyOfFiniteType k X (p ≫ b) (genericPoint X)

theorem graphChowDimension_nonneg [IsIntegral X] [LocallyOfFiniteType (p ≫ b)] :
    0 ≤ graphChowDimension k p b :=
  DimensionFunction.ofLocallyOfFiniteType_nonneg k X (p ≫ b) (genericPoint X)

/-- The source dimension is finite and has the prescribed canonical field degree. -/
theorem topologicalKrullDim_eq_graphChowDimension
    [IsIntegral X] [LocallyOfFiniteType (p ≫ b)] :
    topologicalKrullDim X = ((graphChowDimension k p b).toNat : WithBot ℕ∞) := by
  rw [← genericPoint_height_eq_topologicalKrullDim X,
    point_height_eq_ofLocallyOfFiniteType k X (p ≫ b)]
  rfl

/-- The graph has the canonical source degree, through its actual scheme isomorphism. -/
theorem graphIntegralSubscheme_supportDegree
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (σ : DeckTransformation p) :
    supportDegree (graphPairDimensionFunction k p b) (graphIntegralSubscheme p σ) =
      graphChowDimension k p b := by
  have h := (supportDegree_ofLocallyOfFiniteType_eq_iff k (pullback p p)
    (graphPairStructure k p b) (graphIntegralSubscheme p σ)
      (graphChowDimension k p b).toNat).mpr (by
        change topologicalKrullDim (graphIdeal p σ).subscheme = _
        rw [graphIdeal_topologicalKrullDim, topologicalKrullDim_eq_graphChowDimension k p b])
  simpa only [graphPairDimensionFunction,
    Int.toNat_of_nonneg (graphChowDimension_nonneg k p b)] using h

/-- The actual rational graph cycle inside the existing homogeneous cycle submodule. -/
def gradedGraphCycle
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (σ : DeckTransformation p) :
    cyclesOfDegree ℚ (graphPairDimensionFunction k p b) (graphChowDimension k p b) :=
  ⟨graphCycle p ℚ σ,
    fundamentalCycle_mem_cyclesOfDegree ℚ (graphPairDimensionFunction k p b)
      (graphChowDimension k p b) (graphIntegralSubscheme p σ)
      (graphIntegralSubscheme_supportDegree k p b σ)⟩

@[simp]
theorem gradedGraphCycle_val
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (σ : DeckTransformation p) :
    (gradedGraphCycle k p b σ).val = graphCycle p ℚ σ := rfl

/-- Linear assembly of actual homogeneous rational graph cycles. -/
def gradedGraphCycleLinearMap
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] :
    MonoidAlgebra ℚ (DeckTransformation p) →ₗ[ℚ]
      cyclesOfDegree ℚ (graphPairDimensionFunction k p b) (graphChowDimension k p b) :=
  (Finsupp.linearCombination ℚ (gradedGraphCycle k p b)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp]
theorem gradedGraphCycleLinearMap_single
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (σ : DeckTransformation p) (q : ℚ) :
    gradedGraphCycleLinearMap k p b (MonoidAlgebra.single σ q) =
      q • gradedGraphCycle k p b σ := by
  simp [gradedGraphCycleLinearMap]

/-- Forgetting homogeneity recovers the original actual graph-cycle map. -/
theorem gradedGraphCycleLinearMap_subtype
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] :
    (cyclesOfDegree ℚ (graphPairDimensionFunction k p b) (graphChowDimension k p b)).subtype.comp
        (gradedGraphCycleLinearMap k p b) = graphCycleLinearMap p := by
  apply (LinearMap.cancel_right (MonoidAlgebra.coeffLinearEquiv ℚ).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro σ q
  change (gradedGraphCycleLinearMap k p b (MonoidAlgebra.single σ q)).val =
    graphCycleLinearMap p (MonoidAlgebra.single σ q)
  rw [gradedGraphCycleLinearMap_single, graphCycleLinearMap_single]
  rfl

@[simp]
theorem gradedGraphCycleLinearMap_val
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (ζ : MonoidAlgebra ℚ (DeckTransformation p)) :
    (gradedGraphCycleLinearMap k p b ζ).val = graphCycleLinearMap p ζ :=
  LinearMap.congr_fun (gradedGraphCycleLinearMap_subtype k p b) ζ

/-- The class of the actual rational graph in the existing Chow quotient. -/
def graphChowClass
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)]
    (σ : DeckTransformation p) :
    RationalChowGroup (graphPairDimensionFunction k p b) (graphChowDimension k p b) :=
  rationalClassMap (graphPairDimensionFunction k p b) (graphChowDimension k p b)
    (gradedGraphCycle k p b σ)

/-- Linear graph assembly followed by the actual rational Chow class map. -/
def graphChowLinearMap
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)] :
    MonoidAlgebra ℚ (DeckTransformation p) →ₗ[ℚ]
      RationalChowGroup (graphPairDimensionFunction k p b) (graphChowDimension k p b) :=
  (rationalClassMap (graphPairDimensionFunction k p b) (graphChowDimension k p b)).comp
    (gradedGraphCycleLinearMap k p b)

@[simp]
theorem graphChowLinearMap_apply
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)]
    (ζ : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowLinearMap k p b ζ =
      rationalClassMap (graphPairDimensionFunction k p b) (graphChowDimension k p b)
        (gradedGraphCycleLinearMap k p b ζ) := rfl

@[simp]
theorem graphChowLinearMap_single
    [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
    [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)]
    (σ : DeckTransformation p) (q : ℚ) :
    graphChowLinearMap k p b (MonoidAlgebra.single σ q) =
      q • graphChowClass k p b σ := by
  rw [graphChowLinearMap_apply, gradedGraphCycleLinearMap_single, map_smul]
  rfl

end

end HodgeConjecture.SchemeCorrespondence
