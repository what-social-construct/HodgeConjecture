module

public import HodgeConjecture.Correspondence.GraphChowAction
public import HodgeConjecture.Correspondence.FiniteGroupProjector
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Convolution on the actual graph-generated rational Chow classes

The kernel of the actual graph-to-Chow map is a two-sided ideal: its left
and right stability follow from the actual pair-isomorphism pullbacks on
Chow groups. The quotient by this exact kernel is consequently a rational
convolution algebra. Its injective linear realization identifies it with
the range of the actual graph-to-Chow map. Thus this algebra has
precisely the equalities of actual graph-generated Chow classes, including
their rational-equivalence relations.

Multiplication by graph classes is the actual geometric left or right
pullback. This construction defines no intersection product on the whole
ambient Chow group.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u v

variable (k : Type u) [Field k] {X S : Scheme.{u}}
variable (p : X ⟶ S) (b : S ⟶ Spec (CommRingCat.of k))
variable [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
variable [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)]

/-- The exact kernel of the actual rational graph-Chow map, as a left ideal.
Left stability is supplied by genuine Chow pullback along the pair isomorphisms. -/
def graphChowKernelIdeal : Ideal (MonoidAlgebra ℚ (DeckTransformation p)) where
  carrier := {a | graphChowLinearMap k p b a = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro a c ha hc
    change graphChowLinearMap k p b (a + c) = 0
    rw [map_add, ha, hc, add_zero]
  smul_mem' := by
    intro a c hc
    change graphChowLinearMap k p b c = 0 at hc
    change graphChowLinearMap k p b (a * c) = 0
    rw [← graphChowLeftLinearAction_graphChowLinearMap k p b, hc, map_zero]

@[simp]
theorem mem_graphChowKernelIdeal (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    a ∈ graphChowKernelIdeal k p b ↔ graphChowLinearMap k p b a = 0 := Iff.rfl

/-- Right stability follows independently from the genuine right Chow pullbacks. -/
instance graphChowKernelIdeal_isTwoSided : (graphChowKernelIdeal k p b).IsTwoSided where
  mul_mem_of_left := by
    intro c a hc
    change graphChowLinearMap k p b c = 0 at hc
    change graphChowLinearMap k p b (c * a) = 0
    rw [← graphChowRightLinearAction_graphChowLinearMap k p b, hc, map_zero]

/-- As a rational submodule this ideal is exactly the actual Chow kernel. -/
theorem graphChowKernelIdeal_restrictScalars :
    (graphChowKernelIdeal k p b).restrictScalars ℚ =
      LinearMap.ker (graphChowLinearMap k p b) := by
  ext a
  rfl

/-- The rational convolution algebra of graph-generated actual Chow classes.
Its defining quotient uses the actual Chow kernel, not a free graph span. -/
abbrev GraphChowAlgebra :=
  MonoidAlgebra ℚ (DeckTransformation p) ⧸ graphChowKernelIdeal k p b

/-- The canonical rational algebra map from deck group algebra to graph Chow convolution. -/
def graphChowAlgHom :
    MonoidAlgebra ℚ (DeckTransformation p) →ₐ[ℚ] GraphChowAlgebra k p b :=
  Ideal.Quotient.mkₐ ℚ (graphChowKernelIdeal k p b)

theorem graphChowAlgHom_surjective : Function.Surjective (graphChowAlgHom k p b) :=
  Ideal.Quotient.mkₐ_surjective _ _

/-- Every group-algebra idempotent descends through the actual Chow kernel. -/
theorem graphChowAlgHom_isIdempotent (a : MonoidAlgebra ℚ (DeckTransformation p))
    (ha : IsIdempotentElem a) : IsIdempotentElem (graphChowAlgHom k p b a) :=
  ha.map (graphChowAlgHom k p b)

/-- Equality in the convolution algebra is exactly equality of the actual Chow classes. -/
theorem graphChowAlgHom_eq_iff (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowAlgHom k p b a = graphChowAlgHom k p b c ↔
      graphChowLinearMap k p b a = graphChowLinearMap k p b c := by
  change Ideal.Quotient.mk (graphChowKernelIdeal k p b) a =
    Ideal.Quotient.mk (graphChowKernelIdeal k p b) c ↔ _
  rw [Ideal.Quotient.eq]
  change graphChowLinearMap k p b (a - c) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- The quotient algebra realizes injectively inside the existing rational Chow group. -/
def graphChowRealization :
    GraphChowAlgebra k p b →ₗ[ℚ]
      RationalChowGroup (graphPairDimensionFunction k p b) (graphChowDimension k p b) :=
  ((graphChowKernelIdeal k p b).restrictScalars ℚ).liftQ (graphChowLinearMap k p b)
    (by intro a ha; exact ha)

@[simp]
theorem graphChowRealization_graphChowAlgHom
    (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowRealization k p b (graphChowAlgHom k p b a) =
      graphChowLinearMap k p b a := rfl

theorem graphChowRealization_injective : Function.Injective (graphChowRealization k p b) := by
  intro x y h
  obtain ⟨a, rfl⟩ := graphChowAlgHom_surjective k p b x
  obtain ⟨c, rfl⟩ := graphChowAlgHom_surjective k p b y
  exact (graphChowAlgHom_eq_iff k p b a c).mpr h

/-- The realization has exactly the range of the actual graph-Chow map. -/
theorem graphChowRealization_range :
    LinearMap.range (graphChowRealization k p b) =
      LinearMap.range (graphChowLinearMap k p b) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := graphChowAlgHom_surjective k p b x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨graphChowAlgHom k p b a, rfl⟩

/-- Explicit linear identification with the actual graph-generated Chow submodule. -/
def graphChowRangeEquiv :
    GraphChowAlgebra k p b ≃ₗ[ℚ] LinearMap.range (graphChowLinearMap k p b) :=
  (LinearEquiv.ofInjective (graphChowRealization k p b)
    (graphChowRealization_injective k p b)).trans
      (LinearEquiv.ofEq _ _ (graphChowRealization_range k p b))

@[simp]
theorem graphChowRangeEquiv_apply (z : GraphChowAlgebra k p b) :
    (graphChowRangeEquiv k p b z).val = graphChowRealization k p b z := rfl

/-- The convolution generator represented by the actual closed graph of a deck transformation. -/
def graphChowGenerator (σ : DeckTransformation p) : GraphChowAlgebra k p b :=
  graphChowAlgHom k p b (MonoidAlgebra.single σ 1)

@[simp]
theorem graphChowRealization_generator (σ : DeckTransformation p) :
    graphChowRealization k p b (graphChowGenerator k p b σ) =
      graphChowClass k p b σ := by
  rw [graphChowGenerator, graphChowRealization_graphChowAlgHom,
    graphChowLinearMap_single, one_smul]

@[simp]
theorem graphChowGenerator_mul (σ τ : DeckTransformation p) :
    graphChowGenerator k p b σ * graphChowGenerator k p b τ =
      graphChowGenerator k p b (σ * τ) := by
  simp [graphChowGenerator, ← map_mul, MonoidAlgebra.single_mul_single]

@[simp]
theorem graphChowGenerator_one : graphChowGenerator k p b 1 = 1 := by
  exact map_one (graphChowAlgHom k p b)

/-- The convolution unit realizes as the actual diagonal graph class. -/
@[simp]
theorem graphChowRealization_one :
    graphChowRealization k p b 1 = graphChowClass k p b 1 := by
  rw [← graphChowGenerator_one k p b, graphChowRealization_generator]

/-- Multiplication on the left is characterized by actual linearized Chow pullback. -/
theorem graphChowRealization_mul_left
    (a : MonoidAlgebra ℚ (DeckTransformation p)) (z : GraphChowAlgebra k p b) :
    graphChowRealization k p b (graphChowAlgHom k p b a * z) =
      graphChowLeftLinearAction k p b (graphChowDimension k p b) a
        (graphChowRealization k p b z) := by
  obtain ⟨c, rfl⟩ := graphChowAlgHom_surjective k p b z
  rw [← map_mul, graphChowRealization_graphChowAlgHom,
    graphChowRealization_graphChowAlgHom,
    graphChowLeftLinearAction_graphChowLinearMap]

/-- Multiplication on the right is characterized by actual linearized Chow pullback. -/
theorem graphChowRealization_mul_right
    (z : GraphChowAlgebra k p b) (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowRealization k p b (z * graphChowAlgHom k p b a) =
      graphChowRightLinearAction k p b (graphChowDimension k p b) a
        (graphChowRealization k p b z) := by
  obtain ⟨c, rfl⟩ := graphChowAlgHom_surjective k p b z
  rw [← map_mul, graphChowRealization_graphChowAlgHom,
    graphChowRealization_graphChowAlgHom,
    graphChowRightLinearAction_graphChowLinearMap]

/-- Left multiplication by a graph uses its genuine pair-isomorphism Chow pullback. -/
theorem graphChowRealization_generator_mul (σ : DeckTransformation p)
    (z : GraphChowAlgebra k p b) :
    graphChowRealization k p b (graphChowGenerator k p b σ * z) =
      graphChowLeftAction k p b (graphChowDimension k p b) σ
        (graphChowRealization k p b z) := by
  simp [graphChowGenerator, graphChowRealization_mul_left]

/-- Right multiplication by a graph uses its genuine pair-isomorphism Chow pullback. -/
theorem graphChowRealization_mul_generator (z : GraphChowAlgebra k p b)
    (τ : DeckTransformation p) :
    graphChowRealization k p b (z * graphChowGenerator k p b τ) =
      graphChowRightAction k p b (graphChowDimension k p b) τ
        (graphChowRealization k p b z) := by
  simp [graphChowGenerator, graphChowRealization_mul_right]

section FiniteAction

variable {G : Type v} [Group G]

/-- The actual graph-Chow algebra map of an action by deck transformations. -/
def graphChowActionAlgHom (α : FiniteDeckAction p G) :
    MonoidAlgebra ℚ G →ₐ[ℚ] GraphChowAlgebra k p b :=
  (graphChowAlgHom k p b).comp (α.toDeckGroupAlgebra p)

@[simp]
theorem graphChowActionAlgHom_single (α : FiniteDeckAction p G) (g : G) :
    graphChowActionAlgHom k p b α (MonoidAlgebra.single g 1) =
      graphChowGenerator k p b (α g) := by
  simp [graphChowActionAlgHom, graphChowGenerator]

variable [Fintype G]

/-- The normalized graph average in the actual graph-generated Chow convolution algebra. -/
def graphChowAveragingProjector (α : FiniteDeckAction p G) : GraphChowAlgebra k p b :=
  graphChowActionAlgHom k p b α (finiteGroupAverage G)

theorem graphChowAveragingProjector_eq_sum (α : FiniteDeckAction p G) :
    graphChowAveragingProjector k p b α =
      (Fintype.card G : ℚ)⁻¹ • ∑ g : G, graphChowGenerator k p b (α g) := by
  simp [graphChowAveragingProjector, finiteGroupAverage, finiteGroupSum]

/-- The projector realizes as the normalized sum of actual Chow classes of its graphs. -/
theorem graphChowRealization_averagingProjector (α : FiniteDeckAction p G) :
    graphChowRealization k p b (graphChowAveragingProjector k p b α) =
      (Fintype.card G : ℚ)⁻¹ • ∑ g : G, graphChowClass k p b (α g) := by
  simp [graphChowAveragingProjector_eq_sum]

/-- The actual Chow graph average is a convolution idempotent. -/
theorem graphChowAveragingProjector_isIdempotent (α : FiniteDeckAction p G) :
    IsIdempotentElem (graphChowAveragingProjector k p b α) :=
  (finiteGroupAverage_isIdempotent G).map (graphChowActionAlgHom k p b α)

@[simp]
theorem graphChowGenerator_mul_average (α : FiniteDeckAction p G) (g : G) :
    graphChowGenerator k p b (α g) * graphChowAveragingProjector k p b α =
      graphChowAveragingProjector k p b α := by
  rw [← graphChowActionAlgHom_single k p b α g, graphChowAveragingProjector,
    ← map_mul, single_mul_finiteGroupAverage]

@[simp]
theorem graphChowAverage_mul_generator (α : FiniteDeckAction p G) (g : G) :
    graphChowAveragingProjector k p b α * graphChowGenerator k p b (α g) =
      graphChowAveragingProjector k p b α := by
  rw [← graphChowActionAlgHom_single k p b α g, graphChowAveragingProjector,
    ← map_mul, finiteGroupAverage_mul_single]

/-- The complementary projector in actual graph-generated Chow convolution. -/
def graphChowComplementaryProjector (α : FiniteDeckAction p G) : GraphChowAlgebra k p b :=
  1 - graphChowAveragingProjector k p b α

/-- The complementary projector has the actual diagonal-minus-average Chow class. -/
theorem graphChowRealization_complementaryProjector (α : FiniteDeckAction p G) :
    graphChowRealization k p b (graphChowComplementaryProjector k p b α) =
      graphChowClass k p b 1 -
        (Fintype.card G : ℚ)⁻¹ • ∑ g : G, graphChowClass k p b (α g) := by
  rw [graphChowComplementaryProjector, map_sub, graphChowRealization_one,
    graphChowRealization_averagingProjector]

theorem graphChowComplementaryProjector_isIdempotent (α : FiniteDeckAction p G) :
    IsIdempotentElem (graphChowComplementaryProjector k p b α) :=
  (graphChowAveragingProjector_isIdempotent k p b α).one_sub

@[simp]
theorem graphChowAveragingProjector_mul_complement (α : FiniteDeckAction p G) :
    graphChowAveragingProjector k p b α * graphChowComplementaryProjector k p b α = 0 :=
  (graphChowAveragingProjector_isIdempotent k p b α).mul_one_sub_self

@[simp]
theorem graphChowComplementaryProjector_mul_average (α : FiniteDeckAction p G) :
    graphChowComplementaryProjector k p b α * graphChowAveragingProjector k p b α = 0 :=
  (graphChowAveragingProjector_isIdempotent k p b α).one_sub_mul_self

/-- The orthogonal pair adds to the convolution unit. -/
@[simp]
theorem graphChowAveragingProjector_add_complement (α : FiniteDeckAction p G) :
    graphChowAveragingProjector k p b α + graphChowComplementaryProjector k p b α = 1 := by
  simp [graphChowComplementaryProjector]

/-- The actual classes of the average and complement decompose the diagonal graph class. -/
theorem graphChowRealization_average_add_complement (α : FiniteDeckAction p G) :
    graphChowRealization k p b (graphChowAveragingProjector k p b α) +
        graphChowRealization k p b (graphChowComplementaryProjector k p b α) =
      graphChowClass k p b 1 := by
  rw [← map_add, graphChowAveragingProjector_add_complement, graphChowRealization_one]

end FiniteAction

section Subgroup

variable {G : Type v} [Group G] (H : Subgroup G) [Fintype H]

/-- The actual Chow projector obtained by averaging a finite subgroup of an action. -/
def graphChowSubgroupProjector (α : FiniteDeckAction p G) : GraphChowAlgebra k p b :=
  graphChowAveragingProjector k p b (α.restrict p H)

theorem graphChowSubgroupProjector_isIdempotent (α : FiniteDeckAction p G) :
    IsIdempotentElem (graphChowSubgroupProjector k p b H α) :=
  graphChowAveragingProjector_isIdempotent k p b (α.restrict p H)

/-- Subgroup averaging is the explicit normalized sum in the existing rational Chow group. -/
theorem graphChowRealization_subgroupProjector (α : FiniteDeckAction p G) :
    graphChowRealization k p b (graphChowSubgroupProjector k p b H α) =
      (Fintype.card H : ℚ)⁻¹ • ∑ h : H, graphChowClass k p b (α h) := by
  simpa [graphChowSubgroupProjector] using
    graphChowRealization_averagingProjector k p b (α.restrict p H)

end Subgroup

end

end HodgeConjecture.SchemeCorrespondence
