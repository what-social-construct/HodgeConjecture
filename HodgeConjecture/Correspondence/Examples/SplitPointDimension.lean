module

public import HodgeConjecture.Correspondence.Examples.SplitPointMaps
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Zero-dimensional topology of finite split schemes

The underlying topology of `Spec (I → K)` is discrete. Its irreducible
closed subsets are therefore singletons, and every closed subscheme has
topological Krull dimension at most zero. In particular there are no
one-dimensional integral closed subschemes from which rational-equivalence
relations on zero-cycles could arise.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K] (I : Type u) [Finite I]

instance discreteTopology : DiscreteTopology (scheme K I) := by
  change DiscreteTopology (PrimeSpectrum (I → K))
  infer_instance

/-- Every irreducible subset of a finite split scheme is a point. -/
theorem isIrreducible_iff_point (s : Set (scheme K I)) :
    IsIrreducible s ↔ ∃ i : I, s = {labelEquivScheme K I i} := by
  rw [isIrreducible_iff_singleton]
  exact (labelEquivScheme K I).surjective.exists

/-- The image of an irreducible scheme in a finite split scheme is a single point. -/
theorem range_eq_point {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ scheme K I) :
    ∃ i : I, Set.range f.base = {labelEquivScheme K I i} := by
  apply (isIrreducible_iff_point K I _).mp
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ X).image f.base f.continuous.continuousOn

/-- The split finite scheme has no nontrivial chain of irreducible closed subsets. -/
theorem topologicalKrullDim_le_zero : topologicalKrullDim (scheme K I) ≤ 0 := by
  apply Order.krullDim_nonpos_iff_forall_isMax.mpr
  intro s t hst
  obtain ⟨i, hi⟩ := (isIrreducible_iff_point K I s) |>.mp s.isIrreducible
  obtain ⟨j, hj⟩ := (isIrreducible_iff_point K I t) |>.mp t.isIrreducible
  change (t : Set (scheme K I)) ⊆ s
  change (s : Set (scheme K I)) ⊆ t at hst
  rw [hi, hj] at hst ⊢
  exact Set.singleton_subset_singleton.mpr (Set.singleton_subset_singleton.mp hst).symm

/-- Every actual closed subscheme of the split finite scheme has dimension at most zero. -/
theorem topologicalKrullDim_le_zero_of_isClosedImmersion
    {X : Scheme.{u}} (f : X ⟶ scheme K I) [IsClosedImmersion f] :
    topologicalKrullDim X ≤ 0 :=
  (f.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans
    (topologicalKrullDim_le_zero K I)

/-- A nonempty actual closed subscheme has dimension exactly zero. -/
theorem topologicalKrullDim_eq_zero_of_isClosedImmersion
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ scheme K I) [IsClosedImmersion f] :
    topologicalKrullDim X = 0 := by
  let x : X := Classical.choice inferInstance
  letI : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_le_zero_of_isClosedImmersion K I f)
    Order.krullDim_nonneg

/-- No actual closed subscheme of a finite split scheme has dimension at least one. -/
theorem not_one_le_topologicalKrullDim_of_isClosedImmersion
    {X : Scheme.{u}} (f : X ⟶ scheme K I) [IsClosedImmersion f] :
    ¬ 1 ≤ topologicalKrullDim X :=
  not_le_of_gt ((topologicalKrullDim_le_zero_of_isClosedImmersion K I f).trans_lt
    zero_lt_one)

end SplitPointGeometry

end

end HodgeConjecture
