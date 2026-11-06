/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Sources: Chow/FlatPullback/InverseImageDimension.lean and
Chow/RationalEquivalence/FlatPullbackPrincipalDivisor.lean.
Only dominance of the actual reduced irreducible components is retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.Cycles.ComponentStalk
public import HodgeConjecture.Cycles.FunctionFieldMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace HodgeConjecture.SchemeCycles

noncomputable section

/-- The generic point of an irreducible component generates it. -/
private theorem isGenericPoint_genericPoint_component {P : Scheme.{u}}
    (W : irreducibleComponents P) : IsGenericPoint W.2.1.genericPoint (W : Set P) :=
  W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)

/-- A generization of the generic point of an irreducible component generates that component. -/
private theorem isGenericPoint_of_specializes_genericPoint {P : Scheme.{u}}
    (W : irreducibleComponents P) {y : P} (h : y ⤳ W.2.1.genericPoint) :
    IsGenericPoint y (W : Set P) := by
  have hsub : (W : Set P) ⊆ closure ({y} : Set P) := by
    rw [← isGenericPoint_genericPoint_component W]
    exact closure_minimal (Set.singleton_subset_iff.mpr h.mem_closure) isClosed_closure
  exact Set.Subset.antisymm (W.2.2 isIrreducible_singleton.closure hsub) hsub

/-- Along a flat morphism the generic point of an irreducible component maps to the generic
point of an irreducible component: a flat morphism lifts generalizations, so the generization
of the image lifts to a generization of the point, which must be the point itself. -/
theorem exists_irreducibleComponent_map_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    (W : irreducibleComponents P) :
    ∃ V : irreducibleComponents Z,
      p.base W.2.1.genericPoint = genericPoints.ofComponent V := by
  set ξ : P := W.2.1.genericPoint with hξdef
  set V : irreducibleComponents Z :=
    ⟨irreducibleComponent (p.base ξ), irreducibleComponent_mem_irreducibleComponents _⟩ with hVdef
  have hξW : IsGenericPoint ξ (W : Set P) := isGenericPoint_genericPoint_component W
  have hηx : (genericPoints.ofComponent V : Z) ⤳ p.base ξ :=
    (genericPoints.isGenericPoint_ofComponent V).specializes mem_irreducibleComponent
  obtain ⟨ξ', hξ'ξ, hξ'η⟩ := Flat.generalizingMap p hηx
  exact ⟨V, by rw [← (isGenericPoint_of_specializes_genericPoint W hξ'ξ).eq hξW]; exact hξ'η⟩

/-- Over an irreducible base, the generic point of an irreducible component of the source of a
flat morphism maps to the generic point of the base: there is only one irreducible component
downstairs. -/
theorem map_genericPoint_irreducibleComponent_eq_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z)
    [Flat p] [IrreducibleSpace Z] (W : irreducibleComponents P) :
    p.base W.2.1.genericPoint = genericPoint Z := by
  obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint p W
  have hVU : (V : Set Z) = Set.univ :=
    Set.eq_univ_of_univ_subset (V.2.2 (IrreducibleSpace.isIrreducible_univ Z) (Set.subset_univ _))
  have hg : IsGenericPoint (genericPoints.ofComponent V : Z) (Set.univ : Set Z) := by
    simpa only [hVU] using genericPoints.isGenericPoint_ofComponent V
  exact hV.trans (hg.eq (genericPoint_spec Z))

/-- Over an irreducible base, the image of an irreducible component of the source of a flat
morphism is dense: the component's generic point lies over the generic point of the base, which
is dense. -/
theorem dense_image_irreducibleComponent {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    [IrreducibleSpace Z] (W : irreducibleComponents P) :
    closure (p.base '' (W : Set P)) = Set.univ := by
  have hmem : genericPoint Z ∈ p.base '' (W : Set P) :=
    ⟨W.2.1.genericPoint,
      (isGenericPoint_genericPoint_component W).mem,
      map_genericPoint_irreducibleComponent_eq_genericPoint p W⟩
  refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
  exact (genericPoint_specializes z).mem_closed isClosed_closure (subset_closure hmem)

/-- The existing point-closure object at a component's generic point has exactly the
component as its closed support. -/
theorem pointSupport_component_support {X : Scheme.{u}} (W : irreducibleComponents X) :
    ((pointSupport X W.2.1.genericPoint).val.support : Set X) = W := by
  rw [pointSupport_support, Closeds.coe_closure]
  exact isGenericPoint_genericPoint_component W

/-- Every actual reduced component of a scheme flat over an integral scheme dominates
that scheme, through its existing closed immersion. -/
theorem pointSupport_component_isDominant_comp {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] (W : irreducibleComponents X) :
    IsDominant ((pointSupport X W.2.1.genericPoint).val.subschemeι ≫ f) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  have hrange : Set.range ((pointSupport X W.2.1.genericPoint).val.subschemeι ≫ f).base =
      f.base '' (W : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, pointSupport_component_support]
  rw [hrange]
  exact dense_image_irreducibleComponent f W

end

end HodgeConjecture.SchemeCycles
