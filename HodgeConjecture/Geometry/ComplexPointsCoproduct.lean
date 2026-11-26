module

public import HodgeConjecture.Geometry.ComplexPointsFunctoriality
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

/-!
# Canonical analytic complex points of a scheme coproduct

The actual open coproduct inclusions induce a homeomorphism from the
topological disjoint union of the component complex-point spaces. Its
codomain retains any supplied structure morphism on the original coproduct;
the two compatibility equalities identify its component structures exactly.
No replacement topology or choice of affine coordinates is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.Scheme.ComplexPoints

open CategoryTheory CategoryTheory.Limits Topology

variable {X Y : Scheme.{0}}
  (p : X ⟶ Spec (.of ℂ)) (q : Y ⟶ Spec (.of ℂ))
  (r : X ⨿ Y ⟶ Spec (.of ℂ))
  (hp : (coprod.inl : X ⟶ X ⨿ Y) ≫ r = p)
  (hq : (coprod.inr : Y ⟶ X ⨿ Y) ≫ r = q)

/-- The two original scheme inclusions acting on actual complex points. -/
def coprodPointMap : (ComplexPoints p ⊕ ComplexPoints q) → ComplexPoints r :=
  Sum.elim (map coprod.inl hp) (map coprod.inr hq)

theorem coprodPointMap_injective : Function.Injective (coprodPointMap p q r hp hq) := by
  apply Sum.elim_injective.mpr
  refine ⟨injective_map_of_mono coprod.inl hp,
    injective_map_of_mono coprod.inr hq, ?_⟩
  intro a b hab
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have h := congrArg (fun z : ComplexPoints r => z.hom pt) hab
  change (a.hom ≫ coprod.inl) pt = (b.hom ≫ coprod.inr) pt at h
  simp only [Scheme.Hom.comp_apply] at h
  exact AlgebraicGeometry.inl_ne_inr X Y (a.hom pt) (b.hom pt) h

theorem coprodPointMap_surjective : Function.Surjective (coprodPointMap p q r hp hq) := by
  intro z
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨x | y, hxy⟩ := (AlgebraicGeometry.coprodMk X Y).surjective (z.hom pt)
  · have hz : z ∈ Set.range (map (coprod.inl : X ⟶ X ⨿ Y) hp) := by
      rw [range_map_of_isOpenImmersion]
      apply (mem_iff pt).2
      exact ⟨x, (AlgebraicGeometry.coprodMk_inl X Y x).symm.trans hxy⟩
    obtain ⟨a, ha⟩ := hz
    exact ⟨Sum.inl a, ha⟩
  · have hz : z ∈ Set.range (map (coprod.inr : Y ⟶ X ⨿ Y) hq) := by
      rw [range_map_of_isOpenImmersion]
      apply (mem_iff pt).2
      exact ⟨y, (AlgebraicGeometry.coprodMk_inr X Y y).symm.trans hxy⟩
    obtain ⟨b, hb⟩ := hz
    exact ⟨Sum.inr b, hb⟩

theorem coprodPointMap_isOpenEmbedding : IsOpenEmbedding (coprodPointMap p q r hp hq) :=
  (isOpenEmbedding_map_of_isOpenImmersion coprod.inl hp).sumElim
    (isOpenEmbedding_map_of_isOpenImmersion coprod.inr hq)
    (coprodPointMap_injective p q r hp hq)

/-- Canonical analytic coproduct comparison, preserving the original structure map. -/
def coprodHomeomorph :
    (ComplexPoints p ⊕ ComplexPoints q) ≃ₜ ComplexPoints r :=
  (coprodPointMap_isOpenEmbedding p q r hp hq).isEmbedding.toHomeomorphOfSurjective
    (coprodPointMap_surjective p q r hp hq)

@[simp]
theorem coprodHomeomorph_inl (a : ComplexPoints p) :
    coprodHomeomorph p q r hp hq (Sum.inl a) = map coprod.inl hp a := rfl

@[simp]
theorem coprodHomeomorph_inr (b : ComplexPoints q) :
    coprodHomeomorph p q r hp hq (Sum.inr b) = map coprod.inr hq b := rfl

end AlgebraicGeometry.Scheme.ComplexPoints

end
