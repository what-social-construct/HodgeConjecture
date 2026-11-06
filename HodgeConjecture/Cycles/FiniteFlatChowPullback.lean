module

public import HodgeConjecture.Cycles.FiniteFlatPrincipalRelations
public import HodgeConjecture.Cycles.RationalChow

@[expose] public section

/-! The existing integral and rational Chow quotients carry the original
finite flat fiber pullback, with preservation of principal relations proved. -/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Quotient descent of the original integral cycle pullback. -/
def chowFiniteFlatPullback
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) :
    ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n →ₗ[ℤ]
      ChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n :=
  (principalRelations (DimensionFunction.ofLocallyOfFiniteType k Y pY) n).mapQ
    (principalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n)
    (gradedFiniteFiberPullback f k ℤ pY n)
    (principalRelations_le_comap_finiteFlatPullback k pY f n)

@[simp]
theorem chowFiniteFlatPullback_classMap
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ)
    (c : cyclesOfDegree ℤ (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    chowFiniteFlatPullback k pY f n
        (classMap (DimensionFunction.ofLocallyOfFiniteType k Y pY) n c) =
      classMap (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n
        (gradedFiniteFiberPullback f k ℤ pY n c) := rfl

/-- Graded coefficient extension retains the original finite-fiber pullback. -/
theorem gradedFiniteFiberPullback_rationalize
    (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY] (n : ℤ)
    (c : cyclesOfDegree ℤ (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    gradedFiniteFiberPullback f k ℚ pY n
        (cyclesOfDegreeRationalize (DimensionFunction.ofLocallyOfFiniteType k Y pY) n c) =
      cyclesOfDegreeRationalize (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n
        (gradedFiniteFiberPullback f k ℤ pY n c) := by
  apply Subtype.ext
  exact finiteFiberPullback_rationalize f c.val

/-- Rationalizing any actual integral principal relation gives a member of the original
rational relation span. -/
theorem cyclesOfDegreeRationalize_mem_relations {X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ) (c : cyclesOfDegree ℤ δ n)
    (hc : c ∈ principalRelations δ n) :
    cyclesOfDegreeRationalize δ n c ∈ rationalPrincipalRelations δ n := by
  apply (rationalClassMap_eq_zero_iff δ n _).mp
  rw [← chowRationalize_classMap, (classMap_eq_zero_iff δ n c).mpr hc, map_zero]

/-- Preservation of rational relations follows from integral preservation and the proved
coefficient comparison of the same cycle pullbacks. -/
theorem rationalPrincipalRelations_le_comap_finiteFlatPullback
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) :
    rationalPrincipalRelations (DimensionFunction.ofLocallyOfFiniteType k Y pY) n ≤
      (rationalPrincipalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n).comap
        (gradedFiniteFiberPullback f k ℚ pY n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedFiniteFiberPullback f k ℚ pY n
      (cyclesOfDegreeRationalize (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
        (principalRelation (DimensionFunction.ofLocallyOfFiniteType k Y pY) n d)) ∈
    rationalPrincipalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n
  rw [gradedFiniteFiberPullback_rationalize]
  exact cyclesOfDegreeRationalize_mem_relations _ n _
    (gradedFiniteFiberPullback_principalRelation_mem k pY f n d)

/-- Quotient descent of the original rational cycle pullback. -/
def rationalChowFiniteFlatPullback
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) :
    RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n →ₗ[ℚ]
      RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n :=
  (rationalPrincipalRelations (DimensionFunction.ofLocallyOfFiniteType k Y pY) n).mapQ
    (rationalPrincipalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n)
    (gradedFiniteFiberPullback f k ℚ pY n)
    (rationalPrincipalRelations_le_comap_finiteFlatPullback k pY f n)

@[simp]
theorem rationalChowFiniteFlatPullback_classMap
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ)
    (c : cyclesOfDegree ℚ (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    rationalChowFiniteFlatPullback k pY f n
        (rationalClassMap (DimensionFunction.ofLocallyOfFiniteType k Y pY) n c) =
      rationalClassMap (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n
        (gradedFiniteFiberPullback f k ℚ pY n c) := rfl

/-- Integral Chow rationalization commutes with this same finite flat pullback. -/
theorem rationalChowFiniteFlatPullback_rationalize
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ)
    (c : ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    rationalChowFiniteFlatPullback k pY f n
        (chowRationalize (DimensionFunction.ofLocallyOfFiniteType k Y pY) n c) =
      chowRationalize (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n
        (chowFiniteFlatPullback k pY f n c) := by
  obtain ⟨c, rfl⟩ := classMap_surjective _ n c
  rw [chowRationalize_classMap, rationalChowFiniteFlatPullback_classMap,
    chowFiniteFlatPullback_classMap, chowRationalize_classMap,
    gradedFiniteFiberPullback_rationalize]

end

end HodgeConjecture.SchemeCycles
