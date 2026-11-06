module

public import HodgeConjecture.Boundary.Sheets.MarkedBlockProjector
public import HodgeConjecture.Cycles.RationalChowOpenRestriction
public import HodgeConjecture.Cycles.RationalFiniteChowPushforward

@[expose] public section

/-!
# Marked sheet coefficients on actual homogeneous cycles

For a fixed ambient scheme, degree and family of actual homogeneous cycles
`C s`, form the cycle `∑ s, x(s) • C s` and take its existing rational Chow
class. This constructs a linear Chow-valued map on the existing marked
residual ideal. No cohomology class or inverse realization defines it.

The marked element `q - 1` gives `[C(base)] - ∑ s, [C s]`. The map's image
is exactly the span of the nonmarked cycle classes. Thus the map constructs
cycles from supplied geometric cycles; it does not choose that family from
an arbitrary prescribed Hodge class. Sheet labels do not themselves assert
that these cycles arise from a cover or incidence family.

Open restriction and finite pushforward commute with this construction
through the already proved maps on the same Chow quotients. Finite
pushforward retains the degree weights of Stacks 42.12.1 (02R4) and the
norm-based relation preservation of 42.18.1 (02RT):
https://stacks.math.columbia.edu/tag/02R4
https://stacks.math.columbia.edu/tag/02RT

The degree is the existing dimension grading. On an equidimensional target
of dimension `d`, codimension `p` uses degree `d - p`; no dimension is fixed
here. No intersection product or multiplicativity of the residual map is
assumed. A general geometric Betti realization and prescribed-class
generation remain separate obligations.
-/

set_option autoImplicit false

namespace HodgeConjecture.MarkedSheetChow

open AlgebraicGeometry CategoryTheory SchemeCycles
open scoped BigOperators

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Finite G] (H : Subgroup G)
variable {X : Scheme.{v}} (δ : DimensionFunction X) (n : ℤ)

local instance : Fintype (CollisionFoundations.GaloisSheets H) := Fintype.ofFinite _
local instance : DecidableEq (CollisionFoundations.GaloisSheets H) := Classical.decEq _

/-- Assemble existing homogeneous cycles with the actual residual sheet coefficients. -/
def cycleMap (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    MarkedSheetProjector.Residual H →ₗ[ℚ] cyclesOfDegree ℚ δ n where
  toFun x := ∑ s, x.val s • C s
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, smul_smul]

variable [IsNoetherian X]

/-- The Chow-valued map is the class of the constructed geometric cycle. -/
def chowMap (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    MarkedSheetProjector.Residual H →ₗ[ℚ] RationalChowGroup δ n :=
  (rationalClassMap δ n).comp (cycleMap H δ n C)

theorem chowMap_apply (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n)
    (x : MarkedSheetProjector.Residual H) :
    chowMap H δ n C x = ∑ s, x.val s • rationalClassMap δ n (C s) := by
  simp [chowMap, cycleMap]

/-- A single geometric cycle uses the corresponding residual coefficient. -/
theorem chowMap_single (s : CollisionFoundations.GaloisSheets H)
    (c : cyclesOfDegree ℚ δ n) (x : MarkedSheetProjector.Residual H) :
    chowMap H δ n (Pi.single s c) x = x.val s • rationalClassMap δ n c := by
  classical
  simp [chowMap_apply, Pi.single_apply, apply_ite]

/-- Compute the cycle produced by the marked selector; its class is an output. -/
theorem chowMap_residualClass
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    chowMap H δ n C (MarkedSheetProjector.residualClass H) =
      rationalClassMap δ n (C (baseSheet H)) - ∑ s, rationalClassMap δ n (C s) := by
  classical
  rw [chowMap_apply]
  simp only [MarkedSheetProjector.residualClass, Pi.sub_apply, Pi.one_apply,
    sub_smul, one_smul, Finset.sum_sub_distrib]
  congr 1
  simp [MarkedSheetProjector.selector, genericSheetSelector]

/-- Componentwise rational equivalence preserves the whole residual Chow map. -/
theorem chowMap_congr
    (C C' : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n)
    (h : ∀ s, C s - C' s ∈ rationalPrincipalRelations δ n) :
    chowMap H δ n C = chowMap H δ n C' := by
  apply LinearMap.ext
  intro x
  simp only [chowMap_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact sub_eq_zero.mp (by
    rw [← map_sub, rationalClassMap_eq_zero_iff]
    exact h s)

/-- Exactly the nonmarked supplied cycle classes are available to the linear recipe. -/
theorem range_chowMap
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    LinearMap.range (chowMap H δ n C) =
      Submodule.span ℚ (Set.range (fun s : {s : CollisionFoundations.GaloisSheets H //
        s ≠ baseSheet H} ↦ rationalClassMap δ n (C s.val))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [chowMap_apply]
    apply Submodule.sum_mem
    intro s _
    by_cases hs : s = baseSheet H
    · subst s
      have hx : x.val (baseSheet H) = 0 := x.property
      simp [hx]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    let x : MarkedSheetProjector.Residual H := ⟨Pi.single s.val 1, by
      change (Pi.single s.val (1 : ℚ) : CollisionFoundations.GaloisSheets H → ℚ)
        (baseSheet H) = 0
      simp [s.property.symm]⟩
    refine ⟨x, ?_⟩
    simp [chowMap_apply, x, Pi.single_apply]

/-- The image under a supplied realization is precisely the span of the
realized nonmarked cycles. It need not contain every Hodge class. -/
theorem range_cycleClass_chowMap
    {V : Type w} [AddCommGroup V] [Module ℚ V]
    (cl : RationalChowGroup δ n →ₗ[ℚ] V)
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    LinearMap.range (cl.comp (chowMap H δ n C)) =
      Submodule.span ℚ (Set.range (fun s : {s : CollisionFoundations.GaloisSheets H //
        s ≠ baseSheet H} ↦ cl (rationalClassMap δ n (C s.val)))) := by
  rw [LinearMap.range_comp, range_chowMap, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Any supplied cycle-class map computes the realization of this actual Chow cycle. -/
theorem cycleClass_chowMap_residualClass
    {V : Type w} [AddCommGroup V] [Module ℚ V]
    (cl : RationalChowGroup δ n →ₗ[ℚ] V)
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    cl (chowMap H δ n C (MarkedSheetProjector.residualClass H)) =
      cl (rationalClassMap δ n (C (baseSheet H))) -
        ∑ s, cl (rationalClassMap δ n (C s)) := by
  rw [chowMap_residualClass, map_sub, map_sum]

/-- Reweighting actual cycles realizes any residual input at the canonical
marked vector. This changes only rational coefficients of the supplied
cycles; it does not obtain them from a Hodge class. -/
theorem chowMap_residualClass_reweight
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n)
    (x : MarkedSheetProjector.Residual H) :
    chowMap H δ n (fun s ↦ -(x.val s) • C s)
        (MarkedSheetProjector.residualClass H) = chowMap H δ n C x := by
  rw [chowMap_residualClass, chowMap_apply]
  have hx : x.val (baseSheet H) = 0 := x.property
  simp [hx, Finset.sum_neg_distrib]

/-- Restrict the original cycles on an actual open; the Chow recipe commutes. -/
theorem openRestriction_chowMap
    {U : Scheme.{v}} (j : U ⟶ X) [IsOpenImmersion j]
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    letI := openImmersion_isNoetherian j
    (rationalChowOpenRestriction δ j n).comp (chowMap H δ n C) =
      chowMap H (δ.comapOpenImmersion j) n (fun s ↦ gradedOpenRestriction ℚ δ j n (C s)) := by
  letI := openImmersion_isNoetherian j
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, chowMap_apply, map_sum, map_smul,
    rationalChowOpenRestriction_classMap]

/-- The finite pushforward of the constructed cycle gives the same recipe
on the actual pushed cycles, with canonical field gradings on both schemes. -/
theorem finitePushforward_chowMap
    (k : Type v) [Field k] {Y : Scheme.{v}} [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f]
    (C : CollisionFoundations.GaloisSheets H →
      cyclesOfDegree ℚ (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n) :
    (rationalChowFinitePushforward k pY f n).comp
        (chowMap H (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n C) =
      chowMap H (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
        (fun s ↦ gradedFinitePushforward ℚ
          (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY))
          (DimensionFunction.ofLocallyOfFiniteType k Y pY) f
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n (C s)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, chowMap_apply, map_sum, map_smul,
    rationalChowFinitePushforward_classMap]

end

end HodgeConjecture.MarkedSheetChow
