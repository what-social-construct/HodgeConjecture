module

public import HodgeConjecture.Cycles.ProjectiveLineProductChowClasses
public import HodgeConjecture.Cycles.ProjectiveLineProductFibers
public import HodgeConjecture.Cycles.ChowLocalization
public import HodgeConjecture.Geometry.ProjectiveLineProductAffineChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Ordinary Chow localization for the actual affine chart of P¹ × P¹

The open is the genuine tensor-product affine chart in the product scheme.
Its reduced closed complement is the geometric boundary built from that
open immersion. The existing rational Chow localization theorem applies
to these original objects. Computing the Chow group of the affine plane
and the boundary components is a separate geometric step.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductAffineChowLocalization

open AlgebraicGeometry CategoryTheory SchemeCycles TensorProduct
open HodgeConjecture.ProjectiveLineProductChow

universe u

variable (k : Type u) [Field k]

/-- The actual two-coordinate affine chart inside the product scheme. -/
abbrev chart :
    Spec (.of (Polynomial k ⊗[k] Polynomial k)) ⟶ projectiveLineProduct k :=
  projectiveLineProductAffineChart k

/-- Its actual reduced closed complement. -/
abbrev boundary : Scheme.{u} :=
  (openComplementIdeal (chart k)).subscheme

instance chart_isNoetherian : IsNoetherian (Spec (.of (Polynomial k ⊗[k] Polynomial k))) :=
  openImmersion_isNoetherian (chart k)

/-- The actual product affine chart consists exactly of points where
neither projective-line coordinate is infinity. -/
theorem range_chart :
    Set.range (chart k).base =
      (projectiveLineProductFst k).base ⁻¹'
          Set.range (projectiveLineXChart k).base ∩
        (projectiveLineProductSnd k).base ⁻¹'
          Set.range (projectiveLineXChart k).base := by
  change Set.range ((projectiveLineAffineProductIso k).inv ≫
    projectiveLineAffineProductMap k).base = _
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hs : Set.range (projectiveLineAffineProductIso k).inv.base = Set.univ :=
    Set.range_eq_univ.mpr (projectiveLineAffineProductIso k).inv.homeomorph.surjective
  rw [hs, Set.image_univ]
  exact Scheme.Pullback.range_map
    (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLineXChart k) (projectiveLineXChart k)
    (𝟙 (Spec (.of k))) (by simp) (by simp)

/-- The reduced closed boundary of the actual affine chart has precisely
the union of the two scheme-theoretic infinity-fiber supports. -/
theorem boundary_support_eq_infinity_fibers :
    ((openComplementIdeal (chart k)).support : Set (projectiveLineProduct k)) =
      ((ProjectiveLineProductFibers.firstFiberIdeal k
        (projectiveLineInfinity k)).support : Set (projectiveLineProduct k)) ∪
        ((ProjectiveLineProductFibers.secondFiberIdeal k
          (projectiveLineInfinity k)).support : Set (projectiveLineProduct k)) := by
  ext y
  rw [← Scheme.IdealSheafData.range_subschemeι, range_openComplement, range_chart]
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, not_and_or]
  rw [mem_range_projectiveLineXChart_iff_ne_infinity,
    mem_range_projectiveLineXChart_iff_ne_infinity]
  simp only [not_not, Set.mem_union]
  rw [← ProjectiveLineProductFibers.mem_firstInfinityFiber_support,
    ← ProjectiveLineProductFibers.mem_secondInfinityFiber_support]
  rfl

/-- Restriction from the product's ordinary rational Chow quotient to the
ordinary rational Chow quotient of its actual affine product chart. -/
def restrict :
    RationalChowGroup (dimensionFunction k) 1 →ₗ[ℚ]
      RationalChowGroup ((dimensionFunction k).comapOpenImmersion (chart k)) 1 := by
  letI := openImmersion_isNoetherian (chart k)
  exact rationalChowOpenRestriction (dimensionFunction k) (chart k) 1

/-- Every affine-chart rational Chow class lifts to the product. -/
theorem restrict_surjective : Function.Surjective (restrict k) := by
  exact rationalChowOpenRestriction_surjective (dimensionFunction k) (chart k) 1

/-- Chow localization for the actual affine chart and its actual reduced
closed complement. This is a statement on the existing rational-equivalence
quotients, not an auxiliary cycle quotient. -/
theorem range_boundaryPushforward_eq_ker_restrict :
    letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
    LinearMap.range (rationalChowClosedImmersionPushforward
      ((dimensionFunction k).comapClosedImmersion
        (openComplementIdeal (chart k)).subschemeι)
      (dimensionFunction k) (openComplementIdeal (chart k)).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion (dimensionFunction k)
        (openComplementIdeal (chart k)).subschemeι W).symm) 1) =
      LinearMap.ker (restrict k) := by
  letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
  simpa only [restrict] using
    (range_rationalChowOpenComplementPushforward_eq_ker
      (dimensionFunction k) (chart k) 1)

end HodgeConjecture.ProjectiveLineProductAffineChowLocalization

end
