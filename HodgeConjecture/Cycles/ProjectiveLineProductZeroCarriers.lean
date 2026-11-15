module

public import HodgeConjecture.Geometry.ProjectiveLineProductZeroFibers
public import HodgeConjecture.Geometry.ProjectiveLineProperties
public import HodgeConjecture.Cycles.ClosedImmersionPushforward
public import HodgeConjecture.Cycles.PointSupport
public import HodgeConjecture.Cycles.DivisorSupport
public import HodgeConjecture.Cycles.ProjectiveLineProductIntegralCandidates

/-!
# Integral zero-coordinate carriers in the projective-line product

The closed immersions of either projective line into the scheme product
carry its whole integral support to integral closed subschemes. Their ideal
sheaves equal the existing scheme-theoretic zero-fiber ideals, so both
fibers are integral and isomorphic to `P¹`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace HodgeConjecture.SchemeCycles
open HodgeConjecture.ProjectiveLineProductFibers
open HodgeConjecture.ProjectiveLineProductIntegralCandidates

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- Integral image support of the first zero-coordinate map. -/
def projectiveLineProductZeroFirstCarrier :
    IntegralClosedSubscheme (projectiveLineProduct k) :=
  closedImageSubscheme (projectiveLineProductZeroFirst k)
    (pointSupport (projectiveLine k) (genericPoint (projectiveLine k)))

/-- Integral image support of the second zero-coordinate map. -/
def projectiveLineProductZeroSecondCarrier :
    IntegralClosedSubscheme (projectiveLineProduct k) :=
  closedImageSubscheme (projectiveLineProductZeroSecond k)
    (pointSupport (projectiveLine k) (genericPoint (projectiveLine k)))

/-- The first closed image is exactly the previously constructed reduced
closure of the generic point of its coordinate fiber. -/
theorem projectiveLineProductZeroFirstCarrier_eq_candidate :
    projectiveLineProductZeroFirstCarrier k =
      HodgeConjecture.ProjectiveLineProductIntegralCandidates.firstZeroCarrier k := by
  simp only [projectiveLineProductZeroFirstCarrier,
    HodgeConjecture.ProjectiveLineProductIntegralCandidates.firstZeroCarrier]
  exact closedImage_pointSupport (projectiveLineProductZeroFirst k)
    (genericPoint (projectiveLine k))

/-- The second closed image is exactly the previously constructed reduced
closure of the generic point of its coordinate fiber. -/
theorem projectiveLineProductZeroSecondCarrier_eq_candidate :
    projectiveLineProductZeroSecondCarrier k =
      HodgeConjecture.ProjectiveLineProductIntegralCandidates.secondZeroCarrier k := by
  simp only [projectiveLineProductZeroSecondCarrier,
    HodgeConjecture.ProjectiveLineProductIntegralCandidates.secondZeroCarrier]
  exact closedImage_pointSupport (projectiveLineProductZeroSecond k)
    (genericPoint (projectiveLine k))

/-- The reduced closure of the generic point is the whole integral
projective line. -/
theorem projectiveLine_genericPointSupport_eq_bot :
    (pointSupport (projectiveLine k) (genericPoint (projectiveLine k))).val = ⊥ := by
  rw [pointSupport_val]
  have hclosure : Closeds.closure ({genericPoint (projectiveLine k)} :
      Set (projectiveLine k)) = ⊤ :=
    SetLike.coe_injective (genericPoint_spec (projectiveLine k)).def
  rw [hclosure, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot]

/-- The first zero-coordinate carrier is isomorphic to the actual
projective line. -/
def projectiveLineProductZeroFirstCarrierIso :
    projectiveLine k ≅ (projectiveLineProductZeroFirstCarrier k).val.subscheme := by
  let W := pointSupport (projectiveLine k) (genericPoint (projectiveLine k))
  haveI : IsIso W.val.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot W.val).mpr
      (projectiveLine_genericPointSupport_eq_bot k)
  exact (asIso W.val.subschemeι).symm ≪≫
    closedImageSubschemeIso (projectiveLineProductZeroFirst k) W

/-- The second zero-coordinate carrier is isomorphic to the actual
projective line. -/
def projectiveLineProductZeroSecondCarrierIso :
    projectiveLine k ≅ (projectiveLineProductZeroSecondCarrier k).val.subscheme := by
  let W := pointSupport (projectiveLine k) (genericPoint (projectiveLine k))
  haveI : IsIso W.val.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot W.val).mpr
      (projectiveLine_genericPointSupport_eq_bot k)
  exact (asIso W.val.subschemeι).symm ≪≫
    closedImageSubschemeIso (projectiveLineProductZeroSecond k) W

/-- Every point of the spectrum of a field has the whole spectrum as its
reduced closure. -/
theorem specField_pointSupport_eq_bot (x : Spec (.of k)) :
    (pointSupport (Spec (.of k)) x).val = ⊥ := by
  have hx : x = genericPoint (Spec (.of k)) := Subsingleton.elim _ _
  rw [hx, pointSupport_val]
  have hclosure : Closeds.closure ({genericPoint (Spec (.of k))} :
      Set (Spec (.of k))) = ⊤ :=
    SetLike.coe_injective (genericPoint_spec (Spec (.of k))).def
  rw [hclosure, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot]

/-- The reduced closure of the rational zero point is the scheme-theoretic
image of its closed section. -/
theorem projectiveLine_zeroSectionPointSupport_eq_ker :
    (pointSupport (projectiveLine k) (zeroSectionPoint k)).val =
      (projectiveLineZeroSection k).ker := by
  let x : Spec (.of k) :=
    (projectiveLine k ↘ Spec (.of k)).base (genericPoint (projectiveLine k))
  have h := closedImage_pointSupport (projectiveLineZeroSection k) x
  have hval := congrArg Subtype.val h
  change (pointSupport (Spec (.of k)) x).val.map (projectiveLineZeroSection k) =
    (pointSupport (projectiveLine k) ((projectiveLineZeroSection k).base x)).val at hval
  rw [specField_pointSupport_eq_bot k x, Scheme.IdealSheafData.map_bot] at hval
  exact hval.symm

/-- The point used by the integral candidate construction is the existing
origin of the glued projective line. -/
@[simp] theorem zeroSectionPoint_eq_projectiveLineZero :
    zeroSectionPoint k = projectiveLineZero k := by
  change (projectiveLineZeroSection k)
    ((projectiveLine k ↘ Spec (.of k)).base
      (genericPoint (projectiveLine k))) = projectiveLineZero k
  have h : (projectiveLine k ↘ Spec (.of k)).base
      (genericPoint (projectiveLine k)) = (default : Spec (.of k)) :=
    Subsingleton.elim _ _
  rw [h]
  exact projectiveLineZeroSection_apply_unique k

theorem projectiveLineProductZeroFirstCarrier_val_eq_ker :
    (projectiveLineProductZeroFirstCarrier k).val =
      (projectiveLineProductZeroFirst k).ker := by
  change (pointSupport (projectiveLine k) (genericPoint (projectiveLine k))).val.map
    (projectiveLineProductZeroFirst k) = _
  rw [projectiveLine_genericPointSupport_eq_bot, Scheme.IdealSheafData.map_bot]

theorem projectiveLineProductZeroSecondCarrier_val_eq_ker :
    (projectiveLineProductZeroSecondCarrier k).val =
      (projectiveLineProductZeroSecond k).ker := by
  change (pointSupport (projectiveLine k) (genericPoint (projectiveLine k))).val.map
    (projectiveLineProductZeroSecond k) = _
  rw [projectiveLine_genericPointSupport_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The first integral image is exactly the scheme-theoretic zero fiber,
including its ideal sheaf rather than only its underlying support. -/
theorem projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal :
    (projectiveLineProductZeroFirstCarrier k).val =
      firstFiberIdeal k (zeroSectionPoint k) := by
  let π₁ := projectiveLineProductFst k
  let s := projectiveLineZeroSection k
  let j := projectiveLineProductZeroFirst k
  calc
    (projectiveLineProductZeroFirstCarrier k).val = j.ker :=
      projectiveLineProductZeroFirstCarrier_val_eq_ker k
    _ = (pullback.fst π₁ s).ker := by
      have h : (projectiveLineProductZeroFirstPullbackIso k).hom ≫
          pullback.fst π₁ s = j := by
        simp [π₁, s, j, projectiveLineProductZeroFirstPullbackIso]
      rw [← h, Scheme.Hom.ker_comp_of_isIso]
    _ = s.ker.comap π₁ := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion s π₁
    _ = firstFiberIdeal k (zeroSectionPoint k) := by
      rw [← projectiveLine_zeroSectionPointSupport_eq_ker k]
      rfl

/-- The second integral image is exactly the scheme-theoretic zero fiber. -/
theorem projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal :
    (projectiveLineProductZeroSecondCarrier k).val =
      secondFiberIdeal k (zeroSectionPoint k) := by
  let π₂ := projectiveLineProductSnd k
  let s := projectiveLineZeroSection k
  let j := projectiveLineProductZeroSecond k
  calc
    (projectiveLineProductZeroSecondCarrier k).val = j.ker :=
      projectiveLineProductZeroSecondCarrier_val_eq_ker k
    _ = (pullback.fst π₂ s).ker := by
      have h : (projectiveLineProductZeroSecondPullbackIso k).hom ≫
          pullback.fst π₂ s = j := by
        simp [π₂, s, j, projectiveLineProductZeroSecondPullbackIso]
      rw [← h, Scheme.Hom.ker_comp_of_isIso]
    _ = s.ker.comap π₂ := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion s π₂
    _ = secondFiberIdeal k (zeroSectionPoint k) := by
      rw [← projectiveLine_zeroSectionPointSupport_eq_ker k]
      rfl

/-- The first actual scheme-theoretic zero fiber is integral. -/
theorem projectiveLineProduct_firstZeroFiber_isIntegral :
    IsIntegral (firstFiberIdeal k (zeroSectionPoint k)).subscheme := by
  rw [← projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal k]
  exact (projectiveLineProductZeroFirstCarrier k).property

/-- The second actual scheme-theoretic zero fiber is integral. -/
theorem projectiveLineProduct_secondZeroFiber_isIntegral :
    IsIntegral (secondFiberIdeal k (zeroSectionPoint k)).subscheme := by
  rw [← projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal k]
  exact (projectiveLineProductZeroSecondCarrier k).property

/-- The first zero fiber is integral at the project's original point `0`. -/
theorem projectiveLineProduct_firstOriginFiber_isIntegral :
    IsIntegral (firstFiberIdeal k (projectiveLineZero k)).subscheme := by
  simpa only [zeroSectionPoint_eq_projectiveLineZero] using
    projectiveLineProduct_firstZeroFiber_isIntegral k

/-- The second zero fiber is integral at the project's original point `0`. -/
theorem projectiveLineProduct_secondOriginFiber_isIntegral :
    IsIntegral (secondFiberIdeal k (projectiveLineZero k)).subscheme := by
  simpa only [zeroSectionPoint_eq_projectiveLineZero] using
    projectiveLineProduct_secondZeroFiber_isIntegral k

end AlgebraicGeometry

end
