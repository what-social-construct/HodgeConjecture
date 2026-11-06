module

public import HodgeConjecture.Realization.HodgeClasses
public import HodgeConjecture.Cycles.RationalChowOpenRestriction
public import HodgeConjecture.Cycles.RationalChowPushforward

@[expose] public section

/-!
# Boundary correction on the existing Chow groups

An open-locus representative lifts by the already proved surjectivity of
Chow restriction. Its cohomological discrepancy is a Hodge class. If that
class lifts to a Hodge class on the boundary, algebraicity on the boundary
supplies a correction through the existing closed Chow pushforward.

For a smooth divisor `D` in a smooth projective `X`, the intended boundary
model is codimension `p - 1` on `D`, while the ambient model is codimension
`p` on `X`. Both use the same dimension grading `dim X - p`. Thus the
boundary Hodge conjecture can be an induction hypothesis uniform in dimension.

The supported Hodge lift and the two cycle-class comparison squares are
explicit hypotheses. No general Betti/Gysin construction is asserted here.
The scheme specialization uses actual rational Chow groups and their maps;
it does not assume abstract Chow localization exactness or introduce a new
cycle quotient, projector, realization record, or global source instance.

Sources: Stacks Project, Lemma 42.19.3 (the open-surjectivity consequence),
https://stacks.math.columbia.edu/tag/02RX. The geometric motivation for the
separate supported-Hodge-lift hypothesis is cohomological localization and
Gysin compatibility; see de Cataldo--Migliorini, §2 and Theorem 4.1,
https://arxiv.org/pdf/math/0504560. For a smooth projective boundary, a
polarization-orthogonal complement of the Gysin kernel supplies a Hodge lift.
That argument and the geometric comparison maps remain to be instantiated.
-/

set_option autoImplicit false

namespace HodgeConjecture.BoundaryCorrection

noncomputable section

universe c d h k u v s

variable {ChowX : Type c} {ChowD : Type d} {HX : Type h} {HD : Type k}
  {HU : Type u}
variable [AddCommGroup ChowX] [Module ℚ ChowX]
  [AddCommGroup ChowD] [Module ℚ ChowD]
  [AddCommGroup HX] [Module ℚ HX] [AddCommGroup HD] [Module ℚ HD]
  [AddCommGroup HU] [Module ℚ HU]

/-- Correct any existing ambient cycle whose class agrees with the target
on the open. Algebraicity on the boundary is an explicit input, distinct
from lifting the discrepancy merely as a Hodge class. -/
theorem exists_boundary_correction
    (M : RationalHodgeCycleClassModel ChowX HX)
    (MD : RationalHodgeCycleClassModel ChowD HD)
    (pushCH : ChowD →ₗ[ℚ] ChowX) (pushH : HD →ₗ[ℚ] HX)
    (restrictH : HX →ₗ[ℚ] HU)
    (hPush : M.cycleClass.comp pushCH = pushH.comp MD.cycleClass)
    (hBoundaryLift : ∀ δ : HX, IsRationalHodgeClass M δ → restrictH δ = 0 →
      ∃ γ : HD, IsRationalHodgeClass MD γ ∧ pushH γ = δ)
    (hBoundary : RationalHodgeConjectureAt MD)
    (α : HX) (hα : IsRationalHodgeClass M α) (z : ChowX)
    (hOpen : restrictH (M.cycleClass z) = restrictH α) :
    ∃ b : ChowD, M.cycleClass (z + pushCH b) = α := by
  have hδ : IsRationalHodgeClass M (α - M.cycleClass z) :=
    M.hodgeClasses.sub_mem hα (M.cycleClass_lands ⟨z, rfl⟩)
  have hδOpen : restrictH (α - M.cycleClass z) = 0 := by
    rw [map_sub, hOpen, sub_self]
  obtain ⟨γ, hγ, hγδ⟩ := hBoundaryLift _ hδ hδOpen
  obtain ⟨b, hb⟩ := hBoundary hγ
  refine ⟨b, ?_⟩
  have hPushb := LinearMap.congr_fun hPush b
  simp only [LinearMap.comp_apply] at hPushb
  rw [map_add, hPushb, hb, hγδ, add_sub_cancel]

/-- An open-locus cycle representing the restricted Hodge class suffices
when Chow restriction is surjective and the boundary correction inputs hold.
The open cohomology is just a module here; no pure Hodge structure on a
nonproper open is assumed. -/
theorem isAlgebraicHodgeClass_of_openRestriction
    {ChowU : Type v} [AddCommGroup ChowU] [Module ℚ ChowU]
    (M : RationalHodgeCycleClassModel ChowX HX)
    (MD : RationalHodgeCycleClassModel ChowD HD)
    (clU : ChowU →ₗ[ℚ] HU)
    (restrictCH : ChowX →ₗ[ℚ] ChowU) (restrictH : HX →ₗ[ℚ] HU)
    (pushCH : ChowD →ₗ[ℚ] ChowX) (pushH : HD →ₗ[ℚ] HX)
    (hRestrict : clU.comp restrictCH = restrictH.comp M.cycleClass)
    (hSurj : Function.Surjective restrictCH)
    (hPush : M.cycleClass.comp pushCH = pushH.comp MD.cycleClass)
    (hBoundaryLift : ∀ δ : HX, IsRationalHodgeClass M δ → restrictH δ = 0 →
      ∃ γ : HD, IsRationalHodgeClass MD γ ∧ pushH γ = δ)
    (hBoundary : RationalHodgeConjectureAt MD)
    (α : HX) (hα : IsRationalHodgeClass M α)
    (zU : ChowU) (hzU : clU zU = restrictH α) :
    IsAlgebraicHodgeClass M α := by
  obtain ⟨z, hz⟩ := hSurj zU
  have hOpen : restrictH (M.cycleClass z) = restrictH α := by
    have h := LinearMap.congr_fun hRestrict z
    simp only [LinearMap.comp_apply] at h
    rw [← h, hz, hzU]
  obtain ⟨b, hb⟩ := exists_boundary_correction M MD pushCH pushH restrictH
    hPush hBoundaryLift hBoundary α hα z hOpen
  exact ⟨z + pushCH b, hb⟩

open AlgebraicGeometry CategoryTheory SchemeCycles

/-- The correction criterion on actual rational Chow groups. The source
grading of the closed map is the restriction of the ambient dimension
function; its preservation and open Chow surjectivity are proved inputs
from the existing scheme-cycle construction, not supplied premises.

Only the cohomological maps, their two cycle-class comparisons, the Hodge
lift, and the boundary induction hypothesis remain to be supplied. The closed
map need not be asserted complementary to the open map in this algebraic
consumer: the supported-Hodge-lift hypothesis records the needed coverage. -/
theorem isAlgebraicHodgeClass_of_schemeOpenRestriction
    {X D U : Scheme.{s}} [IsNoetherian X] [IsNoetherian D]
    (δX : DimensionFunction X) (i : D ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ)
    (M : RationalHodgeCycleClassModel (RationalChowGroup δX n) HX)
    (MD : RationalHodgeCycleClassModel
      (RationalChowGroup (δX.comapClosedImmersion i) n) HD) :
    letI := openImmersion_isNoetherian j
    ∀ (clU : RationalChowGroup (δX.comapOpenImmersion j) n →ₗ[ℚ] HU)
      (restrictH : HX →ₗ[ℚ] HU) (pushH : HD →ₗ[ℚ] HX),
      clU.comp (rationalChowOpenRestriction δX j n) =
          restrictH.comp M.cycleClass →
      M.cycleClass.comp (rationalChowClosedImmersionPushforward
          (δX.comapClosedImmersion i) δX i
          (fun W ↦ (supportDegree_comapClosedImmersion δX i W).symm) n) =
          pushH.comp MD.cycleClass →
      (∀ δ : HX, IsRationalHodgeClass M δ → restrictH δ = 0 →
        ∃ γ : HD, IsRationalHodgeClass MD γ ∧ pushH γ = δ) →
      RationalHodgeConjectureAt MD →
      ∀ α : HX, IsRationalHodgeClass M α →
        ∀ zU : RationalChowGroup (δX.comapOpenImmersion j) n,
          clU zU = restrictH α → IsAlgebraicHodgeClass M α := by
  letI := openImmersion_isNoetherian j
  intro clU restrictH pushH hRestrict hPush hBoundaryLift hBoundary α hα zU hzU
  exact isAlgebraicHodgeClass_of_openRestriction M MD clU
    (rationalChowOpenRestriction δX j n) restrictH
    (rationalChowClosedImmersionPushforward (δX.comapClosedImmersion i) δX i
      (fun W ↦ (supportDegree_comapClosedImmersion δX i W).symm) n) pushH
    hRestrict (rationalChowOpenRestriction_surjective δX j n)
    hPush hBoundaryLift hBoundary α hα zU hzU

end

end HodgeConjecture.BoundaryCorrection
