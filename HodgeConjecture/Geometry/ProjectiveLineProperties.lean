module

public import HodgeConjecture.Geometry.ProjectiveLine
public import HodgeConjecture.Cycles.FiniteTypeSchemeDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.IsIntegral

@[expose] public section

/-!
# Integral, finite-type and dimension properties of the actual projective line

Selected proof adaptations from AxiomMath/Stacks, revision
f8e70c5dd04bfabcb423d5e325461f527c85a5d6,
StacksFrontier/AlgebraicGeometry/Scheme/Glueing/
ProjectiveLineIntegral.lean and ProjectiveLineFiniteType.lean, Apache-2.0;
see third_party/axiom-stacks/LICENSE. Dimension is derived using the existing
open-immersion coheight comparison and Mathlib's polynomial dimension theorem.
Normal stalks are actual localizations of the normal polynomial charts.

The scheme throughout is the existing two-chart gluing. No properness,
projective-spectrum identification or Chow comparison is supplied as input.
-/

set_option autoImplicit false

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace
open HodgeConjecture.SchemeCycles

noncomputable section

universe u

section Ring

variable (k : Type u) [CommRing k]

/-- The actual overlap inclusion into the second affine chart. -/
abbrev projectiveLineOverlapYInclusion :
    Spec (.of (LaurentPolynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k

instance : IsOpenImmersion (projectiveLineOverlapYInclusion k) := by
  unfold projectiveLineOverlapYInclusion
  infer_instance

/-- The first actual affine chart is dense when the base is a domain. -/
theorem denseRange_projectiveLineXChart [IsDomain k] :
    Dense (Set.range (projectiveLineXChart k).base) := by
  have hdense : Dense (Set.range (projectiveLineOverlapYInclusion k).base) :=
    ((projectiveLineOverlapYInclusion k).isOpenEmbedding.isOpen_range).dense
      (Set.range_nonempty _)
  have hcomm : projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k := by
    simpa only [projectiveLineOverlapYInclusion, Category.assoc] using
      projectiveLineOverlap_compat k
  have hsub : (projectiveLineYChart k).base ''
      Set.range (projectiveLineOverlapYInclusion k).base ⊆
        Set.range (projectiveLineXChart k).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(projectiveLinePuncturedChart k).base z, ?_⟩
    exact congrArg (fun f ↦ f.base z) hcomm
  have hY : Set.range (projectiveLineYChart k).base ⊆
      closure ((projectiveLineYChart k).base ''
        Set.range (projectiveLineOverlapYInclusion k).base) := by
    rintro _ ⟨y, rfl⟩
    have h := (projectiveLineYChart k).isOpenEmbedding.isEmbedding
      |>.closure_eq_preimage_closure_image (Set.range (projectiveLineOverlapYInclusion k).base)
    rw [hdense.closure_eq] at h
    exact h.subset (Set.mem_univ y)
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun x ↦ ?_)
  rcases projectiveLine_charts_cover k x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨y, rfl⟩
  · exact closure_mono hsub (hY ⟨y, rfl⟩)

/-- Density transfers irreducibility from the actual polynomial chart. -/
instance projectiveLine_irreducibleSpace_inst [IsDomain k] :
    IrreducibleSpace (projectiveLine k) := by
  have hpre : IsPreirreducible (Set.range (projectiveLineXChart k).base) := by
    rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ
      (X := Spec (.of (Polynomial k)))).image _ (by fun_prop)
  have : PreirreducibleSpace (projectiveLine k) := by
    refine ⟨?_⟩
    rw [← (denseRange_projectiveLineXChart k).closure_eq]
    exact hpre.closure
  exact { toNonempty := ⟨projectiveLineZero k⟩ }

/-- Reducedness is proved on the actual affine cover. -/
theorem projectiveLine_isReduced [_root_.IsReduced (Polynomial k)] :
    AlgebraicGeometry.IsReduced (projectiveLine k) := by
  have hred : ∀ i, AlgebraicGeometry.IsReduced ((projectiveLineOpenCover k).X i) :=
    fun _ ↦ inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (Polynomial k))))
  exact IsReduced.of_openCover (projectiveLine k) (projectiveLineOpenCover k)

/-- The existing glued projective line over a domain is integral. -/
instance projectiveLine_isIntegral_inst [IsDomain k] : IsIntegral (projectiveLine k) := by
  have : AlgebraicGeometry.IsReduced (projectiveLine k) := projectiveLine_isReduced k
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Either actual chart's structure map is the finite-type polynomial-algebra map. -/
theorem projectiveLineAffineStructureMorphism_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveLineAffineStructureMorphism k) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- Finite type is local on the source, so the actual glued structure map has it locally. -/
instance projectiveLine_locallyOfFiniteType_inst :
    LocallyOfFiniteType (projectiveLine k ↘ Spec (.of k)) := by
  have hloc : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  refine IsZariskiLocalAtSource.of_openCover (projectiveLineOpenCover k) fun i ↦ ?_
  have h : (projectiveLineOpenCover k).f i ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k := (projectiveLineStructureMorphism k).2 i
  rw [h]
  exact projectiveLineAffineStructureMorphism_locallyOfFiniteType k

/-- The finite actual affine cover gives a Noetherian scheme over a Noetherian base. -/
instance projectiveLine_isNoetherian [IsNoetherianRing k] :
    IsNoetherian (projectiveLine k) := by
  let : Finite (projectiveLineOpenCover k).I₀ :=
    inferInstanceAs (Finite (ULift.{u} Bool))
  have : ∀ i, IsAffine ((projectiveLineOpenCover k).X i) :=
    fun _ ↦ inferInstanceAs (IsAffine (Spec (.of (Polynomial k))))
  apply (isNoetherian_iff_of_finite_affine_openCover (𝒰 := projectiveLineOpenCover k)).mpr
  intro i
  change IsNoetherianRing Γ(Spec (.of (Polynomial k)), ⊤)
  exact isNoetherianRing_of_ringEquiv (Polynomial k)
    (Scheme.ΓSpecIso (.of (Polynomial k))).symm.commRingCatIsoToRingEquiv

/-- The first actual chart is dominant. -/
instance projectiveLineXChart_isDominant [IsDomain k] : IsDominant (projectiveLineXChart k) :=
  ⟨denseRange_projectiveLineXChart k⟩

end Ring

section Field

variable (k : Type u) [Field k]

/-- The actual affine-line chart has dimension one over a field. -/
theorem topologicalKrullDim_projectiveLineChart :
    topologicalKrullDim (Spec (.of (Polynomial k))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- The glued projective line has dimension one, checked through the actual open chart stalks. -/
theorem topologicalKrullDim_projectiveLine : topologicalKrullDim (projectiveLine k) = 1 := by
  have hchart := topologicalKrullDim_projectiveLineChart k
  rw [topologicalKrullDim_eq_pointKrullDim, Order.krullDim_eq_iSup_coheight] at hchart ⊢
  apply le_antisymm
  · apply iSup_le
    intro x
    rcases projectiveLine_charts_cover k x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [← point_coheight_eq_of_isOpenImmersion (projectiveLineXChart k) y]
      exact (le_iSup _ y).trans hchart.le
    · rw [← point_coheight_eq_of_isOpenImmersion (projectiveLineYChart k) y]
      exact (le_iSup _ y).trans hchart.le
  · rw [← hchart]
    apply iSup_le
    intro y
    rw [point_coheight_eq_of_isOpenImmersion (projectiveLineXChart k) y]
    exact le_iSup (fun x : projectiveLine k ↦ (Order.coheight x : WithBot ℕ∞))
      ((projectiveLineXChart k).base y)

/-- Polynomial-chart stalks are actual localizations of the integrally closed polynomial ring. -/
theorem projectiveLineChart_stalk_isIntegrallyClosed
    (y : Spec (.of (Polynomial k))) :
    IsIntegrallyClosed ((Spec (.of (Polynomial k))).presheaf.stalk y) := by
  have : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime y.asIdeal)
      y.asIdeal.primeCompl y.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (StructureSheaf.stalkIso (Polynomial k) y).toRingEquiv

/-- Every actual stalk of the glued projective line is integrally closed. -/
theorem projectiveLine_stalk_isIntegrallyClosed (x : projectiveLine k) :
    IsIntegrallyClosed ((projectiveLine k).presheaf.stalk x) := by
  rcases projectiveLine_charts_cover k x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have := projectiveLineChart_stalk_isIntegrallyClosed k y
    exact IsIntegrallyClosed.of_equiv
      (asIso ((projectiveLineXChart k).stalkMap y)).symm.commRingCatIsoToRingEquiv
  · have := projectiveLineChart_stalk_isIntegrallyClosed k y
    exact IsIntegrallyClosed.of_equiv
      (asIso ((projectiveLineYChart k).stalkMap y)).symm.commRingCatIsoToRingEquiv

end Field

end

end AlgebraicGeometry
