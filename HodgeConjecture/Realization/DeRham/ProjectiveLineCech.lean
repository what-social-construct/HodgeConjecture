module

public import HodgeConjecture.Geometry.ProjectiveLine
public import HodgeConjecture.Realization.DeRham.LaurentProjectiveCharts
public import HodgeConjecture.Realization.DeRham.LaurentDifferentials
public import HodgeConjecture.Realization.DeRham.Logarithmic
public import HodgeConjecture.Realization.DeRham.LaurentLogarithmicRegulator

@[expose] public section

/-!
# The projective-line two-chart Čech–de Rham complex

The actual two affine charts restrict to the Laurent overlap by the
polynomial map and its inverse-coordinate map. Functions and Kähler
one-forms give the first terms of their Čech–de Rham total complex; all
later terms retain the original overlap exterior forms and differential.
The square-zero laws follow from the proved restriction identities and
closedness of the pulled-back polynomial one-forms.

Degree two is the actual closed/exact quotient of this cochain complex.
Laurent residue annihilates its entire incoming differential and detects
the class of d log T. This file does not identify this Čech realization
with scheme hypercohomology or singular cohomology.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineDeRham

open AlgebraicGeometry CategoryTheory KaehlerDifferential AffineDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- These exact coordinate restrictions give the actual intersection of the named scheme charts. -/
theorem cechChartRingMaps_isPullback :
    CategoryTheory.IsPullback
      (Spec.map (CommRingCat.ofHom (chartZeroRingMap k).toRingHom))
      (Spec.map (CommRingCat.ofHom (chartInfinityRingMap k).toRingHom))
      (projectiveLineXChart k) (projectiveLineYChart k) := by
  have hzero : CommRingCat.ofHom (chartZeroRingMap k).toRingHom =
      CommRingCat.ofHom (Polynomial.toLaurent (R := k)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    rfl
  have hinfinity : CommRingCat.ofHom (chartInfinityRingMap k).toRingHom =
      CommRingCat.ofHom (Polynomial.toLaurent (R := k)) ≫
        CommRingCat.ofHom (LaurentPolynomial.invert (R := k)).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    rfl
  rw [hzero, hinfinity, Spec.map_comp]
  exact projectiveLineOverlap_isPullback k

/-- The chart columns have no suppressed nonzero higher forms. -/
theorem cechHigherChartForms_subsingleton (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (⋀[Polynomial k]^n Ω[Polynomial k⁄k]) :=
  LaurentDeRham.polynomialForms_subsingleton k n hn

/-- Regular functions on the two actual affine-line charts. -/
abbrev CechZero := Polynomial k × Polynomial k

/-- Two chart one-forms and a regular function on their actual overlap. -/
abbrev CechOne := Ω[Polynomial k⁄k] × Ω[Polynomial k⁄k] × LaurentPolynomial k

/-- The degree-zero differential, retaining both Kähler differentials and the Čech difference. -/
def cechDifferentialZero : CechZero k →ₗ[k] CechOne k where
  toFun x := (D k (Polynomial k) x.1, D k (Polynomial k) x.2,
    chartInfinityRingMap k x.2 - chartZeroRingMap k x.1)
  map_add' x y := by ext <;> simp [map_add, sub_add_sub_comm]
  map_smul' a x := by ext <;> simp [map_smul, smul_sub]

/-- The genuine degree-one total differential before exterior-power coordinates. -/
def cechIncomingForm : CechOne k →ₗ[k] Ω[LaurentPolynomial k⁄k] where
  toFun x := chartInfinityFormsMap k x.2.1 - chartZeroFormsMap k x.1 -
    D k (LaurentPolynomial k) x.2.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' a x := by simp [smul_sub]

/-- The same total differential in the existing degree-one exterior power on the overlap. -/
def cechDifferentialOne : CechOne k →ₗ[k] ⋀[LaurentPolynomial k]^1 Ω[LaurentPolynomial k⁄k] :=
  (LinearMap.restrictScalars k
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm.toLinearMap).comp
      (cechIncomingForm k)

theorem cechDifferentialOne_zero (x : CechZero k) :
    cechDifferentialOne k (cechDifferentialZero k x) = 0 := by
  change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
    (chartInfinityFormsMap k (D k (Polynomial k) x.2) -
      chartZeroFormsMap k (D k (Polynomial k) x.1) -
        D k (LaurentPolynomial k)
          (chartInfinityRingMap k x.2 - chartZeroRingMap k x.1)) = 0
  simp only [chartInfinityFormsMap_D, chartZeroFormsMap_D, map_sub, sub_self, map_zero]

/-- Every actual incoming total boundary is closed, including the overlap-function term. -/
theorem cechDifferentialOne_closed (x : CechOne k) :
    deRhamDifferential (A := k) 1 (cechDifferentialOne k x) = 0 := by
  have hexact : deRhamDifferential (A := k) 1
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (D k (LaurentPolynomial k) x.2.2)) = 0 := by
    have h := congrArg
      (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
      (differential_zero k (LaurentPolynomial k) x.2.2)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h]
    exact deRhamDifferential_comp_self 0 _
  change deRhamDifferential (A := k) 1
    ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
      (chartInfinityFormsMap k x.2.1 - chartZeroFormsMap k x.1 -
        D k (LaurentPolynomial k) x.2.2)) = 0
  rw [map_sub, map_sub, map_sub, map_sub,
    chartInfinityForms_closed, chartZeroForms_closed, hexact, sub_self, sub_self]

/-- The actual modules of the two-chart total complex. -/
def cechTerm : ℕ → ModuleCat k
  | 0 => ModuleCat.of k (CechZero k)
  | 1 => ModuleCat.of k (CechOne k)
  | n + 2 => ModuleCat.of k (⋀[LaurentPolynomial k]^(n + 1) Ω[LaurentPolynomial k⁄k])

/-- The total differentials, with the Čech sign on the overlap column. -/
def cechDifferential : (n : ℕ) → cechTerm k n ⟶ cechTerm k (n + 1)
  | 0 => ModuleCat.ofHom (cechDifferentialZero k)
  | 1 => ModuleCat.ofHom (cechDifferentialOne k)
  | n + 2 => ModuleCat.ofHom (-deRhamDifferential (A := k) (B := LaurentPolynomial k) (n + 1))

theorem cechDifferential_comp : (n : ℕ) →
    cechDifferential k n ≫ cechDifferential k (n + 1) = 0
  | 0 => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact cechDifferentialOne_zero k
  | 1 => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact neg_eq_zero.mpr (cechDifferentialOne_closed k x)
  | n + 2 => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change -deRhamDifferential (A := k) (n + 2)
        (-deRhamDifferential (A := k) (n + 1) x) = 0
      rw [map_neg, neg_neg, deRhamDifferential_comp_self]

/-- The constructed total complex on the actual chart and overlap coordinate rings. -/
def cechComplex : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (cechTerm k) (cechDifferential k) (cechDifferential_comp k)

@[simp]
theorem cechComplex_d (n : ℕ) :
    (cechComplex k).d n (n + 1) = cechDifferential k n :=
  CochainComplex.of_d _ _ n

/-- Incoming total boundaries as actual closed overlap forms. -/
def cechToClosedForms : CechOne k →ₗ[k] closedForms k (LaurentPolynomial k) 1 :=
  (cechDifferentialOne k).codRestrict _ (cechDifferentialOne_closed k)

/-- The entire incoming image; no relation-preservation condition is supplied. -/
def cechBoundaries : Submodule k (closedForms k (LaurentPolynomial k) 1) :=
  LinearMap.range (cechToClosedForms k)

/-- Degree two of the two-chart total complex, as its actual closed/exact quotient. -/
abbrev CechH2 := closedForms k (LaurentPolynomial k) 1 ⧸ cechBoundaries k

/-- The class of an actual closed overlap one-form, in total degree two. -/
def cechClass : closedForms k (LaurentPolynomial k) 1 →ₗ[k] CechH2 k :=
  (cechBoundaries k).mkQ

@[simp]
theorem cechClass_boundary (x : CechOne k) :
    cechClass k (cechToClosedForms k x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

theorem cechClass_eq_zero_iff (ω : closedForms k (LaurentPolynomial k) 1) :
    cechClass k ω = 0 ↔ ∃ x : CechOne k, cechDifferentialOne k x = ω.val := by
  change ((cechBoundaries k).mkQ ω = 0) ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The same degree-two short complex, with the outgoing sign normalized. -/
def cechDegreeTwoShortComplex : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk (cechDifferentialOne k)
    (deRhamDifferential (A := k) (B := LaurentPolynomial k) 1)
    (LinearMap.ext (cechDifferentialOne_closed k))

/-- Sign normalization on the last term preserves the actual short complex. -/
def cechDegreeTwoShortComplexIso :
    (cechComplex k).sc' 1 2 3 ≅ cechDegreeTwoShortComplex k :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (LinearEquiv.neg k (M := ⋀[LaurentPolynomial k]^2 Ω[LaurentPolynomial k⁄k])).toModuleIso
    (by simp [cechDegreeTwoShortComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', cechDifferential, Category.id_comp,
      Category.comp_id])
    (by
      apply ModuleCat.hom_ext
      ext x
      change deRhamDifferential (A := k) 1 x = -(-deRhamDifferential (A := k) 1 x)
      exact (neg_neg _).symm)

/-- The closed/exact model is categorical degree-two homology of the constructed total complex. -/
def cechCohomologyTwoIso :
    (cechComplex k).homology 2 ≅ ModuleCat.of k (CechH2 k) :=
  (cechComplex k).homologyIsoSc' 1 2 3
      (CochainComplex.prev_nat_succ 1) (CochainComplex.next ℕ 2) ≪≫
    ShortComplex.homologyMapIso (cechDegreeTwoShortComplexIso k) ≪≫
      (cechDegreeTwoShortComplex k).moduleCatHomologyIso

/-- Residue annihilates every actual total boundary, not just exact overlap forms. -/
theorem cechBoundaries_le_ker_residue :
    cechBoundaries k ≤ LinearMap.ker (LaurentDeRham.closedFormResidue k) := by
  rintro _ ⟨x, rfl⟩
  change LaurentDeRham.kaehlerResidue k
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]
      (cechDifferentialOne k x)) = 0
  change LaurentDeRham.kaehlerResidue k
    ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k])
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (cechIncomingForm k x))) = 0
  rw [LinearEquiv.apply_symm_apply]
  change LaurentDeRham.kaehlerResidue k
    (chartInfinityFormsMap k x.2.1 - chartZeroFormsMap k x.1 -
      D k (LaurentPolynomial k) x.2.2) = 0
  rw [map_sub, map_sub, residue_chartInfinityFormsMap, residue_chartZeroFormsMap,
    LaurentDeRham.kaehlerResidue_D, sub_self, sub_self]

/-- The actual residue detector descends to total degree-two cohomology. -/
def cechResidue : CechH2 k →ₗ[k] k :=
  (cechBoundaries k).liftQ (LaurentDeRham.closedFormResidue k)
    (cechBoundaries_le_ker_residue k)

@[simp]
theorem cechResidue_class (ω : closedForms k (LaurentPolynomial k) 1) :
    cechResidue k (cechClass k ω) = LaurentDeRham.closedFormResidue k ω := rfl

end

end HodgeConjecture.ProjectiveLineDeRham
