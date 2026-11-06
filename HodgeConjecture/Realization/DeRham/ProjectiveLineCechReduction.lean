module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineCohomology
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-!
# Reducing projective-line total degree two to the sheaf Čech cokernel

Every Laurent function is the difference of actual chart functions.
Consequently its differential is already a difference of chart one-forms.
The total degree-two boundary space is therefore exactly the image of the
one-form restriction difference, the cokernel used by the sheaf
Mayer–Vietoris sequence. No division or characteristic hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDeRham

open KaehlerDifferential LaurentPolynomial

universe u

variable (k : Type u) [CommRing k]

/-- The actual Čech restriction difference for regular functions. -/
def chartFunctionDifference : (Polynomial k × Polynomial k) →ₗ[k] LaurentPolynomial k where
  toFun p := chartInfinityRingMap k p.2 - chartZeroRingMap k p.1
  map_add' p q := by simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
  map_smul' a p := by simp [smul_sub]

/-- Every Laurent function is a difference of functions on the actual two charts. -/
theorem chartFunctionDifference_surjective : Function.Surjective (chartFunctionDifference k) := by
  intro f
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      obtain ⟨p, hp⟩ := hf
      obtain ⟨q, hq⟩ := hg
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | C_mul_T n a =>
      cases n with
      | ofNat m =>
          refine ⟨(-Polynomial.monomial m a, 0), ?_⟩
          change chartInfinityRingMap k 0 - chartZeroRingMap k (-Polynomial.monomial m a) = _
          simp [chartZeroRingMap, Polynomial.toLaurent_C_mul_T]
      | negSucc m =>
          refine ⟨(0, Polynomial.monomial (m + 1) a), ?_⟩
          change chartInfinityRingMap k (Polynomial.monomial (m + 1) a) -
            chartZeroRingMap k 0 = _
          simp [chartInfinityRingMap, Polynomial.toLaurent_C_mul_T, Int.negSucc_eq]

/-- The actual Čech restriction difference for one-forms. -/
def chartFormsDifference : (Ω[Polynomial k⁄k] × Ω[Polynomial k⁄k]) →ₗ[k]
    Ω[LaurentPolynomial k⁄k] where
  toFun ω := chartInfinityFormsMap k ω.2 - chartZeroFormsMap k ω.1
  map_add' ω η := by simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
  map_smul' a ω := by simp [smul_sub]

/-- The overlap-function term in the total differential contributes no additional relations. -/
theorem range_cechIncomingForm_eq :
    LinearMap.range (cechIncomingForm k) = LinearMap.range (chartFormsDifference k) := by
  apply le_antisymm
  · rintro _ ⟨⟨α, β, f⟩, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := chartFunctionDifference_surjective k f
    refine ⟨(α - D k (Polynomial k) p, β - D k (Polynomial k) q), ?_⟩
    change chartInfinityFormsMap k (β - D k (Polynomial k) q) -
        chartZeroFormsMap k (α - D k (Polynomial k) p) =
      chartInfinityFormsMap k β - chartZeroFormsMap k α - D k (LaurentPolynomial k) f
    rw [map_sub, map_sub, chartInfinityFormsMap_D, chartZeroFormsMap_D,
      ← hpq]
    change _ = _ - D k (LaurentPolynomial k)
      (chartInfinityRingMap k q - chartZeroRingMap k p)
    rw [map_sub]
    abel
  · rintro _ ⟨⟨α, β⟩, rfl⟩
    exact ⟨(α, β, 0), by simp [cechIncomingForm, chartFormsDifference]⟩

/-- The original overlap-class map covers every total degree-two cohomology class. -/
theorem overlapClass_surjective : Function.Surjective (overlapClass k) := by
  intro z
  obtain ⟨ω, rfl⟩ := (cechBoundaries k).mkQ_surjective z
  refine ⟨exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k] ω.val, ?_⟩
  apply congrArg (cechClass k)
  apply Subtype.ext
  exact (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm_apply_apply _

/-- The kernel consists precisely of the one-form chart restrictions. -/
theorem ker_overlapClass_eq :
    LinearMap.ker (overlapClass k) = LinearMap.range (chartFormsDifference k) := by
  ext ω
  rw [LinearMap.mem_ker]
  change cechClass k (overlapClosedForm k ω) = 0 ↔ _
  rw [cechClass_eq_zero_iff]
  change (∃ x, cechDifferentialOne k x =
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm ω) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    rw [← range_cechIncomingForm_eq]
    refine ⟨x, ?_⟩
    change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
      (cechIncomingForm k x) = _ at hx
    exact (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm.injective hx
  · rintro ⟨⟨α, β⟩, rfl⟩
    refine ⟨(α, β, 0), ?_⟩
    change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
      (chartInfinityFormsMap k β - chartZeroFormsMap k α - D k (LaurentPolynomial k) 0) = _
    simp only [map_zero, sub_zero]
    rfl

/-- The sheaf Čech one-form cokernel identifies with the original total degree-two target. -/
def formsCokernelEquiv :
    (Ω[LaurentPolynomial k⁄k] ⧸ LinearMap.range (chartFormsDifference k)) ≃ₗ[k] CechH2 k :=
  (Submodule.quotEquivOfEq _ _ (ker_overlapClass_eq k).symm).trans
    ((overlapClass k).quotKerEquivOfSurjective (overlapClass_surjective k))

/-- The quotient comparison retains the original overlap representative. -/
@[simp]
theorem formsCokernelEquiv_mk (ω : Ω[LaurentPolynomial k⁄k]) :
    formsCokernelEquiv k ((LinearMap.range (chartFormsDifference k)).mkQ ω) =
      overlapClass k ω := by
  simp [formsCokernelEquiv]

end HodgeConjecture.ProjectiveLineDeRham
