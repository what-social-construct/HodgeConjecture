module

public import HodgeConjecture.Geometry.ProjectiveLineProperties
public import HodgeConjecture.Cycles.IntegralCodimension
public import HodgeConjecture.Cycles.TopDegreeRelations
public import HodgeConjecture.Cycles.CoefficientExtension
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

/-!
# The actual projective-line grading and zero-cycle coefficient degree

The canonical field dimension function has generic value one, so its
existing degree-zero cycles are precisely cycles on prime divisors.
Every degree-one integral relation carrier is the whole actual projective
line, through its existing closed immersion. The original relation cycles
are consequently actual ambient principal divisors.

The coefficient-sum maps retain the existing integral and rational cycle
modules. On a principal divisor they are exactly the finite sum of its
actual local divisor orders. Rational-equivalence invariance is not assumed
here. Over non-algebraically-closed fields an unweighted coefficient sum is
not asserted to be the residue-degree-weighted geometric degree.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineCycles

open AlgebraicGeometry CategoryTheory SchemeCycles

noncomputable section

universe u v

variable (k : Type u) [Field k]

/-- The existing canonical field grading on the original glued projective line. -/
def dimensionFunction : DimensionFunction (projectiveLine k) :=
  DimensionFunction.ofLocallyOfFiniteType k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k))

/-- The generic value is derived from the actual dimension-one theorem. -/
@[simp]
theorem dimensionFunction_genericPoint : dimensionFunction k (genericPoint (projectiveLine k)) = 1 := by
  have h := integral_topologicalKrullDim_eq_ofLocallyOfFiniteType k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k))
  rw [topologicalKrullDim_projectiveLine] at h
  have hn := DimensionFunction.ofLocallyOfFiniteType_nonneg k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) (genericPoint (projectiveLine k))
  change 1 = ((dimensionFunction k (genericPoint (projectiveLine k))).toNat : WithBot ℕ∞) at h
  change 0 ≤ dimensionFunction k (genericPoint (projectiveLine k)) at hn
  have ht : (dimensionFunction k (genericPoint (projectiveLine k))).toNat = 1 := by
    exact_mod_cast h.symm
  omega

/-- Every actual nongeneric point has zero canonical field dimension. -/
theorem dimensionFunction_eq_zero_of_ne_genericPoint (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) : dimensionFunction k x = 0 := by
  have hle : x ≤ genericPoint (projectiveLine k) :=
    Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
  have hnot : ¬genericPoint (projectiveLine k) ≤ x := by
    intro hge
    exact hx (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq)
  have hlt := (dimensionFunction k).strictMono (lt_iff_le_not_ge.mpr ⟨hle, hnot⟩)
  rw [dimensionFunction_genericPoint] at hlt
  have hn := DimensionFunction.ofLocallyOfFiniteType_nonneg k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) x
  change 0 ≤ dimensionFunction k x at hn
  omega

/-- The reduced closure of an actual nongeneric point is an original degree-zero generator. -/
theorem supportDegree_pointSupport_eq_zero_of_ne_genericPoint (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    supportDegree (dimensionFunction k) (pointSupport (projectiveLine k) x) = 0 := by
  rw [supportDegree, ambientGenericPoint_pointSupport]
  exact dimensionFunction_eq_zero_of_ne_genericPoint k x hx

/-- Actual degree-zero integral generators have codimension one, and conversely. -/
theorem supportDegree_zero_iff_supportCodimension_one
    (W : IntegralClosedSubscheme (projectiveLine k)) :
    supportDegree (dimensionFunction k) W = 0 ↔ supportCodimension W = 1 := by
  have h := supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
    k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)) W 1
  change supportDegree (dimensionFunction k) W =
    dimensionFunction k (genericPoint (projectiveLine k)) - (1 : ℤ) ↔
      supportCodimension W = (1 : ℕ∞) at h
  simpa only [dimensionFunction_genericPoint, sub_self] using h

/-- Every original degree-one carrier immersion is an actual scheme isomorphism. -/
theorem integralSubscheme_isIso_of_supportDegree_one
    (W : IntegralClosedSubscheme (projectiveLine k))
    (hW : supportDegree (dimensionFunction k) W = 1) : IsIso W.val.subschemeι :=
  integralSubscheme_isIso_of_supportDegree_eq (dimensionFunction k) W
    (hW.trans (dimensionFunction_genericPoint k).symm)

/-- Every actual degree-zero principal relation is an ambient principal divisor of P¹. -/
theorem principalRelation_exists_principalDivisor
    (d : PrincipalRelationData (dimensionFunction k) 0) :
    ∃ f : (projectiveLine k).functionFieldˣ,
      (principalRelation (dimensionFunction k) 0 d).val = principalDivisor (projectiveLine k) f := by
  have := d.1.val.property
  have hW : supportDegree (dimensionFunction k) d.1.val =
      dimensionFunction k (genericPoint (projectiveLine k)) := by
    rw [dimensionFunction_genericPoint]
    simpa using d.1.property
  change ∃ f, ambientPrincipalDivisor d.1.val d.2 = principalDivisor (projectiveLine k) f
  exact exists_ambientPrincipalDivisor_eq_principalDivisor (dimensionFunction k) d.1.val hW d.2

/-- The coefficient sum on the original cycle module; no relation quotient is involved. -/
def coefficientSum (R : Type v) [Semiring R] : Cycles (projectiveLine k) R →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ ↦ (1 : R))

@[simp]
theorem coefficientSum_single (R : Type v) [Semiring R]
    (W : IntegralClosedSubscheme (projectiveLine k)) (a : R) :
    coefficientSum k R (Finsupp.single W a) = a := by
  simp [coefficientSum]

/-- The functional retains precisely the actual finite list of coefficients. -/
theorem coefficientSum_apply (R : Type v) [Semiring R] (c : Cycles (projectiveLine k) R) :
    coefficientSum k R c = c.sum (fun _ a ↦ a) := by
  simp [coefficientSum, Finsupp.linearCombination_apply]

/-- Restrict the original coefficient functional to actual degree-zero cycles. -/
def coefficientDegree (R : Type v) [Semiring R] :
    cyclesOfDegree R (dimensionFunction k) 0 →ₗ[R] R :=
  (coefficientSum k R).comp (cyclesOfDegree R (dimensionFunction k) 0).subtype

/-- Integral zero-cycle coefficient degree on the original homogeneous submodule. -/
abbrev integralDegree := coefficientDegree k ℤ

/-- Rational zero-cycle coefficient degree on the original homogeneous submodule. -/
abbrev rationalDegree := coefficientDegree k ℚ

@[simp]
theorem coefficientDegree_apply (R : Type v) [Semiring R]
    (c : cyclesOfDegree R (dimensionFunction k) 0) :
    coefficientDegree k R c = coefficientSum k R c.val := rfl

@[simp]
theorem coefficientDegree_single (R : Type v) [Semiring R]
    (W : IntegralClosedSubscheme (projectiveLine k)) (a : R)
    (hW : supportDegree (dimensionFunction k) W = 0) :
    coefficientDegree k R ⟨Finsupp.single W a,
      single_mem_cyclesOfDegree R (dimensionFunction k) 0 W a hW⟩ = a := by
  exact coefficientSum_single k R W a

/-- The actual reduced point-closure cycle in the original homogeneous cycle module. -/
def pointCycle (R : Type v) [Semiring R] (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) : cyclesOfDegree R (dimensionFunction k) 0 :=
  ⟨fundamentalCycle R (pointSupport (projectiveLine k) x),
    fundamentalCycle_mem_cyclesOfDegree R (dimensionFunction k) 0
      (pointSupport (projectiveLine k) x)
      (supportDegree_pointSupport_eq_zero_of_ne_genericPoint k x hx)⟩

/-- Every coefficient-one actual closed point cycle has coefficient degree one. -/
@[simp]
theorem coefficientDegree_pointCycle (R : Type v) [Semiring R] (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    coefficientDegree k R (pointCycle k R x hx) = 1 :=
  coefficientSum_single k R (pointSupport (projectiveLine k) x) 1

/-- The actual principal divisor has exactly the finite sum of its prime local orders. -/
theorem coefficientSum_principalDivisor_prime
    (f : (projectiveLine k).functionFieldˣ) :
    coefficientSum k ℤ (principalDivisor (projectiveLine k) f) =
      ∑ᶠ Z : PrimeDivisor (projectiveLine k), primeDivisorOrder (projectiveLine k) Z f := by
  classical
  let a : PrimeDivisor (projectiveLine k) →₀ ℤ := Finsupp.ofSupportFinite
    (fun Z ↦ primeDivisorOrder (projectiveLine k) Z f)
    (finite_primeDivisorOrder_support (projectiveLine k) f)
  rw [coefficientSum_apply, principalDivisor, Finsupp.sum_embDomain]
  change a.sum (fun _ z ↦ z) = ∑ᶠ Z, primeDivisorOrder (projectiveLine k) Z f
  have hs : Function.support (fun Z ↦ primeDivisorOrder (projectiveLine k) Z f) ⊆
      (a.support : Set (PrimeDivisor (projectiveLine k))) := by
    intro Z hZ
    exact Finsupp.mem_support_iff.mpr hZ
  exact (finsum_eq_finsetSum_of_support_subset
    (fun Z ↦ primeDivisorOrder (projectiveLine k) Z f) hs).symm

/-- The same coefficient sum, indexed by the original actual codimension-one points. -/
theorem coefficientSum_principalDivisor
    (f : (projectiveLine k).functionFieldˣ) :
    coefficientSum k ℤ (principalDivisor (projectiveLine k) f) =
      ∑ᶠ x : DivisorPoint (projectiveLine k), divisorOrder (projectiveLine k) x f := by
  rw [coefficientSum_principalDivisor_prime]
  simpa only [primeDivisorOrder_pointSupport] using
    (finsum_comp_equiv (divisorPointEquivPrimeDivisor (projectiveLine k))
      (f := fun Z ↦ primeDivisorOrder (projectiveLine k) Z f)).symm

/-- Coefficient extension preserves the same finite sum, with the integer sum cast to ℚ. -/
theorem coefficientSum_mapRange_intCast (c : Cycles (projectiveLine k) ℤ) :
    coefficientSum k ℚ (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      (coefficientSum k ℤ c : ℚ) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add W a c _ _ ih =>
      simpa [Finsupp.mapRange_add] using ih

/-- The original integral-to-rational coefficient map preserves the zero-cycle degree. -/
theorem rationalDegree_rationalize (c : cyclesOfDegree ℤ (dimensionFunction k) 0) :
    rationalDegree k (cyclesOfDegreeRationalize (dimensionFunction k) 0 c) =
      (integralDegree k c : ℚ) :=
  coefficientSum_mapRange_intCast k c.val

end

end HodgeConjecture.ProjectiveLineCycles
