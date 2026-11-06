module

import HodgeConjecture.Realization.DeRham.CohomologyProduct
import HodgeConjecture.Realization.DeRham.ProjectiveLineChern
import HodgeConjecture.Realization.DeRham.ProjectiveLineCohomology
import HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-!
Positive-degree forms, actual closed/exact quotients and categorical
homology, the two actual projective-line charts, and the ordinary Čech
first-Chern map. The original integral and rational Chow quotients map to
this degree-two target after actual principal-divisor degree zero is proved.
Boundary independence is checked on actual forms and on both local
trivializations. Residue detects nonzero degree-one and total degree-two
classes. No Bloch-Chow, scheme-hypercohomology or Betti/Hodge comparison
is supplied as an assumption in these checks.
-/

open AlgebraicGeometry CategoryTheory KaehlerDifferential
open HodgeConjecture HodgeConjecture.AffineDeRham
open HodgeConjecture.ProjectiveLineDeRham

noncomputable section

universe u

section Affine

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

-- Multiplication and inversion act on the original unit symbols before quotienting.
example (u v : Aˣ) :
    logarithmicRegulator k A (Additive.ofMul (u * v⁻¹)) =
      logarithmicClass k A u - logarithmicClass k A v := by
  rw [logarithmicRegulator_apply, logarithmicClass_mul, logarithmicClass_inv,
    sub_eq_add_neg]

-- Integral powers include negative powers on the actual Kähler form.
example (u : Aˣ) : logarithmicDifferential k A (u ^ (-3 : ℤ)) =
    (-3 : ℤ) • logarithmicDifferential k A u :=
  logarithmicDifferential_zpow k A u (-3)

-- A unit multiplied by its inverse has zero class in the genuine H¹ quotient.
example (u : Aˣ) :
    logarithmicClass k A u + logarithmicClass k A u⁻¹ = 0 := by
  rw [logarithmicClass_inv, add_neg_cancel]

-- Replacing both representatives by actual incoming differentials leaves cup unchanged.
example (ω η : closedForms k A 1) (f g : ⋀[A]^0 Ω[A⁄k]) :
    cohomologyClass k A 2
        (closedOneWedge k A (ω + differentialToClosedForms k A 0 f)
          (η + differentialToClosedForms k A 0 g)) =
      cohomologyClass k A 2 (closedOneWedge k A ω η) := by
  rw [← cupOne_class_class, ← cupOne_class_class]
  simp only [map_add, cohomologyClass_differential, add_zero]

-- The mixed terms cancel for arbitrary genuine H¹ classes, in every characteristic.
example (α β : Cohomology k A 1) : cupOne k A α β + cupOne k A β α = 0 := by
  rw [cupOne_swap k A α β, neg_add_cancel]

-- Bilinearity is retained after the actual quotient descent.
example (α β γ : Cohomology k A 1) :
    cupOne k A (α + β) γ = cupOne k A α γ + cupOne k A β γ ∧
      cupOne k A α (β + γ) = cupOne k A α β + cupOne k A α γ := by
  constructor
  · exact LinearMap.congr_fun ((cupOne k A).map_add α β) γ
  · exact (cupOne k A α).map_add β γ

end Affine

-- Actual nonzero logarithmic cohomology exists over the complex coefficient field.
example : LaurentDeRham.coordinateClass ℂ ≠ 0 := LaurentDeRham.coordinateClass_ne_zero ℂ

-- Residue reads powers of the original coordinate unit in H¹.
example : LaurentDeRham.cohomologyResidue ℚ
    (logarithmicClass ℚ (LaurentPolynomial ℚ) (LaurentDeRham.variableUnit ℚ ^ 3)) = 3 := by
  rw [logarithmicClass_pow, map_nsmul]
  change (3 : ℕ) • LaurentDeRham.cohomologyResidue ℚ
    (LaurentDeRham.coordinateClass ℚ) = 3
  rw [LaurentDeRham.cohomologyResidue_coordinateClass]
  norm_num

-- Signed rational coefficients are genuinely detected, without imposing rationality on ℂ.
example : LaurentDeRham.cohomologyResidue ℚ
    ((-3 / 2 : ℚ) • LaurentDeRham.coordinateClass ℚ) = -3 / 2 := by
  rw [map_smul, LaurentDeRham.cohomologyResidue_coordinateClass, smul_eq_mul, mul_one]

section Projective

variable (k : Type u) [CommRing k]

-- The inverse-coordinate ring restriction is the overlap map of the actual glued scheme.
example :
    projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      Spec.map (CommRingCat.ofHom (chartInfinityRingMap k).toRingHom) ≫
        projectiveLineYChart k := by
  rw [projectiveLineOverlap_compat, ← Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.toRingHom) ≫
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent) =
      Spec.map (CommRingCat.ofHom (chartInfinityRingMap k).toRingHom)
  rw [← Spec.map_comp]
  rfl

-- All chart-form and overlap-function boundary terms vanish in total degree two.
example (x : CechOne k) : cechResidue k (cechClass k (cechToClosedForms k x)) = 0 := by
  rw [cechClass_boundary, map_zero]

-- Adding an arbitrary actual total boundary preserves the class.
example (ω : closedForms k (LaurentPolynomial k) 1) (x : CechOne k) :
    cechClass k (ω + cechToClosedForms k x) = cechClass k ω := by
  rw [map_add, cechClass_boundary, add_zero]

-- The whole incoming total differential has zero residue, before passing to cohomology.
example (x : CechOne k) :
    LaurentDeRham.closedFormResidue k (cechToClosedForms k x) = 0 :=
  cechBoundaries_le_ker_residue k ⟨x, rfl⟩

-- Changing both chart trivializations preserves the resulting ordinary Chern class.
example (t : Additive (LaurentPolynomial k)ˣ)
    (u : Additive (Polynomial k)ˣ × Additive (Polynomial k)ˣ) :
    firstChern k (transitionClass k (t + chartCoboundary k u)) =
      firstChern k (transitionClass k t) := by
  rw [firstChern_transitionClass, firstChern_transitionClass,
    firstChernTransition_changeTrivialization]

-- A chart coboundary represents the trivial first-Chern class.
example (u : Additive (Polynomial k)ˣ × Additive (Polynomial k)ˣ) :
    firstChern k (transitionClass k (chartCoboundary k u)) = 0 := by
  rw [firstChern_transitionClass]
  exact chartCoboundary_le_ker_firstChernTransition k ⟨u, rfl⟩

end Projective

-- Negative tensor powers have the correct signed ordinary Chern normalization.
example : cechResidue ℚ
    (firstChern ℚ (transitionClass ℚ
      (Additive.ofMul (LaurentDeRham.variableUnit ℚ ^ (-3 : ℤ))))) = -3 := by
  rw [firstChern_transitionClass, firstChernTransition_coordinate_zpow, map_zsmul,
    cechResidue_chernCoordinate]
  norm_num

-- The computed Chern class remains nonzero in categorical degree-two homology
-- of the constructed total complex, not just in a coordinate presentation.
example : (cechCohomologyTwoIso ℚ).inv.hom (chernCoordinate ℚ) ≠ 0 := by
  intro h
  have hh := congrArg (cechCohomologyTwoIso ℚ).hom.hom h
  exact chernCoordinate_ne_zero ℚ (by simpa using hh)

-- Complex coefficients are detected by the actual total-degree-two residue functional.
example : cechResidue ℂ (chernCoordinateLinearMap ℂ Complex.I) = Complex.I :=
  cechResidue_chernCoordinateLinearMap ℂ Complex.I

section ProjectiveCohomology

variable (k : Type u) [CommRing k]

-- Every actual closed representative has its original residue as its sole coordinate.
example (ω : closedForms k (LaurentPolynomial k) 1) :
    cechClass k ω = LaurentDeRham.closedFormResidue k ω • chernCoordinate k :=
  cechClass_eq_residue_smul k ω

-- The residue computation is an inverse on every class of the entire boundary quotient.
example (z : CechH2 k) : (cechResidueEquiv k).symm (cechResidue k z) = z :=
  (cechResidueEquiv k).symm_apply_apply z

end ProjectiveCohomology

-- The coordinate computation also sends the actual categorical homology class to one.
example : (cechCohomologyTwoCoordinates ℤ).hom.hom
    ((cechCohomologyTwoIso ℤ).inv.hom (chernCoordinate ℤ)) = 1 := by
  change cechResidueEquiv ℤ ((cechCohomologyTwoIso ℤ).hom.hom
    ((cechCohomologyTwoIso ℤ).inv.hom (chernCoordinate ℤ))) = 1
  have h := congrArg
    (fun e : ModuleCat.of ℤ (CechH2 ℤ) ⟶ ModuleCat.of ℤ (CechH2 ℤ) ↦
      e.hom (chernCoordinate ℤ)) (cechCohomologyTwoIso ℤ).inv_hom_id
  change (cechCohomologyTwoIso ℤ).hom.hom
    ((cechCohomologyTwoIso ℤ).inv.hom (chernCoordinate ℤ)) = chernCoordinate ℤ at h
  rw [h]
  exact cechResidue_chernCoordinate ℤ

-- In characteristic two this is an actual regular-chart boundary, with no division by two.
example : laurentClass (ZMod 2) (LaurentPolynomial.T 2) = 0 := by
  simpa using laurentClass_positive (ZMod 2) 1 1

-- A coefficient ring with zero divisors retains the full residue equivalence and normalization.
example : cechResidueEquiv (ZMod 6) (chernCoordinate (ZMod 6)) = 1 ∧
    Function.Bijective (cechResidue (ZMod 6)) :=
  ⟨cechResidue_chernCoordinate (ZMod 6), (cechResidueEquiv (ZMod 6)).bijective⟩

section OrdinaryCycles

open SchemeCycles ProjectiveLineCycles ProjectiveLineCycleClass

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

-- The old actual principal divisor and every old relation carrier have degree zero,
-- with neither invariance nor a replacement cycle model supplied as an input.
example (f : (projectiveLine k).functionFieldˣ)
    (d : PrincipalRelationData (dimensionFunction k) 0) :
    coefficientSum k ℤ (principalDivisor (projectiveLine k) f) = 0 ∧
      integralDegree k (principalRelation (dimensionFunction k) 0 d) = 0 :=
  ⟨coefficientSum_principalDivisor_eq_zero k f, integralDegree_principalRelation k d⟩

-- Integral-to-rational coefficient extension retains the original ordinary Chow quotients.
example (z : ChowGroup (dimensionFunction k) 0) :
    rationalChowDegree k (chowRationalize (dimensionFunction k) 0 z) =
      (integralChowDegree k z : ℚ) := rationalChowDegree_chowRationalize k z

-- The two actual cycle maps agree through the original coefficient-extension map.
example (z : ChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (chowRationalize (dimensionFunction k) 0 z)) =
      integralCycleClass k z := cycleClass_chowRationalize k z

-- An original relation carrier, rationalized by the existing API, has zero cycle class.
example (d : PrincipalRelationData (dimensionFunction k) 0) :
    cycleClass k (rationalClassMap (dimensionFunction k) 0
      (cyclesOfDegreeRationalize (dimensionFunction k) 0
        (principalRelation (dimensionFunction k) 0 d))) = 0 :=
  cycleClass_principalRelation k d

-- The actual source point classes are nonzero in both original quotients.
example : integralInfinityClass k ≠ 0 ∧ rationalInfinityClass k ≠ 0 := by
  constructor
  · intro h
    have hh := congrArg (integralChowDegree k) h
    rw [integralChowDegree_infinity, map_zero] at hh
    exact one_ne_zero hh
  · intro h
    have hh := congrArg (rationalChowDegree k) h
    rw [rationalChowDegree_infinity, map_zero] at hh
    exact one_ne_zero hh

-- The original rational infinity cycle maps to the actual transition first-Chern class.
example :
    RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (rationalInfinityClass k)) =
      firstChern k (transitionClass k (Additive.ofMul (LaurentDeRham.variableUnit k))) ∧
      cechResidue k (RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (rationalInfinityClass k))) = 1 := by
  constructor
  · rw [cycleClass_apply, rationalChowDegree_infinity, Rat.cast_one, one_smul,
      firstChern_transitionClass]
    rfl
  · rw [residue_cycleClass, rationalChowDegree_infinity, Rat.cast_one]

-- Signed rational point weights are read by the independently constructed residue detector.
example : cechResidue k (RestrictScalars.addEquiv ℚ k (CechH2 k)
    (cycleClass k ((-5 / 2 : ℚ) • rationalInfinityClass k))) = (-5 / 2 : k) := by
  rw [residue_cycleClass, map_smul, rationalChowDegree_infinity, smul_eq_mul, mul_one]
  norm_num

-- Q-linearity is on the actual ordinary Chow group and the same Cech H² with scalar restriction.
example (z w : RationalChowGroup (dimensionFunction k) 0) :
    cycleClass k ((2 : ℚ) • z - w) = (2 : ℚ) • cycleClass k z - cycleClass k w := by
  rw [map_sub, map_smul]

-- Every two actual coefficient-one closed-point cycles have the same normalized image.
example (x y : projectiveLine k) (hx : x ≠ genericPoint (projectiveLine k))
    (hy : y ≠ genericPoint (projectiveLine k)) :
    cycleClass k
      (rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ x hx) -
        rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ y hy)) = 0 := by
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply (RestrictScalars.addEquiv ℚ k (CechH2 k)).injective
  rw [cycleClass_pointCycle, cycleClass_pointCycle]

end OrdinaryCycles

-- The concrete ordinary rational cycle map over the complex field is nonzero.
example : ProjectiveLineCycleClass.cycleClass ℂ ≠ 0 :=
  ProjectiveLineCycleClass.cycleClass_ne_zero ℂ

-- Complex multiples outside the rational degree image do not become rational cycle classes.
-- This is a coefficient guard, with no assertion of rational Hodge membership.
example : (RestrictScalars.addEquiv ℚ ℂ (CechH2 ℂ)).symm (Complex.I • chernCoordinate ℂ) ∉
    LinearMap.range (ProjectiveLineCycleClass.cycleClass ℂ) := by
  rintro ⟨z, hz⟩
  have hr := congrArg (fun w : ProjectiveLineCycleClass.RationalTarget ℂ ↦
    cechResidue ℂ (RestrictScalars.addEquiv ℚ ℂ (CechH2 ℂ) w)) hz
  rw [ProjectiveLineCycleClass.residue_cycleClass, AddEquiv.apply_symm_apply,
    map_smul, cechResidue_chernCoordinate, smul_eq_mul, mul_one] at hr
  have hi := congrArg Complex.im hr
  norm_num at hi

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `KaehlerDifferential.deRhamDifferential_smul,
    `KaehlerDifferential.deRhamDifferential_wedgeMul,
    `KaehlerDifferential.deRhamDifferential_wedgeMul_eq_zero_of_closed,
    `HodgeConjecture.AffineDeRham.cohomologyIso,
    `HodgeConjecture.AffineDeRham.cohomologyClass_succ_eq_zero_iff,
    `HodgeConjecture.AffineDeRham.closedOneWedge_exact_left,
    `HodgeConjecture.AffineDeRham.closedOneWedge_exact_right,
    `HodgeConjecture.AffineDeRham.cupOne_class_class,
    `HodgeConjecture.AffineDeRham.cupOne_self,
    `HodgeConjecture.AffineDeRham.logarithmicForm_closed,
    `HodgeConjecture.AffineDeRham.logarithmicDifferential_mul,
    `HodgeConjecture.AffineDeRham.map_logarithmicDifferential,
    `HodgeConjecture.LaurentDeRham.kaehlerResidue_D,
    `HodgeConjecture.LaurentDeRham.dlogT_not_exact,
    `HodgeConjecture.LaurentDeRham.coordinateClass_ne_zero,
    `AlgebraicGeometry.projectiveLine_charts_cover,
    `AlgebraicGeometry.projectiveLineOverlap_isPullback,
    `HodgeConjecture.ProjectiveLineDeRham.residue_chartZeroFormsMap,
    `HodgeConjecture.ProjectiveLineDeRham.residue_chartInfinityFormsMap,
    `HodgeConjecture.ProjectiveLineDeRham.cechDifferential_comp,
    `HodgeConjecture.ProjectiveLineDeRham.cechCohomologyTwoIso,
    `HodgeConjecture.ProjectiveLineDeRham.cechBoundaries_le_ker_residue,
    `HodgeConjecture.ProjectiveLineDeRham.chartCoboundary_le_ker_firstChernTransition,
    `HodgeConjecture.ProjectiveLineDeRham.firstChern,
    `HodgeConjecture.ProjectiveLineDeRham.firstChern_transitionClass,
    `HodgeConjecture.ProjectiveLineDeRham.firstChernTransition_changeTrivialization,
    `HodgeConjecture.ProjectiveLineDeRham.cechResidue_chernCoordinate,
    `HodgeConjecture.ProjectiveLineDeRham.firstChern_ne_zero,
    `HodgeConjecture.ProjectiveLineDeRham.chernCoordinateLinearMap_injective,
    `HodgeConjecture.ProjectiveLineDeRham.overlapClass_chartZero,
    `HodgeConjecture.ProjectiveLineDeRham.overlapClass_chartInfinity,
    `HodgeConjecture.ProjectiveLineDeRham.laurentClass_eq_constantCoefficient,
    `HodgeConjecture.ProjectiveLineDeRham.cechClass_eq_residue_smul,
    `HodgeConjecture.ProjectiveLineDeRham.cechResidueEquiv,
    `HodgeConjecture.ProjectiveLineDeRham.cechCohomologyTwoCoordinates,
    `HodgeConjecture.ProjectiveLineCycles.principalRelation_exists_principalDivisor,
    `HodgeConjecture.ProjectiveLineCycles.coefficientSum_principalDivisor_eq_zero,
    `HodgeConjecture.ProjectiveLineCycles.principalRelations_le_ker_integralDegree,
    `HodgeConjecture.ProjectiveLineCycles.rationalPrincipalRelations_le_ker_rationalDegree,
    `HodgeConjecture.ProjectiveLineCycles.rationalChowDegree,
    `HodgeConjecture.ProjectiveLineCycles.rationalChowDegree_chowRationalize,
    `HodgeConjecture.ProjectiveLineCycleClass.integralCycleClass_infinity,
    `HodgeConjecture.ProjectiveLineCycleClass.cycleClass_pointCycle,
    `HodgeConjecture.ProjectiveLineCycleClass.residue_cycleClass,
    `HodgeConjecture.ProjectiveLineCycleClass.cycleClass_ne_zero,
    `HodgeConjecture.ProjectiveLineCycleClass.cycleClass_principalRelation,
    `HodgeConjecture.ProjectiveLineCycleClass.cycleClass_chowRationalize,
    `HodgeConjecture.ProjectiveLineCycleClass.scalar_chernCoordinate_not_mem_cycleClass_range]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
