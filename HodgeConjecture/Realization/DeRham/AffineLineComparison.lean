module

public import HodgeConjecture.Realization.DeRham.Polynomial
public import HodgeConjecture.Realization.Betti.SingularPathConnected
public import HodgeConjecture.Realization.Betti.Examples.AffineLineComplexPoints
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

/-!
# The actual affine-line comparison in degree zero

The algebraic space is the universal-derivation kernel of `ℂ[X]`. The
rational topological space is the singular zero-cocycle algebra on actual
complex-algebra points with their regular-function evaluation topology.
Scalar extension is the genuine tensor product `ℂ ⊗[ℚ] H⁰_B`.

The comparison preserves multiplication and agrees with evaluation at every
actual point. Polynomial substitution induces both pullbacks, and their
comparison square is proved. The final homology isomorphism uses the actual
constructed de Rham complex. No higher-degree or general cycle-class
comparison is asserted here.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineLineDeRham

open CategoryTheory AffineLineComplexPoints
open scoped Polynomial TensorProduct

noncomputable section

/-- The genuine rational singular zero-cohomology of the affine line's complex points. -/
abbrev Betti := SingularDegreeZero.H0 Point

/-- The actual affine de Rham zero-cohomology of the polynomial coordinate ring. -/
abbrev DeRham := AffineDeRham.H0 ℂ ℂ[X]

/-- Betti coordinates come from evaluation and proved path connectedness. -/
def bettiCoordinates : Betti ≃ₐ[ℚ] ℚ :=
  SingularDegreeZero.equivConstants Point (evalPoint 0)

/-- Algebraic coordinates come from the proved closed-polynomial calculation. -/
abbrev deRhamCoordinates : DeRham ≃ₐ[ℂ] ℂ := AffineDeRham.affineLineCoordinates ℂ

/-- All actual point evaluations give the same rational Betti coordinate. -/
theorem bettiCoordinates_eval (h : Betti) (p : Point) :
    bettiCoordinates h = SingularDegreeZero.eval Point h p :=
  SingularDegreeZero.eval_eq Point h (evalPoint 0) p

/-- Algebraic coordinates agree with evaluation of the original regular function. -/
theorem deRhamCoordinates_eval (a : DeRham) (p : Point) :
    p a.val = deRhamCoordinates a := by
  have ha := congrArg (fun b : DeRham ↦ b.val) (deRhamCoordinates.symm_apply_apply a)
  have hc : Polynomial.C (deRhamCoordinates a) = a.val := by
    simpa only [AffineDeRham.affineLineCoordinates_symm_coe] using ha
  rw [← hc]
  exact p.commutes _

/-- Genuine scalar extension of the independently constructed rational Betti space. -/
abbrev Complexification := ℂ ⊗[ℚ] Betti

/-- Scalar extension of Betti evaluation, with the tensor unit comparison. -/
def complexCoordinates : Complexification ≃ₐ[ℂ] ℂ :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) bettiCoordinates).trans
    (Algebra.TensorProduct.rid ℚ ℂ ℂ)

@[simp]
theorem complexCoordinates_tmul (c : ℂ) (h : Betti) :
    complexCoordinates (c ⊗ₜ[ℚ] h) = c * (bettiCoordinates h : ℂ) := by
  change bettiCoordinates h • c = c * (bettiCoordinates h : ℂ)
  rw [Algebra.smul_def, mul_comm, eq_ratCast]

/-- Extend actual singular evaluation at a point, independently of the comparison. -/
def complexEvaluation (p : Point) : Complexification →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.productLeftAlgHom (AlgHom.id ℂ ℂ)
    ((Algebra.ofId ℚ ℂ).comp (SingularDegreeZero.evalAt Point p))

@[simp]
theorem complexEvaluation_tmul (p : Point) (c : ℂ) (h : Betti) :
    complexEvaluation p (c ⊗ₜ[ℚ] h) = c * (SingularDegreeZero.eval Point h p : ℂ) := rfl

/-- Every scalar-extended point evaluation agrees with the constant coordinates. -/
theorem complexEvaluation_eq_coordinates (p : Point) :
    complexEvaluation p = complexCoordinates.toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c h
  change complexEvaluation p (c ⊗ₜ[ℚ] h) = complexCoordinates (c ⊗ₜ[ℚ] h)
  rw [complexEvaluation_tmul, complexCoordinates_tmul, bettiCoordinates_eval h p]

/-- The canonical rational embedding remains the pure tensor `1 ⊗ h`. -/
def rationalEmbedding : Betti →ₗ[ℚ] Complexification :=
  TensorProduct.mk ℚ ℂ Betti 1

@[simp]
theorem complexCoordinates_rationalEmbedding (h : Betti) :
    complexCoordinates (rationalEmbedding h) = (bettiCoordinates h : ℂ) := by
  simp [rationalEmbedding]

theorem rationalEmbedding_injective : Function.Injective rationalEmbedding := by
  intro h k hk
  apply bettiCoordinates.injective
  have hc := congrArg complexCoordinates hk
  simp only [complexCoordinates_rationalEmbedding] at hc
  exact_mod_cast hc

/-- The algebraic-to-Betti comparison is constructed from the two actual cohomologies. -/
def bettiComparison : DeRham ≃ₐ[ℂ] Complexification :=
  deRhamCoordinates.trans complexCoordinates.symm

@[simp]
theorem complexCoordinates_bettiComparison (a : DeRham) :
    complexCoordinates (bettiComparison a) = deRhamCoordinates a := by
  simp [bettiComparison]

/-- The comparison is ordinary evaluation on every original complex-valued point. -/
theorem bettiComparison_evaluation (a : DeRham) (p : Point) :
    complexEvaluation p (bettiComparison a) = p a.val := by
  rw [complexEvaluation_eq_coordinates]
  change complexCoordinates (bettiComparison a) = p a.val
  rw [complexCoordinates_bettiComparison, deRhamCoordinates_eval]

/-- Complex constants map to actual pure tensors with the constant unit cocycle. -/
theorem bettiComparison_constant (c : ℂ) :
    bettiComparison (deRhamCoordinates.symm c) =
      c ⊗ₜ[ℚ] SingularDegreeZero.constantClass Point 1 := by
  apply complexCoordinates.injective
  simp [bettiCoordinates]

/-- Rational normalization agrees with the independently defined rational embedding. -/
theorem bettiComparison_rational (q : ℚ) :
    bettiComparison (deRhamCoordinates.symm (q : ℂ)) =
      rationalEmbedding (SingularDegreeZero.constantClass Point q) := by
  apply complexCoordinates.injective
  simp [bettiCoordinates]

/-- Cup multiplication is preserved in the genuine scalar-extended cohomology algebra. -/
theorem bettiComparison_mul (a b : DeRham) :
    bettiComparison (a * b) = bettiComparison a * bettiComparison b :=
  map_mul bettiComparison a b

/-- The comparison also identifies categorical homology of the original de Rham complex. -/
def cohomologyZeroComparison :
    (KaehlerDifferential.deRhamComplex ℂ ℂ[X]).homology 0 ≅
      ModuleCat.of ℂ Complexification :=
  AffineDeRham.cohomologyZeroIso ℂ ℂ[X] ≪≫ bettiComparison.toLinearEquiv.toModuleIso

/-- Pullback on the original closed-function kernel uses polynomial substitution. -/
def deRhamPullback (f : ℂ[X]) : DeRham →ₐ[ℂ] DeRham :=
  AffineDeRham.map ℂ (Polynomial.aeval f)

/-- Pullback of actual singular cochains by the continuous polynomial point map. -/
def bettiPullback (f : ℂ[X]) : Betti →ₐ[ℚ] Betti :=
  SingularDegreeZero.pullback (mapContinuous f)

/-- Scalar extension of the original rational singular pullback. -/
def complexPullback (f : ℂ[X]) : Complexification →ₐ[ℂ] Complexification :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (bettiPullback f)

@[simp]
theorem deRhamCoordinates_pullback (f : ℂ[X]) (a : DeRham) :
    deRhamCoordinates (deRhamPullback f a) = deRhamCoordinates a := by
  calc
    _ = evalPoint 0 (deRhamPullback f a).val :=
      (deRhamCoordinates_eval (deRhamPullback f a) (evalPoint 0)).symm
    _ = (map f (evalPoint 0)) a.val := rfl
    _ = _ := deRhamCoordinates_eval a _

@[simp]
theorem bettiCoordinates_pullback (f : ℂ[X]) (h : Betti) :
    bettiCoordinates (bettiPullback f h) = bettiCoordinates h :=
  SingularDegreeZero.equivConstants_pullback Point (evalPoint 0) (evalPoint 0)
    (mapContinuous f) h

@[simp]
theorem complexCoordinates_pullback (f : ℂ[X]) (z : Complexification) :
    complexCoordinates (complexPullback f z) = complexCoordinates z := by
  induction z using TensorProduct.inductionOn with
  | tmul c h => simp [complexPullback]
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

/-- Polynomial pullback naturality is proved for the actual two kernel-model maps. -/
theorem bettiComparison_pullback (f : ℂ[X]) (a : DeRham) :
    bettiComparison (deRhamPullback f a) = complexPullback f (bettiComparison a) := by
  apply complexCoordinates.injective
  simp

/-- The complex class with coordinate `I` lies outside the rational embedding. -/
theorem imaginaryClass_not_rational :
    complexCoordinates.symm Complex.I ∉ Set.range rationalEmbedding := by
  rintro ⟨h, hh⟩
  have hc := congrArg complexCoordinates hh
  have hi := congrArg Complex.im hc
  simp only [complexCoordinates_rationalEmbedding, AlgEquiv.apply_symm_apply,
    Complex.ratCast_im, Complex.I_im] at hi
  exact zero_ne_one hi

end

end HodgeConjecture.AffineLineDeRham
