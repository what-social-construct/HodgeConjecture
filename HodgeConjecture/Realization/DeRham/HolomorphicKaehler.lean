module

public import HodgeConjecture.Realization.DeRham.HolomorphicComplex
public import HodgeConjecture.Geometry.Holomorphic.FunctionAlgebra
public import HodgeConjecture.Realization.DeRham.PresheafComplex
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# The actual Kähler-to-holomorphic differential map in degree one

Complex differentiation is a derivation of the native ring of holomorphic
functions. The existing Kähler universal property supplies the map on
one-forms; an actual algebra map into those functions gives the usual
formula da ↦ d(φ a). No holomorphic regular-evaluation map for a general
scheme, or all-degree algebraic/analytic comparison, is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open TopologicalSpace KaehlerDifferential
open scoped Manifold ContDiff Polynomial
open HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The same exterior derivative on zero-forms, viewed as a derivation of functions. -/
def holomorphicDerivation (U : Opens E) : Derivation ℂ (Functions U) (Sections U 1) where
  toLinearMap := (HolomorphicForms.differential U 0).comp (functionsEquiv U).symm.toLinearMap
  map_one_eq_zero' := by
    change HolomorphicForms.differential U 0 _ = 0
    exact differential_constant U 1
  leibniz' f g := by
    apply (oneFormsEquiv U).injective
    apply ContMDiffMap.ext
    intro x
    change oneCoeffEquiv (HolomorphicForms.differential U 0 ((functionsEquiv U).symm (f * g)) x) =
      oneCoeffEquiv (f x • HolomorphicForms.differential U 0 ((functionsEquiv U).symm g) x +
        g x • HolomorphicForms.differential U 0 ((functionsEquiv U).symm f) x)
    rw [map_add, map_smul, map_smul]
    change oneFormsEquiv U (HolomorphicForms.differential U 0 ((functionsEquiv U).symm (f * g))) x =
      f x • oneFormsEquiv U (HolomorphicForms.differential U 0 ((functionsEquiv U).symm g)) x +
        g x • oneFormsEquiv U (HolomorphicForms.differential U 0 ((functionsEquiv U).symm f)) x
    rw [oneFormsEquiv_differential, oneFormsEquiv_differential, oneFormsEquiv_differential]
    have he : extend (f * g) = extend f * extend g := by
      classical
      funext y
      by_cases hy : y ∈ U <;> simp [extend, hy]
    rw [he, fderiv_mul (contDiffAt_extend f x |>.differentiableAt (by simp))
      (contDiffAt_extend g x |>.differentiableAt (by simp))]
    rw [extend_of_mem f x, extend_of_mem g x]

/-- The existing Kähler universal property, with the actual complex derivative as input. -/
def kaehlerRealization (U : Opens E) : Ω[Functions U⁄ℂ] →ₗ[Functions U] Sections U 1 :=
  (holomorphicDerivation U).liftKaehlerDifferential

theorem kaehlerRealization_D (U : Opens E) (f : Functions U) :
    kaehlerRealization U (D ℂ (Functions U) f) =
      HolomorphicForms.differential U 0 ((functionsEquiv U).symm f) :=
  (holomorphicDerivation U).liftKaehlerDifferential_comp_D f

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Pullback along an actual holomorphic algebra map, followed by the original Kähler lift. -/
def algebraicOneFormsMap (U : Opens E) (φ : A →ₐ[ℂ] Functions U) :
    Ω[A⁄ℂ] →ₗ[ℂ] Sections U 1 :=
  ((kaehlerRealization U).restrictScalars ℂ).comp (AlgebraDeRham.kaehlerMap ℂ φ)

theorem algebraicOneFormsMap_D (U : Opens E) (φ : A →ₐ[ℂ] Functions U) (a : A) :
    algebraicOneFormsMap U φ (D ℂ A a) =
      HolomorphicForms.differential U 0 ((functionsEquiv U).symm (φ a)) := by
  change kaehlerRealization U (AlgebraDeRham.kaehlerMap ℂ φ (D ℂ A a)) = _
  rw [AlgebraDeRham.kaehlerMap_D, kaehlerRealization_D]

/-- The actual polynomial evaluation map on a complex-line coordinate open. -/
def polynomialEvaluation (U : Opens ℂ) : ℂ[X] →ₐ[ℂ] Functions U :=
  Polynomial.aeval (⟨Subtype.val, contMDiff_subtype_val⟩ : Functions U)

theorem polynomialEvaluation_apply (U : Opens ℂ) (p : ℂ[X]) (x : U) :
    polynomialEvaluation U p x = Polynomial.aeval (x : ℂ) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, ContMDiffMap.coe_add, Pi.add_apply] using congrArg₂ (· + ·) hp hq
  | monomial n c =>
    have hc : ((algebraMap ℂ (Functions U)) c) x = c := rfl
    simp [polynomialEvaluation, Polynomial.aeval_monomial, ContMDiffMap.coe_pow, hc]

end HodgeConjecture.HolomorphicDeRham
