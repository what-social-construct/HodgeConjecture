module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineCech
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

/-!
# The ordinary Čech first Chern class on the projective-line cover

A line-bundle transition unit on the actual Laurent overlap maps to the
total degree-two class of its logarithmic differential. Changing either
chart trivialization contributes an actual total boundary, so the map
descends to the Čech Picard quotient of transition units. Laurent residue
detects the coordinate transition with value one.

This is the ordinary first-Chern construction on this explicit cover.
The source is the stated Čech transition quotient. A separate ordinary
Chow-source map is constructed in ProjectiveLineCycleClass using the
actual principal-divisor degree theorem. Identifications of these entire
source groups and of the target with scheme or Betti cohomology remain separate.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineDeRham

open KaehlerDifferential AffineDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- The actual map on units, written additively for transition cocycles. -/
def chartUnitMap (f : Polynomial k →ₐ[k] LaurentPolynomial k) :
    Additive (Polynomial k)ˣ →+ Additive (LaurentPolynomial k)ˣ where
  toFun u := Additive.ofMul (Units.map f.toMonoidHom u.toMul)
  map_zero' := by change Units.map f.toMonoidHom 1 = 1; exact map_one _
  map_add' u v := by
    change Units.map f.toMonoidHom (u.toMul * v.toMul) =
      Units.map f.toMonoidHom u.toMul * Units.map f.toMonoidHom v.toMul
    exact map_mul _ _ _

/-- Changing the two local trivializations changes the transition by their ratio. -/
def chartCoboundary : Additive (Polynomial k)ˣ × Additive (Polynomial k)ˣ →+
    Additive (LaurentPolynomial k)ˣ :=
  (chartUnitMap k (chartInfinityRingMap k)).comp (AddMonoidHom.snd _ _) -
    (chartUnitMap k (chartZeroRingMap k)).comp (AddMonoidHom.fst _ _)

/-- The Čech Picard group of transition units for the actual two-chart cover. -/
abbrev TransitionPicard := Additive (LaurentPolynomial k)ˣ ⧸ (chartCoboundary k).range

/-- Passage from an actual transition unit to its class modulo changes of trivializations. -/
def transitionClass : Additive (LaurentPolynomial k)ˣ →+ TransitionPicard k :=
  QuotientAddGroup.mk' (chartCoboundary k).range

/-- The logarithmic construction, before passing to transition classes. -/
def firstChernTransition : Additive (LaurentPolynomial k)ˣ →+ CechH2 k where
  toFun u := cechClass k (closedLogarithmicForm k (LaurentPolynomial k) u.toMul)
  map_zero' := by rw [show (0 : Additive (LaurentPolynomial k)ˣ).toMul = 1 from rfl]; simp
  map_add' u v := by
    change cechClass k (closedLogarithmicForm k (LaurentPolynomial k) (u.toMul * v.toMul)) = _
    rw [closedLogarithmicForm_mul, map_add]

/-- The restriction of a chart logarithmic form is the original logarithmic form of its unit image. -/
theorem logarithmicForm_chartUnitMap (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (u : (Polynomial k)ˣ) :
    logarithmicForm k (LaurentPolynomial k) (Units.map f.toMonoidHom u) =
      (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (polynomialKaehlerPullback k f (logarithmicDifferential k (Polynomial k) u)) := by
  apply (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).injective
  rw [oneEquiv_logarithmicForm, LinearEquiv.apply_symm_apply]
  change f ((u⁻¹ : (Polynomial k)ˣ) : Polynomial k) •
    D k (LaurentPolynomial k) (f (u : Polynomial k)) =
      polynomialKaehlerPullback k f
        (((u⁻¹ : (Polynomial k)ˣ) : Polynomial k) • D k (Polynomial k) (u : Polynomial k))
  rw [polynomialKaehlerPullback_smul, polynomialKaehlerPullback_D]

/-- A change of trivialization on the zero chart is an actual total boundary. -/
@[simp]
theorem firstChernTransition_chartZero (u : Additive (Polynomial k)ˣ) :
    firstChernTransition k (chartUnitMap k (chartZeroRingMap k) u) = 0 := by
  apply (cechClass_eq_zero_iff k _).mpr
  refine ⟨(-logarithmicDifferential k (Polynomial k) u.toMul, 0, 0), ?_⟩
  change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
    (chartInfinityFormsMap k 0 -
      chartZeroFormsMap k (-logarithmicDifferential k (Polynomial k) u.toMul) -
        D k (LaurentPolynomial k) 0) =
      logarithmicForm k (LaurentPolynomial k)
        (Units.map (chartZeroRingMap k).toMonoidHom u.toMul)
  rw [logarithmicForm_chartUnitMap, map_zero, map_neg, map_zero, zero_sub, neg_neg, sub_zero]
  rfl

/-- A change of trivialization on the infinity chart is likewise an actual total boundary. -/
@[simp]
theorem firstChernTransition_chartInfinity (u : Additive (Polynomial k)ˣ) :
    firstChernTransition k (chartUnitMap k (chartInfinityRingMap k) u) = 0 := by
  apply (cechClass_eq_zero_iff k _).mpr
  refine ⟨(0, logarithmicDifferential k (Polynomial k) u.toMul, 0), ?_⟩
  change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
    (chartInfinityFormsMap k (logarithmicDifferential k (Polynomial k) u.toMul) -
      chartZeroFormsMap k 0 - D k (LaurentPolynomial k) 0) =
      logarithmicForm k (LaurentPolynomial k)
        (Units.map (chartInfinityRingMap k).toMonoidHom u.toMul)
  rw [logarithmicForm_chartUnitMap, map_zero, map_zero, sub_zero, sub_zero]
  rfl

/-- Every Čech coboundary vanishes under the constructed first-Chern formula. -/
theorem chartCoboundary_le_ker_firstChernTransition :
    (chartCoboundary k).range ≤ (firstChernTransition k).ker := by
  rintro _ ⟨u, rfl⟩
  change firstChernTransition k
    (chartUnitMap k (chartInfinityRingMap k) u.2 -
      chartUnitMap k (chartZeroRingMap k) u.1) = 0
  rw [map_sub, firstChernTransition_chartInfinity, firstChernTransition_chartZero, sub_self]

/-- The ordinary Čech first Chern class, well defined modulo both actual chart trivializations. -/
def firstChern : TransitionPicard k →+ CechH2 k :=
  QuotientAddGroup.lift (chartCoboundary k).range (firstChernTransition k)
    (chartCoboundary_le_ker_firstChernTransition k)

@[simp]
theorem firstChern_transitionClass (u : Additive (LaurentPolynomial k)ˣ) :
    firstChern k (transitionClass k u) = firstChernTransition k u := rfl

/-- Changing local trivializations leaves the actual first-Chern class unchanged. -/
theorem firstChernTransition_changeTrivialization (t : Additive (LaurentPolynomial k)ˣ)
    (u : Additive (Polynomial k)ˣ × Additive (Polynomial k)ˣ) :
    firstChernTransition k (t + chartCoboundary k u) = firstChernTransition k t := by
  rw [map_add, show firstChernTransition k (chartCoboundary k u) = 0 from
    chartCoboundary_le_ker_firstChernTransition k ⟨u, rfl⟩, add_zero]

/-- The distinguished total degree-two class from the coordinate transition unit. -/
def chernCoordinate : CechH2 k :=
  firstChernTransition k (Additive.ofMul (LaurentDeRham.variableUnit k))

/-- Its normalization is computed by the actual Laurent residue on forms. -/
@[simp]
theorem cechResidue_chernCoordinate : cechResidue k (chernCoordinate k) = 1 := by
  change LaurentDeRham.closedFormResidue k
    (closedLogarithmicForm k (LaurentPolynomial k) (LaurentDeRham.variableUnit k)) = 1
  exact LaurentDeRham.cohomologyResidue_coordinateClass k

theorem chernCoordinate_ne_zero [Nontrivial k] : chernCoordinate k ≠ 0 := by
  intro h
  have hres := congrArg (cechResidue k) h
  rw [cechResidue_chernCoordinate, map_zero] at hres
  exact one_ne_zero hres

/-- The constructed ordinary Čech first-Chern map is nonzero. -/
theorem firstChern_ne_zero [Nontrivial k] : firstChern k ≠ 0 := by
  intro h
  have hu := DFunLike.congr_fun h
    (transitionClass k (Additive.ofMul (LaurentDeRham.variableUnit k)))
  exact chernCoordinate_ne_zero k hu

/-- Tensor powers of the coordinate transition have the expected integral Chern class. -/
theorem firstChernTransition_coordinate_zpow (n : ℤ) :
    firstChernTransition k (Additive.ofMul (LaurentDeRham.variableUnit k ^ n)) =
      n • chernCoordinate k :=
  (firstChernTransition k).map_zsmul n (Additive.ofMul (LaurentDeRham.variableUnit k))

/-- A split copy of the coefficient ring in total degree two. -/
def chernCoordinateLinearMap : k →ₗ[k] CechH2 k :=
  LinearMap.toSpanSingleton k _ (chernCoordinate k)

@[simp]
theorem cechResidue_chernCoordinateLinearMap (a : k) :
    cechResidue k (chernCoordinateLinearMap k a) = a := by
  change cechResidue k (a • chernCoordinate k) = a
  rw [map_smul, cechResidue_chernCoordinate, smul_eq_mul, mul_one]

theorem chernCoordinateLinearMap_injective : Function.Injective (chernCoordinateLinearMap k) := by
  intro a b h
  simpa only [cechResidue_chernCoordinateLinearMap] using congrArg (cechResidue k) h

end

end HodgeConjecture.ProjectiveLineDeRham
