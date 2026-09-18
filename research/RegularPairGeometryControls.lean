import HodgeConjecture.Boundary.Normalization.RegularPairBoundary
import Mathlib.RingTheory.Polynomial.Basic
import Lean.Util.CollectAxioms

/-!
# Research controls for choosing fixed--moving regular pairs

Run with `lake env lean research/RegularPairGeometryControls.lean`.

These algebraic controls distinguish existence of a regular pair from a
successful choice of its first element. In the plane, the coordinate pair
works, whereas multiplying the first coordinate by the second makes every
element of the moving principal ideal fail quotient regularity. They do not
construct a `NormalizedCover`, a group action, or actual boundary ideals.

This file is research-only and is not exported by the production spine.
Every named diagnostic theorem has an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.Research.RegularPairGeometryControls

open HodgeConjecture.NormalizationInertia Polynomial

section Algebra

variable {T : Type*} [CommRing T]

/-- An element nilpotent modulo a proper ideal cannot be regular there. -/
theorem not_regular_of_mem_radical (J : Ideal T) (hJ : J ≠ ⊤)
    (g : T) (hg : g ∈ J.radical) : ¬ IsSMulRegular (T ⧸ J) g := by
  intro hRegular
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hg
  have hOne : (1 : T) ∈ J :=
    mem_of_isSMulRegular_quotient_of_smul_mem (hRegular.pow n)
      (by simpa only [smul_eq_mul, mul_one] using hn)
  exact hJ (Ideal.eq_top_of_isUnit_mem J hOne isUnit_one)

/-- If `f = a*b`, every multiple of the nonunit factor `b` kills the
nonzero class of `a` modulo `f`. -/
theorem not_regular_of_mem_factor [IsDomain T]
    (a b : T) (ha : a ≠ 0) (hb : ¬ IsUnit b)
    (g : T) (hg : g ∈ Ideal.span {b}) :
    ¬ IsSMulRegular (T ⧸ Ideal.span {a * b}) g := by
  intro hRegular
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg
  have haMem : a ∈ Ideal.span {a * b} :=
    mem_of_isSMulRegular_quotient_of_smul_mem hRegular (by
      rw [smul_eq_mul, Ideal.mem_span_singleton]
      exact ⟨c, by ring⟩)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp haMem
  apply hb
  apply isUnit_of_mul_eq_one b d
  apply (mul_left_cancel₀ ha)
  simpa only [mul_assoc, mul_one] using hd.symm

/-- Constant coefficients cancel modulo the polynomial coordinate. -/
theorem constant_regular_mod_X [IsDomain T] (r : T) (hr : r ≠ 0) :
    IsSMulRegular (T[X] ⧸ Ideal.span {(X : T[X])}) (C r) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro q hq
  simp only [smul_eq_mul, Ideal.mem_span_singleton, X_dvd_iff,
    coeff_C_mul] at hq ⊢
  exact (mul_eq_zero.mp hq).resolve_left hr

end Algebra

section Plane

-- The outer variable is x; the constant polynomial in the inner variable is y.
local notation "P" => ℚ[X][X]
local notation "x" => (X : P)
local notation "y" => C (X : ℚ[X])

/-- The two coordinate directions give a genuine regular pair. -/
theorem coordinate_pair_regular :
    IsSMulRegular (P ⧸ Ideal.span {x}) y :=
  constant_regular_mod_X (X : ℚ[X]) X_ne_zero

/-- The existing production criterion excludes height-one containment
for the sum of the two coordinate ideals. -/
theorem coordinate_sum_not_le_heightOne (p : PrimeSpectrum P)
    (hp : p.asIdeal.primeHeight = 1) :
    ¬ Ideal.span {x} + Ideal.span {y} ≤ p.asIdeal := by
  apply not_le_heightOne_of_regularPair _ x y
    (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
    X_ne_zero coordinate_pair_regular p hp

/-- The positive control is a proper ideal, so its height-one exclusion
does not come merely from using the unit ideal. -/
theorem coordinate_sum_ne_top :
    (Ideal.span {x} + Ideal.span {y} : Ideal P) ≠ ⊤ := by
  let e : P →+* ℚ := constantCoeff.comp constantCoeff
  have hle : Ideal.span {x} + Ideal.span {y} ≤ RingHom.ker e := by
    rw [Submodule.add_eq_sup, sup_le_iff]
    constructor <;> rw [Ideal.span_le, Set.singleton_subset_iff] <;>
      simp [RingHom.mem_ker, e]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top e) hle

/-- Multiplying the chosen fixed coordinate by the moving coordinate
preserves membership in the fixed ideal. -/
theorem product_choice_mem_fixed : x * y ∈ Ideal.span {x} := by
  rw [Ideal.mem_span_singleton]
  exact ⟨y, rfl⟩

/-- That permitted first-element choice destroys quotient regularity
for every element of the moving ideal, not just for its generator. -/
theorem product_choice_no_regular_moving (g : P)
    (hg : g ∈ Ideal.span {y}) :
    ¬ IsSMulRegular (P ⧸ Ideal.span {x * y}) g := by
  exact not_regular_of_mem_factor x y X_ne_zero
    (fun h => not_isUnit_X (isUnit_C.mp h)) g hg

end Plane

end HodgeConjecture.Research.RegularPairGeometryControls

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.Research.RegularPairGeometryControls.not_regular_of_mem_radical,
      `HodgeConjecture.Research.RegularPairGeometryControls.not_regular_of_mem_factor,
      `HodgeConjecture.Research.RegularPairGeometryControls.constant_regular_mod_X,
      `HodgeConjecture.Research.RegularPairGeometryControls.coordinate_pair_regular,
      `HodgeConjecture.Research.RegularPairGeometryControls.coordinate_sum_not_le_heightOne,
      `HodgeConjecture.Research.RegularPairGeometryControls.coordinate_sum_ne_top,
      `HodgeConjecture.Research.RegularPairGeometryControls.product_choice_mem_fixed,
      `HodgeConjecture.Research.RegularPairGeometryControls.product_choice_no_regular_moving] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
