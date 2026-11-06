module

public import HodgeConjecture.Cycles.ProjectiveLinePrincipalDegree
public import Mathlib.Algebra.Polynomial.Reverse

@[expose] public section

/-!
# The infinity order through actual coordinate inversion

A rational-function ring endomorphism fixing the constants and inverting
the coordinate takes polynomial degree to minus the order at zero. This
arithmetic identity is the remaining local computation for the actual
projective-line chart transition.

Selected proof adaptation from AxiomMath/Stacks, revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Chow/ProjectiveLineDivisorDegree/Inversion.lean`,
Apache-2.0. See `third_party/axiom-stacks/LICENSE`.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles.ProjectiveLineDegree

open Polynomial UniqueFactorizationMonoid

noncomputable section

universe u

variable {k : Type u} [Field k] [DecidableEq k]

private theorem count_X_normalizedFactors_X_pow (d : ℕ) :
    (normalizedFactors (Polynomial.X ^ d : Polynomial k)).count Polynomial.X = d := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible irreducible_X,
    monic_X.normalize_eq_self, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]

private theorem count_X_normalizedFactors_reverse {a : Polynomial k} (ha : a ≠ 0) :
    (normalizedFactors a.reverse).count Polynomial.X = 0 := by
  refine Multiset.count_eq_zero_of_notMem fun hmem ↦ ?_
  have hdvd : (Polynomial.X : Polynomial k) ∣ a.reverse := dvd_of_mem_normalizedFactors hmem
  rw [Polynomial.X_dvd_iff, coeff_zero_reverse] at hdvd
  exact leadingCoeff_ne_zero.mpr ha hdvd

omit [DecidableEq k] in
private theorem inversion_algebraMap_eq_eval₂ (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    {y : RatFunc k} (hX : tau RatFunc.X = y) (a : Polynomial k) :
    tau (algebraMap (Polynomial k) (RatFunc k) a) =
      Polynomial.eval₂ (algebraMap k (RatFunc k)) y a := by
  have h : tau.comp (algebraMap (Polynomial k) (RatFunc k)) =
      Polynomial.eval₂RingHom (algebraMap k (RatFunc k)) y := by
    refine Polynomial.ringHom_ext (fun x ↦ ?_) ?_
    · simpa [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C] using hconst x
    · simpa [RatFunc.algebraMap_X] using hX
  exact congrArg (fun f : Polynomial k →+* RatFunc k ↦ f a) h

omit [DecidableEq k] in
private theorem eval₂_X_eq_algebraMap (a : Polynomial k) :
    Polynomial.eval₂ (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k) a =
      algebraMap (Polynomial k) (RatFunc k) a :=
  (inversion_algebraMap_eq_eval₂ (RingHom.id _) (fun _ ↦ rfl) rfl a).symm

omit [DecidableEq k] in
private theorem inversion_algebraMap (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹) (a : Polynomial k) :
    tau (algebraMap (Polynomial k) (RatFunc k) a) =
      algebraMap (Polynomial k) (RatFunc k) a.reverse /
        algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ a.natDegree) := by
  have hXinv : (RatFunc.X : RatFunc k)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  let _ : Invertible ((RatFunc.X : RatFunc k)⁻¹) := invertibleOfNonzero hXinv
  have hinvOf : ⅟((RatFunc.X : RatFunc k)⁻¹) = RatFunc.X := by simp
  have key := Polynomial.eval₂_reverse_mul_pow (algebraMap k (RatFunc k))
    ((RatFunc.X : RatFunc k)⁻¹) a
  rw [hinvOf, eval₂_X_eq_algebraMap] at key
  rw [inversion_algebraMap_eq_eval₂ tau hconst hX, ← key, map_pow, RatFunc.algebraMap_X,
    inv_pow, ← div_eq_mul_inv]

private theorem finiteOrder_X_inversion_algebraMap (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹) {a : Polynomial k} (ha : a ≠ 0) :
    finiteOrder (Polynomial.X : Polynomial k) (tau (algebraMap (Polynomial k) (RatFunc k) a)) =
      -(a.natDegree : ℤ) := by
  have hrev : a.reverse ≠ 0 := by simpa [Polynomial.reverse_eq_zero] using ha
  have hpow : (Polynomial.X ^ a.natDegree : Polynomial k) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  rw [inversion_algebraMap tau hconst hX, finiteOrder_div _ hrev hpow,
    count_X_normalizedFactors_reverse ha, count_X_normalizedFactors_X_pow]
  simp

/-- Reading a nonzero rational function in the inverse coordinate computes its infinity order. -/
theorem finiteOrder_X_inversion (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹)
    (g : RatFunc k) (hg : g ≠ 0) :
    finiteOrder (Polynomial.X : Polynomial k) (tau g) = -g.intDegree := by
  have hnum := RatFunc.num_ne_zero hg
  have hden := RatFunc.denom_ne_zero g
  have hne : ∀ a : Polynomial k, a ≠ 0 → tau (algebraMap (Polynomial k) (RatFunc k) a) ≠ 0 :=
    fun a ha ↦ (map_ne_zero_iff _ tau.injective).mpr
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr ha)
  have htaunum := hne _ hnum
  have htauden := hne _ hden
  have hsplit : tau g = tau (algebraMap (Polynomial k) (RatFunc k) g.num) *
      (tau (algebraMap (Polynomial k) (RatFunc k) g.denom))⁻¹ := by
    rw [← map_inv₀, ← map_mul, ← div_eq_mul_inv, RatFunc.num_div_denom]
  have hinvden : finiteOrder (Polynomial.X : Polynomial k)
      ((tau (algebraMap (Polynomial k) (RatFunc k) g.denom))⁻¹) =
        -finiteOrder (Polynomial.X : Polynomial k)
          (tau (algebraMap (Polynomial k) (RatFunc k) g.denom)) := by
    have h := finiteOrder_mul (Polynomial.X : Polynomial k) (inv_ne_zero htauden) htauden
    rw [inv_mul_cancel₀ htauden, finiteOrder_one] at h
    omega
  rw [hsplit, finiteOrder_mul _ htaunum (inv_ne_zero htauden), hinvden,
    finiteOrder_X_inversion_algebraMap tau hconst hX hnum,
    finiteOrder_X_inversion_algebraMap tau hconst hX hden, RatFunc.intDegree]
  omega

end

end HodgeConjecture.SchemeCycles.ProjectiveLineDegree
