module

public import HodgeConjecture.Boundary.Normalization.AffineSections

@[expose] public section

/-!
# Constructing actual sections from local fractions

A rational function admitting a local fraction at every point of an open
defines an actual structure-sheaf section. In particular, clearing its
denominator by a power of an ideal gives a section on every open disjoint
from the ideal's zero locus. Both conclusions use the existing section
subalgebra; no additional range or algebra instance is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {T : CommRingCat.{u}} [IsDomain T]
variable {N : Type v} [Field N] [Algebra T N] [IsFractionRing T N]

/-- Local fractions of a rational function glue to an actual section, whose
image belongs to the existing affine section subalgebra. -/
theorem mem_affineSectionSubalgebra_of_localFractions
    (U : (Spec T).Opens) [Nonempty U] (z : N)
    (h : ∀ x : U, ∃ a b : T, b ∉ x.1.asIdeal ∧
      algebraMap T N b * z = algebraMap T N a) :
    z ∈ affineSectionSubalgebra U := by
  classical
  choose a b hb he using h
  have hcross (x y : U) : b y * a x = b x * a y := by
    apply IsFractionRing.injective T N
    simp only [map_mul, ← he]
    ring
  have hlocal (x y : U) :
      IsLocalization.mk' (Localization.AtPrime y.1.asIdeal)
          (a y) (⟨b y, hb y⟩ : y.1.asIdeal.primeCompl) *
        algebraMap T (Localization.AtPrime y.1.asIdeal) (b x) =
      algebraMap T (Localization.AtPrime y.1.asIdeal) (a x) := by
    apply (IsLocalization.map_units (Localization.AtPrime y.1.asIdeal)
      (⟨b y, hb y⟩ : y.1.asIdeal.primeCompl)).mul_right_cancel
    calc
      _ = (IsLocalization.mk' (Localization.AtPrime y.1.asIdeal)
          (a y) (⟨b y, hb y⟩ : y.1.asIdeal.primeCompl) *
          algebraMap T (Localization.AtPrime y.1.asIdeal) (b y)) *
          algebraMap T (Localization.AtPrime y.1.asIdeal) (b x) := by ring
      _ = algebraMap T (Localization.AtPrime y.1.asIdeal) (a y) *
          algebraMap T (Localization.AtPrime y.1.asIdeal) (b x) := by
        rw [IsLocalization.mk'_spec]
      _ = _ := by
        rw [← map_mul, ← map_mul]
        congr 1
        simpa only [mul_comm] using (hcross x y).symm
  let s : Γ(Spec T, U) := ⟨fun x =>
    IsLocalization.mk' (Localization.AtPrime x.1.asIdeal)
      (a x) (⟨b x, hb x⟩ : x.1.asIdeal.primeCompl), fun x => by
      refine ⟨U ⊓ PrimeSpectrum.basicOpen (b x), ⟨x.2, hb x⟩,
        (show U ⊓ PrimeSpectrum.basicOpen (b x) ≤ U from inf_le_left).hom,
        a x, b x, ?_⟩
      intro y
      refine ⟨y.2.2, ?_⟩
      change _ = Localization.mk (a x) (⟨b x, y.2.2⟩ : y.1.asIdeal.primeCompl)
      rw [Localization.mk_eq_mk'_apply]
      exact IsLocalization.eq_mk'_iff_mul_eq.mpr (hlocal x ⟨y.1, y.2.1⟩)⟩
  let x : U := Classical.choice (by assumption)
  have hs : b x • s = algebraMap T Γ(Spec T, U) (a x) := by
    rw [Algebra.smul_def]
    apply Subtype.ext
    funext y
    change algebraMap T (Localization.AtPrime y.1.asIdeal) (b x) *
      IsLocalization.mk' (Localization.AtPrime y.1.asIdeal)
        (a y) (⟨b y, hb y⟩ : y.1.asIdeal.primeCompl) =
      algebraMap T (Localization.AtPrime y.1.asIdeal) (a x)
    simpa only [mul_comm] using hlocal x y
  refine ⟨s, ?_⟩
  have hb0 : algebraMap T N (b x) ≠ 0 := by
    intro h0
    have hb0 : b x = 0 := (IsFractionRing.injective T N) (by simpa using h0)
    exact hb x (hb0 ▸ x.1.asIdeal.zero_mem)
  apply mul_left_cancel₀ hb0
  calc
    algebraMap T N (b x) * affineSectionsToFractionField U s =
        affineSectionsToFractionField U (b x • s) := by
      simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
    _ = algebraMap T N (a x) := by rw [hs]; exact AlgHom.commutes _ _
    _ = algebraMap T N (b x) * z := (he x).symm

/-- An ideal-power denominator condition produces a genuine section on
every open avoiding the ideal's zero locus. -/
theorem mem_affineSectionSubalgebra_of_ideal_pow_mul
    (U : (Spec T).Opens) [Nonempty U] (J : Ideal T) (n : ℕ) (z : N)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (hz : ∀ t ∈ J ^ n, ∃ a : T, algebraMap T N t * z = algebraMap T N a) :
    z ∈ affineSectionSubalgebra U := by
  apply mem_affineSectionSubalgebra_of_localFractions U z
  intro x
  obtain ⟨f, hfJ, hfp⟩ := Set.not_subset.mp (hU x)
  obtain ⟨a, ha⟩ := hz (f ^ n) (Ideal.pow_mem_pow hfJ n)
  exact ⟨a, f ^ n, fun h => hfp (x.1.isPrime.mem_of_pow_mem n h), ha⟩

end

end HodgeConjecture.NormalizationInertia
