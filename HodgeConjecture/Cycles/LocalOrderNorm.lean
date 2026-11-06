module

public import HodgeConjecture.Cycles.LocalOrderDeterminant
public import HodgeConjecture.CommutativeAlgebra.SemilocalLength
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

/-!
# Norms and actual quotient lengths

Specialize the proved determinant comparison to multiplication in a finite
extension of fraction fields. The image of the finite algebra is proved to
be a lattice; finite dimensionality of the fraction extension is derived.
Thus the order of a norm is the base-ring length of the actual principal
quotient, without freeness, normality or separability assumptions.

The final theorem combines this with the semilocal residue-degree sum.
Its summands are localizations of the actual principal quotient. Their
identification with local orders is proved in `Cycles/LocalOrderLocalization.lean`.
`Cycles/LocalOrderNormFormula.lean` derives the semilocal hypotheses and
assembles the formula for arbitrary nonzero fractions. Transport to scheme
divisors remains the next step. The sources are Stacks Tags
02MJ (https://stacks.math.columbia.edu/tag/02MJ) and
02RT (https://stacks.math.columbia.edu/tag/02RT).
-/

set_option autoImplicit false
namespace HodgeConjecture.SchemeCycles

noncomputable section

open HodgeConjecture.CommutativeAlgebra

variable (R K L : Type*) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- The determinant comparison for multiplication by a nonzero field element. -/
theorem latticeIndex_eq_localOrder_norm [FiniteDimensional K L]
    (M : Submodule R L) [Submodule.IsLattice K M] (y : Lˣ) :
    latticeIndex M (M.map ((Algebra.lmul K L (y : L)).restrictScalars R)) =
      localOrder R (Units.map (Algebra.norm K) y) := by
  let e := (LinearEquiv.smulOfUnit (M := L) y).restrictScalars K
  have he : e.toLinearMap = Algebra.lmul K L (y : L) := rfl
  have hdet : LinearEquiv.det e = Units.map (Algebra.norm K) y := by
    apply Units.ext
    simp only [LinearEquiv.coe_det, he, Units.coe_map, Algebra.norm_apply]
  rw [← he, ← hdet]
  exact latticeIndex_eq_localOrder_det R K L M e

variable (B : Type*) [CommRing B] [IsDomain B] [Algebra R B]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L] [Module.Finite R B]

private def finiteAlgebraLattice : Submodule R L :=
  LinearMap.range ((Algebra.linearMap B L).restrictScalars R)

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
private theorem finiteAlgebraLattice_isLattice : Submodule.IsLattice K (finiteAlgebraLattice R L B) where
  fg := by
    rw [finiteAlgebraLattice, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := B)).map _
  span_eq_top := by
    change Submodule.span K (Set.range (algebraMap B L)) = ⊤
    have hinj : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    have h := IsFractionRing.ideal_span_singleton_map_subset (R := R) (S := B) (K := K)
      (L := L) (a := 1) (b := Set.univ) hinj (by simp)
    apply SetLike.coe_injective
    simpa using h

include R B in
omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
private theorem finiteAlgebraLattice_finiteDimensional : FiniteDimensional K L := by
  let M := finiteAlgebraLattice R L B
  letI := finiteAlgebraLattice_isLattice R K L B
  letI := lattice_isLocalizedModule R K L M Submodule.IsLattice.span_eq_top
  exact Module.Finite.of_isLocalizedModule (Rₚ := K) (nonZeroDivisors R) M.subtype

omit [IsDomain R] [IsFractionRing R K] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDomain B] [IsFractionRing B L] [Module.Finite R B] in
private theorem finiteAlgebraLattice_mul_image (b : B) :
    (finiteAlgebraLattice R L B).map
      ((Algebra.lmul K L (algebraMap B L b)).restrictScalars R) =
    ((Ideal.span {b}).restrictScalars R).map ((Algebra.linearMap B L).restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨b * z, Ideal.mem_span_singleton.mpr ⟨z, rfl⟩, ?_⟩
    exact map_mul (algebraMap B L) b z
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨algebraMap B L w, ⟨w, rfl⟩, ?_⟩
    exact (map_mul (algebraMap B L) b w).symm

/-- The order of the actual field norm equals the base length of the actual principal quotient. -/
theorem localOrder_norm_algebraMap_eq_length (b : B) (hb : b ≠ 0) :
    localOrder R (Units.map (Algebra.norm K)
      (Units.mk0 (algebraMap B L b)
        ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb))) =
      ((Module.length R (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  letI := finiteAlgebraLattice_isLattice R K L B
  letI := finiteAlgebraLattice_finiteDimensional R K L B
  rw [← latticeIndex_eq_localOrder_norm R K L (finiteAlgebraLattice R L B),
    Units.val_mk0, finiteAlgebraLattice_mul_image]
  rw [finiteAlgebraLattice, latticeIndex_of_le _ _ (LinearMap.map_le_range),
    submoduleQuotientLength_range _ (IsFractionRing.injective B L)]
  rfl

include K L in
/-- The principal quotient has finite base length, derived without assuming the algebra is free. -/
theorem principalQuotient_restrictScalars_length_ne_top (b : B) (hb : b ≠ 0) :
    Module.length R (B ⧸ Ideal.span {b}) ≠ ⊤ := by
  let M := finiteAlgebraLattice R L B
  let y := Units.mk0 (algebraMap B L b)
    ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb)
  let e := (LinearEquiv.smulOfUnit (M := L) y).restrictScalars K
  letI := finiteAlgebraLattice_isLattice R K L B
  letI := lattice_map_isLattice R K L e M
  have h := Module.length_ne_top_iff.mpr (lattice_quotient_finiteLength R K L
    (M.map (e.restrictScalars R).toLinearMap) M Submodule.IsLattice.fg)
  change submoduleQuotientLength M
    (M.map ((Algebra.lmul K L (algebraMap B L b)).restrictScalars R)) ≠ ⊤ at h
  dsimp only [M] at h
  rw [finiteAlgebraLattice_mul_image, finiteAlgebraLattice,
    submoduleQuotientLength_range _ (IsFractionRing.injective B L)] at h
  exact h

/-- For a fraction, the norm order is the signed difference of the two actual quotient lengths. -/
theorem localOrder_norm_fraction_eq_length (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    localOrder R (Units.map (Algebra.norm K)
      (Units.mk0 (algebraMap B L a)
          ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr ha) /
        Units.mk0 (algebraMap B L b)
          ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb))) =
      ((Module.length R (B ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length R (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  rw [map_div, localOrder_div, localOrder_norm_algebraMap_eq_length R K L B a ha,
    localOrder_norm_algebraMap_eq_length R K L B b hb]

variable [IsLocalRing R] [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R)]
  [∀ q : MaximalSpectrum B, Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q.asIdeal)]

/-- The norm order as a residue-degree-weighted sum of localized principal-quotient lengths. -/
theorem localOrder_norm_algebraMap_eq_sum_localized_length (b : B) (hb : b ≠ 0) :
    localOrder R (Units.map (Algebra.norm K)
      (Units.mk0 (algebraMap B L b)
        ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb))) =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q.asIdeal) : ℤ) *
          ((Module.length (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).toNat : ℤ) := by
  have hR := Module.length_ne_top_iff.mp
    (principalQuotient_restrictScalars_length_ne_top R K L B b hb)
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hR
  have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower R hN, isArtinian_of_tower R hA⟩
  rw [localOrder_norm_algebraMap_eq_length R K L B b hb]
  exact length_restrictScalars_toNat_eq_sum_residueDegree B R _ hB

end

end HodgeConjecture.SchemeCycles
