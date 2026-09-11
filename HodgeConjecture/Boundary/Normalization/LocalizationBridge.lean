import HodgeConjecture.Boundary.Normalization.PrimeInertia
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Localizing a normalization at a valuation center

The normalization diagram currently remembers an embedding of its
normalization ring into a discrete valuation ring and the contraction of the
maximal ideal.  For comparison with ring-theoretic prime inertia, one needs
the stronger statement that this valuation ring is the localization of the
normalization ring at the selected prime.

This module packages that commutative-algebra datum.  It is deliberately
separate from `ValuationCenteredAt`: centeredness follows from localization,
whereas the converse is false without additional hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u

namespace NormalizationInertia

open scoped Pointwise

section StablePrime

variable {S G : Type*}
variable [CommRing S] [Group G] [MulSemiringAction G S]

/-- An automorphism stabilizing a prime also stabilizes its multiplicative
complement.  This is the denominator comparison needed to extend the
automorphism to the localization. -/
theorem primeCompl_map_eq_of_smul_eq
    (Q : Ideal S) [Q.IsPrime] (g : G) (hQ : g • Q = Q) :
    Q.primeCompl.map
        (MulSemiringAction.toRingAut G S g).toMonoidHom =
      Q.primeCompl := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g • y ∉ Q
    intro hgy
    apply hy
    apply (Ideal.smul_mem_pointwise_smul_iff
      (a := g) (S := Q) (x := y)).mp
    rw [hQ]
    exact hgy
  · intro hx
    refine ⟨g⁻¹ • x, ?_, ?_⟩
    · change g⁻¹ • x ∉ Q
      intro hginv
      apply hx
      have hmem := Ideal.smul_mem_pointwise_smul g (g⁻¹ • x) Q hginv
      simpa [hQ] using hmem
    · change g • (g⁻¹ • x) = x
      simp

end StablePrime

section LocalizationData

variable {B K N : Type u}
variable [CommRing B] [Field K] [Field N]
variable [Algebra B K] [Algebra K N] [Algebra B N]
variable [IsScalarTower B K N]

/-- A centered valuation ring together with the stronger assertion that it
is the localization of the normal-closure normalization at the selected
prime.  The compatibility field fixes the embedding into the common fraction
field `N`; an abstract localization equivalence alone would not identify the
two Galois actions used by the project. -/
structure ValuationLocalizationAt
    (V : CollisionFoundations.DiscreteValuationTower K (N := N))
    (q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))) where
  centerMap :
    NormalClosureNormalizationRing (B := B) (N := N) →+*
      V.valuationRing
  centerMap_coe :
    ∀ x,
      ((centerMap x : V.valuationRing) : N) = (x : N)
  isLocalization :
    letI : Algebra
        (NormalClosureNormalizationRing (B := B) (N := N))
        V.valuationRing := centerMap.toAlgebra
    IsLocalization.AtPrime V.valuationRing q.asIdeal

/-- The proposition that compatible localization data exist.  Keeping this
as the `Nonempty` wrapper around `ValuationLocalizationAt` lets proofs use
the data while allowing centeredness, itself a proposition, to imply the
existence statement. -/
def HasValuationLocalizationAt
    (V : CollisionFoundations.DiscreteValuationTower K (N := N))
    (q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))) : Prop :=
  Nonempty (ValuationLocalizationAt (B := B) V q)

omit [Algebra B K] [IsScalarTower B K N] in
/-- Localization at the selected prime implies the weaker centeredness datum
used by `Diagram`. -/
theorem ValuationLocalizationAt.toValuationCenteredAt
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q) :
    ValuationCenteredAt (B := B) V q := by
  letI : Algebra
      (NormalClosureNormalizationRing (B := B) (N := N))
      V.valuationRing := h.centerMap.toAlgebra
  letI : IsLocalization.AtPrime V.valuationRing q.asIdeal :=
    h.isLocalization
  refine ⟨h.centerMap, h.centerMap_coe, ?_⟩
  exact IsLocalization.AtPrime.comap_maximalIdeal
    V.valuationRing q.asIdeal

namespace ValuationLocalizationAt

/-- A Galois automorphism stabilizing the center prime extends uniquely to
an automorphism of the localized valuation ring. -/
noncomputable def localRingEquivOfPrimeStabilizer
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    (σ : N ≃ₐ[K] N) (hσ : σ • q.asIdeal = q.asIdeal) :
    V.valuationRing ≃+* V.valuationRing := by
  letI : Algebra
      (NormalClosureNormalizationRing (B := B) (N := N))
      V.valuationRing := h.centerMap.toAlgebra
  letI : IsLocalization.AtPrime V.valuationRing q.asIdeal :=
    h.isLocalization
  exact
    IsLocalization.ringEquivOfRingEquiv
      V.valuationRing V.valuationRing
      (MulSemiringAction.toRingAut
        (N ≃ₐ[K] N)
        (NormalClosureNormalizationRing (B := B) (N := N)) σ)
      (primeCompl_map_eq_of_smul_eq q.asIdeal σ hσ)

/-- On elements of the normalization ring, the localized automorphism is
the original Galois action. -/
theorem localRingEquivOfPrimeStabilizer_centerMap
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    (σ : N ≃ₐ[K] N) (hσ : σ • q.asIdeal = q.asIdeal)
    (x : NormalClosureNormalizationRing (B := B) (N := N)) :
    h.localRingEquivOfPrimeStabilizer σ hσ (h.centerMap x) =
      h.centerMap (σ • x) := by
  letI : Algebra
      (NormalClosureNormalizationRing (B := B) (N := N))
      V.valuationRing := h.centerMap.toAlgebra
  letI : IsLocalization.AtPrime V.valuationRing q.asIdeal :=
    h.isLocalization
  exact
    IsLocalization.ringEquivOfRingEquiv_eq
      (primeCompl_map_eq_of_smul_eq q.asIdeal σ hσ) x

/-- The localized automorphism agrees, inside the common field `N`, with the
original Galois automorphism.  The compatibility with `N` is why
`centerMap_coe` is part of `ValuationLocalizationAt`. -/
theorem localRingEquivOfPrimeStabilizer_coe
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    (σ : N ≃ₐ[K] N) (hσ : σ • q.asIdeal = q.asIdeal)
    (x : V.valuationRing) :
    ((h.localRingEquivOfPrimeStabilizer σ hσ x :
        V.valuationRing) : N) =
      σ (x : N) := by
  letI : Algebra
      (NormalClosureNormalizationRing (B := B) (N := N))
      V.valuationRing := h.centerMap.toAlgebra
  letI : IsLocalization.AtPrime V.valuationRing q.asIdeal :=
    h.isLocalization
  let e := h.localRingEquivOfPrimeStabilizer σ hσ
  have heq :
      V.valuationRing.toSubring.subtype.comp e.toRingHom =
        σ.toRingEquiv.toRingHom.comp
          V.valuationRing.toSubring.subtype := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext a
    change
      ((e (h.centerMap a) : V.valuationRing) : N) =
        σ ((h.centerMap a : V.valuationRing) : N)
    rw [localRingEquivOfPrimeStabilizer_centerMap,
      h.centerMap_coe, h.centerMap_coe]
    rfl
  exact DFunLike.congr_fun heq x

/-- A prime-stabilizing Galois automorphism carries every element of the
localized valuation ring back into that valuation ring. -/
theorem smul_mem_valuationRing_of_prime_stable
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    (σ : N ≃ₐ[K] N) (hσ : σ • q.asIdeal = q.asIdeal)
    {x : N} (hx : x ∈ V.valuationRing) :
    σ x ∈ V.valuationRing := by
  let xV : V.valuationRing := ⟨x, hx⟩
  let yV := h.localRingEquivOfPrimeStabilizer σ hσ xV
  have hy : ((yV : V.valuationRing) : N) ∈ V.valuationRing := yV.property
  rw [h.localRingEquivOfPrimeStabilizer_coe σ hσ xV] at hy
  exact hy

/-- Under the localization realization, an automorphism stabilizing the
center prime also stabilizes the valuation subring inside `N`. -/
theorem smul_valuationRing_eq_of_prime_stable
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    (σ : N ≃ₐ[K] N) (hσ : σ • q.asIdeal = q.asIdeal) :
    σ • V.valuationRing = V.valuationRing := by
  have hσinv : σ⁻¹ • q.asIdeal = q.asIdeal := by
    calc
      σ⁻¹ • q.asIdeal = σ⁻¹ • (σ • q.asIdeal) := by rw [hσ]
      _ = q.asIdeal := inv_smul_smul σ q.asIdeal
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    have hmem := h.smul_mem_valuationRing_of_prime_stable σ hσ hx
    have heq : σ (σ⁻¹ • x) = x := by
      change σ (σ.symm x) = x
      exact σ.apply_symm_apply x
    rw [heq] at hmem
    exact hmem
  · exact h.smul_mem_valuationRing_of_prime_stable σ⁻¹ hσinv

/-- Prime inertia acts trivially on the residue field of the localized
valuation ring. -/
theorem residue_localRingEquivOfPrimeInertia
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q)
    {σ : N ≃ₐ[K] N}
    (hσ : σ ∈ normalizationPrimeInertiaGroup
      (B := B) (K := K) q.asIdeal)
    (v : V.valuationRing) :
    IsLocalRing.residue V.valuationRing
        (h.localRingEquivOfPrimeStabilizer σ
          ((mem_primeInertiaSubgroup_iff
            (A := FullInvariantNormalizationRing
              (B := B) (K := K) (N := N))
            q.asIdeal σ).mp hσ).1 v) =
      IsLocalRing.residue V.valuationRing v := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  letI : Algebra
      S V.valuationRing := h.centerMap.toAlgebra
  letI : IsLocalization.AtPrime V.valuationRing q.asIdeal :=
    h.isLocalization
  have hprime := (mem_primeInertiaSubgroup_iff
    (A := FullInvariantNormalizationRing
      (B := B) (K := K) (N := N)) q.asIdeal σ).mp hσ
  let e := h.localRingEquivOfPrimeStabilizer σ hprime.1
  have heq :
      (IsLocalRing.residue V.valuationRing).comp e.toRingHom =
        IsLocalRing.residue V.valuationRing := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext x
    change IsLocalRing.residue V.valuationRing (e (h.centerMap x)) =
      IsLocalRing.residue V.valuationRing (h.centerMap x)
    rw [localRingEquivOfPrimeStabilizer_centerMap]
    rw [← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    rw [← map_sub]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      V.valuationRing q.asIdeal _).2 (hprime.2 x)
  exact DFunLike.congr_fun heq v

/-- Identifying the centered valuation ring with the localization at its
center supplies the reverse inclusion from prime inertia to valuation
inertia. -/
theorem primeInertia_le_valuationInertia
    {V : CollisionFoundations.DiscreteValuationTower K (N := N)}
    {q : PrimeSpectrum
      (NormalClosureNormalizationRing (B := B) (N := N))}
    (h : ValuationLocalizationAt (B := B) V q) :
    normalizationPrimeInertiaGroup
        (B := B) (K := K) q.asIdeal ≤
      CollisionFoundations.inertiaGroupAt K V.valuationRing := by
  intro σ hσ
  have hprime := (mem_primeInertiaSubgroup_iff
    (A := FullInvariantNormalizationRing
      (B := B) (K := K) (N := N)) q.asIdeal σ).mp hσ
  let τ : V.valuationRing.decompositionSubgroup K :=
    ⟨σ, h.smul_valuationRing_eq_of_prime_stable σ hprime.1⟩
  rw [CollisionFoundations.inertiaGroupAt, Subgroup.mem_map]
  refine ⟨τ, ?_, rfl⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro y
  obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y
  change τ • IsLocalRing.residue V.valuationRing v =
    IsLocalRing.residue V.valuationRing v
  rw [← IsLocalRing.ResidueField.residue_smul]
  have haction :
      τ • v = h.localRingEquivOfPrimeStabilizer σ hprime.1 v := by
    apply Subtype.ext
    change σ (v : N) =
      ((h.localRingEquivOfPrimeStabilizer σ hprime.1 v :
          V.valuationRing) : N)
    exact
      (h.localRingEquivOfPrimeStabilizer_coe σ hprime.1 v).symm
  rw [haction]
  exact residue_localRingEquivOfPrimeInertia h hσ v

end ValuationLocalizationAt

end LocalizationData

section DiagramBridge

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : AlgebraicGeometry.Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

/-- At a height-one point of the finite normalization over a Noetherian
base, the centered discrete valuation ring is the localization of the
normalization ring at its center.

The proof first shows that the canonical prime localization is a valuation
ring: it is a Noetherian, integrally closed, local domain of dimension at
most one.  The centered map then extends to a local homomorphism from this
localization.  Maximality of valuation subrings in the common fraction field
forces that homomorphism to be an equivalence. -/
theorem hasValuationLocalizationAt_of_isNoetherianRing
    [IsNoetherianRing B]
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    HasValuationLocalizationAt
      (B := B) (D.valuationAt E) E.1 := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let V := (D.valuationAt E).valuationRing
  letI : FiniteDimensional K N := C.normalClosure.finiteNormal
  letI : Module.Finite B S := C.finiteNormalClosureModel
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite B S
  letI : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  letI : IsFractionRing S N :=
    integralClosure.isFractionRing_of_finite_extension K N
  rcases D.valuation_centered E with ⟨centerMap, hcenter, hcomap⟩
  refine ⟨⟨centerMap, hcenter, ?_⟩⟩
  letI : Algebra S V := centerMap.toAlgebra
  let Q := E.1.asIdeal
  let T := Localization.AtPrime Q
  letI : IsNoetherianRing T :=
    IsLocalization.isNoetherianRing Q.primeCompl T inferInstance
  letI : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T Q.primeCompl
      Q.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim T ≤ (1 : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q T,
      Ideal.height_eq_primeHeight, E.2.1]
    exact_mod_cast le_rfl
  letI : Ring.KrullDimLE 1 T := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne T :=
    ⟨fun {P} hP hPrime =>
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (inferInstance : Ring.KrullDimLE 1 T)) P hP hPrime⟩
  have hvalCriterion :
      IsIntegrallyClosed T ∧
        ∀ P : Ideal T, P ≠ ⊥ → P.IsPrime →
          P = IsLocalRing.maximalIdeal T :=
    ⟨inferInstance, fun P hP hPrime =>
      IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hP hPrime)⟩
  letI : ValuationRing T :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain T).out 3 1).mp
      hvalCriterion
  have hdenV : ∀ y : Q.primeCompl, IsUnit (centerMap y) := by
    intro y
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hy
    apply y.property
    have hymem :
        (y : S) ∈
          (IsLocalRing.maximalIdeal V).comap centerMap := hy
    rw [hcomap] at hymem
    exact hymem
  let f : T →+* V := IsLocalization.lift hdenV
  have hfcomp : f.comp (algebraMap S T) = centerMap :=
    IsLocalization.lift_comp hdenV
  have hflocalEq :
      (IsLocalRing.maximalIdeal V).comap f =
        IsLocalRing.maximalIdeal T := by
    apply (Localization.AtPrime.eq_maximalIdeal_iff_comap_eq
      (I := Q)).mp
    rw [Ideal.comap_comap, hfcomp, hcomap]
  letI : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 4 0).mp hflocalEq
  have hdenN :
      ∀ y : Q.primeCompl, IsUnit ((algebraMap S N) y) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro hy
    have hy0 : (y : S) = 0 :=
      (IsFractionRing.injective S N) (by simpa using hy)
    exact y.property (hy0 ▸ Q.zero_mem)
  let toN : T →+* N := IsLocalization.lift hdenN
  letI : Algebra T N := toN.toAlgebra
  letI : IsScalarTower S T N :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.lift_comp hdenN).symm
  letI : IsFractionRing T N :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      Q.primeCompl T N
  let g : V →+* N := V.toSubring.subtype
  have hgf : g.comp f = algebraMap T N := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    rw [RingHom.comp_assoc, hfcomp,
      ← IsScalarTower.algebraMap_eq S T N]
    ext x
    exact hcenter x
  have hgfBijective : Function.Bijective (g.rangeRestrict.comp f) :=
    bijective_rangeRestrict_comp_of_valuationRing f g hgf
  have hfBijective : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hgfBijective.1
      exact congrArg g.rangeRestrict hxy
    · intro y
      rcases hgfBijective.2 (g.rangeRestrict y) with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hxN : g (f x) = g y :=
        congrArg (fun z : g.range => (z : N)) hx
      exact Subtype.ext hxN
  let fAlg : T →ₐ[S] V :=
    IsLocalization.liftAlgHom (M := Q.primeCompl)
      (f := Algebra.ofId S V) (fun y => by
        change IsUnit (centerMap y)
        exact hdenV y)
  have hfAlgBijective : Function.Bijective fAlg := hfBijective
  let e : T ≃ₐ[S] V := AlgEquiv.ofBijective fAlg hfAlgBijective
  exact IsLocalization.isLocalization_of_algEquiv Q.primeCompl e

omit [IsFractionRing B K] in
/-- A localization realization of the valuation ring discharges the explicit
reverse-containment condition introduced in `PrimeInertia`. -/
theorem primeInertiaComparisonAt_of_localization
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hlocal : HasValuationLocalizationAt
      (B := B) (D.valuationAt E) E.1) :
    D.PrimeInertiaComparisonAt E := by
  rcases hlocal with ⟨hlocal⟩
  exact ⟨hlocal.primeInertia_le_valuationInertia⟩

/-- Noetherianity of the affine base supplies the local comparison required
by the prime-inertia descent step. -/
theorem primeInertiaComparisonAt_of_isNoetherianRing
    [IsNoetherianRing B]
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    D.PrimeInertiaComparisonAt E :=
  D.primeInertiaComparisonAt_of_localization E
    (D.hasValuationLocalizationAt_of_isNoetherianRing E)

omit [IsFractionRing B K] in
/-- With the local normalization ring realized as the selected valuation
ring, valuation inertia and ring-theoretic prime inertia coincide. -/
theorem valuationInertia_eq_normalizationPrimeInertiaGroup_of_localization
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hlocal : HasValuationLocalizationAt
      (B := B) (D.valuationAt E) E.1) :
    CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing =
      normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal :=
  D.valuationInertia_eq_normalizationPrimeInertiaGroup E
    (D.primeInertiaComparisonAt_of_localization E hlocal)

/-- At every ramified height-one point in a diagram over a Noetherian base,
the two definitions of inertia agree. -/
theorem valuationInertia_eq_normalizationPrimeInertiaGroup_of_isNoetherianRing
    [IsNoetherianRing B]
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing =
      normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal :=
  D.valuationInertia_eq_normalizationPrimeInertiaGroup E
    (D.primeInertiaComparisonAt_of_isNoetherianRing E)

/-- The commutative-algebra localization bridge supplies the missing arrow:
valuation-inertia containment in `H` implies the prime-inertia containment
required for fixed-ring descent. -/
theorem normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing
    [IsNoetherianRing B]
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (H : Subgroup C.normalClosure.galoisGroup)
    (hvaluation :
      CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing ≤ H) :
    normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal ≤ H :=
  D.normalizationPrimeInertia_le_of_valuationInertia_le E
    (D.primeInertiaComparisonAt_of_isNoetherianRing E) H hvaluation

end Diagram

end DiagramBridge

end NormalizationInertia

end

end HodgeConjecture
