-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.LocalStructure

@[expose] public section

/-!
# Étaleness at a selected index-one prime

These proofs are adapted from AxiomMath/Stacks, revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean`,
under Apache-2.0; see `third_party/axiom-stacks/LICENSE`.

They isolate the finite-presentation, ramification, and étaleness consequences
used in the DVR form of the fixed-inertia argument. The fixed-ring assembly is
in `DvrInertiaFixedRing.lean`.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

open scoped Pointwise

/-- In a finite Galois algebra, the decomposition group's order is the
ramification index times the residue degree. -/
private theorem card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    (A B G : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (m : Ideal B) [m.IsPrime] :
    Nat.card (MulAction.stabilizer G m) = m.ramificationIdx A * m.inertiaDeg A := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (m.under A) B G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (m.under A) m G,
    Ideal.inertiaDegIn_eq_inertiaDeg (m.under A) m G,
    ← Algebra.IsInvariant.orbit_eq_primesOver A B G (m.under A) m,
    ← MulAction.index_stabilizer] at h
  have hpos : 0 < (MulAction.stabilizer G m).index := by
    by_contra! hz
    have he := (MulAction.stabilizer G m).index_mul_card
    rw [Nat.eq_zero_of_le_zero hz, zero_mul] at he
    exact Nat.card_pos (α := G) |>.ne' he.symm
  exact Nat.eq_of_mul_eq_mul_left hpos
    ((MulAction.stabilizer G m).index_mul_card.trans h.symm)

/-- Over a normal field extension, finite separable degree counts
automorphisms of the extension field. -/
private theorem finSepDegree_eq_card_aut_of_normal
    (k F : Type*) [Field k] [Field F] [Algebra k F] [Normal k F] :
    Field.finSepDegree k F = Nat.card Gal(F/k) := by
  rw [Field.finSepDegree_eq_of_adjoin_splits k F F (IntermediateField.adjoin_univ k F)
    (fun x _ ↦ ⟨Algebra.IsIntegral.isIntegral x, Normal.splits inferInstance x⟩)]
  exact (Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom k F).toEquiv).symm

section ResidueFields

attribute [local instance] Ideal.Quotient.field

/-- The decomposition group has order the inertia-group order times the
separable degree of the residue extension. -/
private theorem card_stabilizer_eq_card_inertia_mul_finSepDegree
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [SMulCommClass G A B] (p : Ideal A) (P : Ideal B)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Field.finSepDegree (A ⧸ p) (B ⧸ P) := by
  let := Ideal.Quotient.normal G p P
  have heq : Subgroup.index ((P.inertia G).subgroupOf (MulAction.stabilizer G P)) =
      Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [finSepDegree_eq_card_aut_of_normal, ← heq,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv]
  exact ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index.symm

/-- For the action of a prime's inertia group, both the decomposition and
inertia subgroups are full and the residue extension has separable degree one. -/
private theorem card_inertia_inertia_and_finSepDegree_eq_one
    {B G C : Type*} [CommRing B] [CommRing C] [Algebra C B]
    [Group G] [Finite G] [MulSemiringAction G B] (P : Ideal B) (q : Ideal C)
    [q.IsMaximal] [P.IsMaximal] [P.LiesOver q] [IsGaloisGroup (P.inertia G) C B] :
    Nat.card (MulAction.stabilizer (P.inertia G) P) = Nat.card (P.inertia G) ∧
      Nat.card (P.inertia (P.inertia G)) = Nat.card (P.inertia G) ∧
      Field.finSepDegree (C ⧸ q) (B ⧸ P) = 1 := by
  have hcard : Nat.card (MulAction.stabilizer (P.inertia G) P) = Nat.card (P.inertia G) := by
    rw [top_unique (a := MulAction.stabilizer (P.inertia G) P) fun g _ ↦
      Ideal.inertia_le_stabilizer (M := G) P g.property,
      Nat.card_congr (Subgroup.topEquiv (G := P.inertia G)).toEquiv]
  have hcardi : Nat.card (P.inertia (P.inertia G)) = Nat.card (P.inertia G) := by
    rw [top_unique (a := P.inertia (P.inertia G)) fun g _ ↦
      Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp g.property),
      Nat.card_congr (Subgroup.topEquiv (G := P.inertia G)).toEquiv]
  have hsep := card_stabilizer_eq_card_inertia_mul_finSepDegree (G := P.inertia G) q P
  erw [hcard, hcardi] at hsep
  exact ⟨hcard, hcardi, by nlinarith [Nat.card_pos (α := P.inertia G)]⟩

/-- A ring with finitely many primes is finitely presented over itself after
localizing at a prime: finitely many primes allow one principal denominator. -/
private theorem finitePresentation_atPrime_of_finite_spectrum
    (R : Type*) [CommRing R] [Finite (PrimeSpectrum R)] (p : Ideal R) [p.IsPrime] :
    Algebra.FinitePresentation R (Localization.AtPrime p) := by
  classical
  let T := {q : PrimeSpectrum R // ¬ q.asIdeal ≤ p}
  have hex (q : T) : ∃ x : R, x ∈ q.1.asIdeal ∧ x ∉ p :=
    IsConcreteLE.not_le_iff_exists.mp q.2
  choose x hx hxp using hex
  let := Fintype.ofFinite T
  let f := ∏ q : T, x q
  have hfp : f ∉ p := by
    simpa only [f, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists] using hxp
  have hpow : ∀ s ∈ p.primeCompl, ∃ m ∈ Submonoid.powers f, s ∣ m := by
    intro s hs
    have hf : f ∈ (Ideal.span ({s} : Set R)).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro q hq
      have hnot : ¬ q ≤ p := fun h ↦ hs (h (Ideal.subset_span (Set.mem_singleton s) |> hq.1))
      let q' : T := ⟨⟨q, hq.2⟩, hnot⟩
      exact q.mem_of_dvd (Finset.dvd_prod_of_mem x (Finset.mem_univ q')) (hx q')
    obtain ⟨n, hn⟩ := hf
    exact ⟨f ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : IsLocalization.Away f (Localization.AtPrime p) :=
    (IsLocalization.iff_of_le_of_exists_dvd
      (Submonoid.powers f) p.primeCompl hle hpow).mpr inferInstance
  exact IsLocalization.Away.finitePresentation f

/-- For a finite flat algebra with finite prime spectrum, separability of the
selected residue extension and ramification index one imply étaleness after
localizing at that prime. -/
theorem etale_atPrime_of_ramificationIdx_eq_one
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [Module.Finite A C] [Module.Flat A C]
    [Finite (PrimeSpectrum C)]
    (p : Ideal A) (q : Ideal C) [p.IsMaximal] [q.IsMaximal] [q.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (C ⧸ q)] (he : q.ramificationIdx A = 1) :
    Algebra.Etale A (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmap : p.map (algebraMap A (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at he
    simpa only [← q.over_def p] using he
  have : Algebra.IsUnramifiedAt A q :=
    (Algebra.isUnramifiedAt_iff_map_eq A p q).mpr ⟨inferInstance, hmap⟩
  have : Algebra.IsEtaleAt A q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  have : Algebra.FinitePresentation C (Localization.AtPrime q) :=
    finitePresentation_atPrime_of_finite_spectrum C q
  have : Algebra.FinitePresentation A (Localization.AtPrime q) :=
    Algebra.FinitePresentation.trans A C (Localization.AtPrime q)
  exact ⟨inferInstance, inferInstance⟩

/-- In a finite flat Galois tower, taking invariants by the inertia group
gives ramification index one and a separable residue extension at the
contracted prime. This is the arithmetic input for Stacks Tag `09EH`. -/
theorem ramificationIdx_eq_one_and_isSeparable_of_inertia
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
    (C : Type*) [CommRing C] [IsDomain C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] [Module.Finite A C] [Module.Finite C B] [Module.Flat C B]
    [IsGaloisGroup (P.inertia G) C B]
    (q : Ideal C) [q.IsMaximal] [q.LiesOver p] [P.LiesOver q] :
    q.ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ p) (C ⧸ q) := by
  obtain ⟨hcard, hcardi, hsep1⟩ := card_inertia_inertia_and_finSepDegree_eq_one (G := G) P q
  have : IsScalarTower (A ⧸ p) (C ⧸ q) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change Ideal.Quotient.mk P (algebraMap A B a) =
        Ideal.Quotient.mk P (algebraMap C B (algebraMap A C a))
      rw [← IsScalarTower.algebraMap_apply A C B])
  have htower := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic
    (A ⧸ p) (C ⧸ q) (B ⧸ P)
  rw [hsep1, mul_one] at htower
  have hupper := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg C B (P.inertia G) P
  erw [hcard] at hupper
  have htotal := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg A B G P
  rw [card_stabilizer_eq_card_inertia_mul_finSepDegree p P, hupper,
    Ideal.ramificationIdx_tower (R := A) q P, Ideal.inertiaDeg_tower (R := A) q P,
    ← htower] at htotal
  have hepos := P.ramificationIdx_pos C
  have hfpos := P.inertiaDeg_pos C
  have hcancel : Field.finSepDegree (A ⧸ p) (C ⧸ q) =
      q.ramificationIdx A * q.inertiaDeg A := by
    nlinarith
  letI : Module.Finite A (C ⧸ q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective A q)
  letI : FiniteDimensional (A ⧸ p) (C ⧸ q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (C ⧸ q)
  have hle := Field.finSepDegree_le_finrank (A ⧸ p) (C ⧸ q)
  rw [← Ideal.inertiaDeg_eq_of_isMaximal p q] at hle
  have heq : q.ramificationIdx A = 1 := by
    have := q.ramificationIdx_pos A
    have := q.inertiaDeg_pos A
    nlinarith
  refine ⟨heq, (Field.finSepDegree_eq_finrank_iff (A ⧸ p) (C ⧸ q)).mp ?_⟩
  rw [hcancel, heq, one_mul, Ideal.inertiaDeg_eq_of_isMaximal p q]

end ResidueFields

end

end HodgeConjecture.NormalizationInertia
