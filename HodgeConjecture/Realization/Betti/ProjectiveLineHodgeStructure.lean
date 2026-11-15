module

public import HodgeConjecture.Realization.Betti.ProjectiveLineComplexification
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Order.SupIndep

@[expose] public section

/-!
# The pure type-(1,1) structure on actual projective-line Betti H²

The rational space and its tensor complexification are the independently
constructed actual singular cohomology objects. Conjugation is canonical:
it conjugates the complex coefficient of every pure tensor and fixes its
rational cohomology factor. The type-(1,1) bigrading gives a finite pure
weight-two rational Hodge structure, with its decreasing filtration defined
by the sums of the bigrading pieces.

This module does not use a cycle map to define its pieces. Agreement of
this structure with the image of the actual scheme de Rham degree
filtration is a separate geometric comparison, proved in its own module.
No general Hodge decomposition or degeneration theorem is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineHodgeStructure

open TensorProduct ProjectiveLineBettiComplexification
open scoped ComplexConjugate

instance bettiFiniteDimensional : FiniteDimensional ℚ Betti :=
  ProjectiveLineBettiCohomology.h2Equiv.symm.finiteDimensional

instance complexificationFiniteDimensional : FiniteDimensional ℂ Complexification :=
  coordinates.symm.finiteDimensional

theorem finrank_betti : Module.finrank ℚ Betti = 1 := by
  rw [ProjectiveLineBettiCohomology.h2Equiv.finrank_eq]
  exact Module.finrank_self ℚ

theorem finrank_complexification : Module.finrank ℂ Complexification = 1 := by
  rw [coordinates.finrank_eq]
  exact Module.finrank_self ℂ

/-- Conjugation coming from the original rational tensor factor. -/
def conjugation (z : Complexification) : Complexification :=
  RationalComplexification.conjugation Betti z

@[simp]
theorem coordinates_conjugation (z : Complexification) :
    coordinates (conjugation z) = conj (coordinates z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp [conjugation, coordinates_tmul]
  | add x y hx hy => simp [conjugation, map_add] at hx hy ⊢; rw [hx, hy]

@[simp]
theorem conjugation_zero : conjugation 0 = 0 := by
  apply coordinates.injective
  simp

theorem conjugation_add (z w : Complexification) :
    conjugation (z + w) = conjugation z + conjugation w := by
  apply coordinates.injective
  simp

theorem conjugation_smul (c : ℂ) (z : Complexification) :
    conjugation (c • z) = conj c • conjugation z := by
  apply coordinates.injective
  simp [smul_eq_mul]

@[simp]
theorem conjugation_involutive (z : Complexification) :
    conjugation (conjugation z) = z := by
  apply coordinates.injective
  simp

@[simp]
theorem conjugation_eq_zero_iff (z : Complexification) : conjugation z = 0 ↔ z = 0 := by
  constructor
  · intro h
    simpa using congrArg conjugation h
  · rintro rfl
    exact conjugation_zero

/-- Only the original complex scalar is conjugated, so this is the canonical real structure. -/
@[simp]
theorem conjugation_tmul (c : ℂ) (z : Betti) :
    conjugation (c ⊗ₜ[ℚ] z) = conj c ⊗ₜ[ℚ] z := by
  apply coordinates.injective
  simp

@[simp]
theorem conjugation_rationalEmbedding (z : Betti) :
    conjugation (rationalEmbedding z) = rationalEmbedding z := by
  change conjugation ((1 : ℂ) ⊗ₜ[ℚ] z) = (1 : ℂ) ⊗ₜ[ℚ] z
  simp

/-- The conjugate subspace, expressed by the canonical involution's inverse image. -/
def conjugateSubmodule (W : Submodule ℂ Complexification) : Submodule ℂ Complexification :=
  RationalComplexification.conjugateSubmodule Betti W

@[simp]
theorem mem_conjugateSubmodule (W : Submodule ℂ Complexification) (z : Complexification) :
    z ∈ conjugateSubmodule W ↔ conjugation z ∈ W := Iff.rfl

@[simp]
theorem conjugateSubmodule_top : conjugateSubmodule ⊤ = ⊤ := by
  ext z
  simp

@[simp]
theorem conjugateSubmodule_bot : conjugateSubmodule ⊥ = ⊥ := by
  ext z
  simp

@[simp]
theorem conjugateSubmodule_involutive (W : Submodule ℂ Complexification) :
    conjugateSubmodule (conjugateSubmodule W) = W := by
  ext z
  simp

/-- The independently specified type-(1,1) bigrading on actual complexified singular H². -/
def bigrading (p q : ℤ) : Submodule ℂ Complexification :=
  if p = 1 ∧ q = 1 then ⊤ else ⊥

@[simp]
theorem bigrading_one_one : bigrading 1 1 = ⊤ := by simp [bigrading]

theorem bigrading_eq_bot (p q : ℤ) (h : ¬ (p = 1 ∧ q = 1)) : bigrading p q = ⊥ := by
  simp [bigrading, h]

theorem bigrading_pure_weight_two (p q : ℤ) (h : p + q ≠ 2) : bigrading p q = ⊥ := by
  apply bigrading_eq_bot
  rintro ⟨rfl, rfl⟩
  exact h (by norm_num)

theorem bigrading_effective (p q : ℤ) (h : p < 0 ∨ q < 0) : bigrading p q = ⊥ := by
  apply bigrading_eq_bot
  rintro ⟨rfl, rfl⟩
  omega

theorem bigrading_exhaustive : (⨆ pq : ℤ × ℤ, bigrading pq.1 pq.2) = ⊤ := by
  apply top_unique
  simpa using (le_iSup (fun pq : ℤ × ℤ ↦ bigrading pq.1 pq.2) (1, 1))

/-- Independence against the supremum of all other types gives an actual direct decomposition. -/
theorem bigrading_direct : iSupIndep (fun pq : ℤ × ℤ ↦ bigrading pq.1 pq.2) := by
  intro pq
  by_cases h : pq.1 = 1 ∧ pq.2 = 1
  · have hpq : pq = (1, 1) := Prod.ext h.1 h.2
    subst pq
    have hrest : (⨆ (pq : ℤ × ℤ) (_ : pq ≠ (1, 1)), bigrading pq.1 pq.2) = ⊥ := by
      apply iSup_eq_bot.mpr
      intro pq
      apply iSup_eq_bot.mpr
      intro hpq
      exact bigrading_eq_bot _ _ (fun h ↦ hpq (Prod.ext h.1 h.2))
    rw [hrest]
    exact disjoint_bot_right
  · dsimp only
    rw [bigrading_eq_bot _ _ h]
    exact disjoint_bot_left

/-- Canonical rational conjugation exchanges the two indices. -/
theorem conjugation_bigrading (p q : ℤ) (z : Complexification) :
    conjugation z ∈ bigrading q p ↔ z ∈ bigrading p q := by
  by_cases h : p = 1 ∧ q = 1
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (q = 1 ∧ p = 1) := fun h' ↦ h ⟨h'.2, h'.1⟩
    simp [bigrading_eq_bot p q h, bigrading_eq_bot q p h']

theorem conjugateSubmodule_bigrading (p q : ℤ) :
    conjugateSubmodule (bigrading p q) = bigrading q p := by
  ext z
  exact conjugation_bigrading q p z

/-- The decreasing Hodge filtration defined by sums of the specified Hodge pieces. -/
def filtration (p : ℤ) : Submodule ℂ Complexification :=
  ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), bigrading pq.1 pq.2

theorem filtration_antitone : Antitone filtration := by
  intro p q hpq
  unfold filtration
  apply iSup_le
  intro ij
  apply iSup_le
  intro hq
  exact le_iSup_of_le ij (le_iSup_of_le (hpq.trans hq) le_rfl)

theorem filtration_eq_top (p : ℤ) (hp : p ≤ 1) : filtration p = ⊤ := by
  unfold filtration
  apply top_unique
  calc
    ⊤ = bigrading 1 1 := bigrading_one_one.symm
    _ ≤ ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), bigrading pq.1 pq.2 :=
      le_iSup_of_le (1, 1) (le_iSup_of_le hp le_rfl)

theorem filtration_eq_bot (p : ℤ) (hp : 2 ≤ p) : filtration p = ⊥ := by
  apply iSup_eq_bot.mpr
  intro ij
  apply iSup_eq_bot.mpr
  intro hpi
  apply bigrading_eq_bot
  rintro ⟨hi, _⟩
  omega

@[simp]
theorem filtration_one : filtration 1 = ⊤ := filtration_eq_top 1 le_rfl

@[simp]
theorem filtration_two : filtration 2 = ⊥ := filtration_eq_bot 2 le_rfl

@[simp]
theorem filtration_zero : filtration 0 = ⊤ := filtration_eq_top 0 (by decide)

/-- Recovery of each weight-two type from the filtration and its actual conjugate. -/
theorem bigrading_eq_filtration_inf_conjugate (p q : ℤ) (hpq : p + q = 2) :
    bigrading p q = filtration p ⊓ conjugateSubmodule (filtration q) := by
  by_cases hp : p ≤ 1
  · by_cases hq : q ≤ 1
    · have hp' : p = 1 := by omega
      have hq' : q = 1 := by omega
      subst p
      subst q
      simp
    · have hq' : 2 ≤ q := by omega
      rw [filtration_eq_bot q hq', conjugateSubmodule_bot, inf_bot_eq]
      exact bigrading_eq_bot p q (by omega)
  · have hp' : 2 ≤ p := by omega
    rw [filtration_eq_bot p hp', bot_inf_eq]
    exact bigrading_eq_bot p q (by omega)

/-- The filtration and its conjugate are opposed in weight two. -/
theorem filtration_opposed (p : ℤ) :
    IsCompl (filtration p) (conjugateSubmodule (filtration (3 - p))) := by
  by_cases hp : p ≤ 1
  · rw [filtration_eq_top p hp, filtration_eq_bot (3 - p) (by omega), conjugateSubmodule_bot]
    exact isCompl_top_bot
  · rw [filtration_eq_bot p (by omega), filtration_eq_top (3 - p) (by omega), conjugateSubmodule_top]
    exact isCompl_bot_top

/-- The independent Betti filtration is a genuine pure rational weight-two structure. -/
def pureHodgeStructure : PureRationalHodgeStructure Betti 2 where
  finiteDimensional := inferInstance
  filtration := filtration
  antitone := filtration_antitone
  exhaustive := ⟨1, filtration_one⟩
  separated := ⟨2, filtration_two⟩
  opposed := filtration_opposed

/-- Rational classes are Hodge when their original tensor image lies in type (1,1). -/
def rationalHodgeClasses : Submodule ℚ Betti :=
  ((bigrading 1 1).restrictScalars ℚ).comap rationalEmbedding

theorem mem_rationalHodgeClasses (z : Betti) :
    z ∈ rationalHodgeClasses ↔ rationalEmbedding z ∈ bigrading 1 1 := Iff.rfl

theorem all_hodge (z : Betti) : z ∈ rationalHodgeClasses := by
  rw [mem_rationalHodgeClasses, bigrading_one_one]
  trivial

theorem rationalHodgeClasses_eq_top : rationalHodgeClasses = ⊤ :=
  Submodule.eq_top_iff'.mpr all_hodge

/-- The same rational condition is expressed by the actual conjugate filtration intersection. -/
theorem mem_rationalHodgeClasses_filtration (z : Betti) :
    z ∈ rationalHodgeClasses ↔
      rationalEmbedding z ∈ filtration 1 ∧ conjugation (rationalEmbedding z) ∈ filtration 1 := by
  rw [mem_rationalHodgeClasses, bigrading_eq_filtration_inf_conjugate 1 1 (by norm_num)]
  rfl

end HodgeConjecture.ProjectiveLineHodgeStructure
