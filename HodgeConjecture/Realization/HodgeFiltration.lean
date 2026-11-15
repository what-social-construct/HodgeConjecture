module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-!
# Rational Hodge targets from complex filtrations

The complexification, rational embedding and conjugation are constructed
on the actual tensor product. A rational target is the inverse image of
`Fᵖ ∩ conjugate Fᵖ`, independently of cycles. For a pure weight-`2p`
Hodge structure this is its rational type-`(p,p)` subspace.

`PureRationalHodgeStructure` records the usual finite-dimensional,
bounded, opposed-filtration conditions. It contains no cycle-class map
or supplied Hodge-class subspace. Constructing this structure for a
general variety still requires the geometric comparison and purity proofs.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HodgeConjecture

namespace RationalComplexification

universe u v

variable (H : Type u) [AddCommGroup H] [Module ℚ H]

abbrev Space := ℂ ⊗[ℚ] H

/-- The original rational vector embeds by tensoring with one. -/
def embedding : H →ₗ[ℚ] Space H := TensorProduct.mk ℚ ℂ H 1

theorem embedding_injective : Function.Injective (embedding H) :=
  Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℂ) (M := H)

/-- Complex conjugation viewed as a rational linear map. -/
def scalarConjugation : ℂ →ₗ[ℚ] ℂ :=
  Complex.conjAe.toLinearEquiv.toLinearMap.restrictScalars ℚ

/-- Canonical conjugation acts only on the complex coefficient. -/
def conjugation : Space H →ₗ[ℚ] Space H :=
  TensorProduct.map scalarConjugation (LinearMap.id : H →ₗ[ℚ] H)

@[simp]
theorem conjugation_tmul (c : ℂ) (x : H) :
    conjugation H (c ⊗ₜ[ℚ] x) = star c ⊗ₜ[ℚ] x := rfl

@[simp]
theorem conjugation_embedding (x : H) : conjugation H (embedding H x) = embedding H x := by
  simp [embedding]

theorem conjugation_smul (c : ℂ) (z : Space H) :
    conjugation H (c • z) = star c • conjugation H z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

@[simp]
theorem conjugation_involutive (z : Space H) :
    conjugation H (conjugation H z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp
  | add x y hx hy => simp [hx, hy]

/-- Conjugate subspace under the canonical rational real structure. -/
def conjugateSubmodule (W : Submodule ℂ (Space H)) : Submodule ℂ (Space H) where
  carrier := {z | conjugation H z ∈ W}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change conjugation H (x + y) ∈ W
    rw [map_add]
    exact W.add_mem hx hy
  smul_mem' := by
    intro c z hz
    change conjugation H (c • z) ∈ W
    rw [conjugation_smul]
    exact W.smul_mem (star c) hz

@[simp]
theorem mem_conjugateSubmodule (W : Submodule ℂ (Space H)) (z : Space H) :
    z ∈ conjugateSubmodule H W ↔ conjugation H z ∈ W := Iff.rfl

@[simp]
theorem conjugateSubmodule_top : conjugateSubmodule H ⊤ = ⊤ := by ext; simp

@[simp]
theorem conjugateSubmodule_bot : conjugateSubmodule H ⊥ = ⊥ := by
  ext z
  simp only [mem_conjugateSubmodule, Submodule.mem_bot]
  constructor
  · intro h
    simpa using congrArg (conjugation H) h
  · rintro rfl
    simp

@[simp]
theorem conjugateSubmodule_involutive (W : Submodule ℂ (Space H)) :
    conjugateSubmodule H (conjugateSubmodule H W) = W := by ext; simp

variable {H} {K : Type v} [AddCommGroup K] [Module ℚ K]

/-- Scalar extension of the original rational map. -/
abbrev map (f : H →ₗ[ℚ] K) : Space H →ₗ[ℂ] Space K := f.baseChange ℂ

@[simp]
theorem map_embedding (f : H →ₗ[ℚ] K) (x : H) :
    map f (embedding H x) = embedding K (f x) := rfl

theorem conjugation_map (f : H →ₗ[ℚ] K) (z : Space H) :
    conjugation K (map f z) = map f (conjugation H z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp [hx, hy]

end RationalComplexification

namespace HodgeFiltration

universe u v

variable {H : Type u} [AddCommGroup H] [Module ℚ H]

/-- The rational inverse image of the diagonal filtration intersection. -/
def rationalHodgeClasses (F : ℤ → Submodule ℂ (RationalComplexification.Space H))
    (p : ℤ) : Submodule ℚ H :=
  ((F p ⊓ RationalComplexification.conjugateSubmodule H (F p)).restrictScalars ℚ).comap
    (RationalComplexification.embedding H)

theorem mem_rationalHodgeClasses
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ) (x : H) :
    x ∈ rationalHodgeClasses F p ↔
      RationalComplexification.embedding H x ∈ F p ∧
        RationalComplexification.conjugation H
          (RationalComplexification.embedding H x) ∈ F p := Iff.rfl

/-- A rational vector is fixed by conjugation, so one filtration test suffices. -/
theorem mem_rationalHodgeClasses_iff
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ) (x : H) :
    x ∈ rationalHodgeClasses F p ↔ RationalComplexification.embedding H x ∈ F p := by
  simp [mem_rationalHodgeClasses]

variable {K : Type v} [AddCommGroup K] [Module ℚ K]

/-- A rational map preserves the two complex filtrations after scalar extension. -/
def IsFilteredMap
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H))
    (G : ℤ → Submodule ℂ (RationalComplexification.Space K)) (f : H →ₗ[ℚ] K) : Prop :=
  ∀ p, F p ≤ (G p).comap (RationalComplexification.map f)

/-- Filtered rational maps preserve the independently defined rational targets. -/
theorem map_mem_rationalHodgeClasses
    {F : ℤ → Submodule ℂ (RationalComplexification.Space H)}
    {G : ℤ → Submodule ℂ (RationalComplexification.Space K)}
    {f : H →ₗ[ℚ] K} (hf : IsFilteredMap F G f) (p : ℤ) {x : H}
    (hx : x ∈ rationalHodgeClasses F p) : f x ∈ rationalHodgeClasses G p := by
  rw [mem_rationalHodgeClasses_iff] at hx ⊢
  exact (RationalComplexification.map_embedding f x) ▸ hf p hx

end HodgeFiltration

/-- A finite rational vector space with a bounded decreasing complex
filtration opposed to its canonical conjugate in the specified weight. -/
structure PureRationalHodgeStructure
    (H : Type*) [AddCommGroup H] [Module ℚ H] (weight : ℤ) where
  finiteDimensional : FiniteDimensional ℚ H
  filtration : ℤ → Submodule ℂ (RationalComplexification.Space H)
  antitone : Antitone filtration
  exhaustive : ∃ p, filtration p = ⊤
  separated : ∃ p, filtration p = ⊥
  opposed : ∀ p, IsCompl (filtration p)
    (RationalComplexification.conjugateSubmodule H (filtration (weight + 1 - p)))

namespace PureRationalHodgeStructure

variable {H : Type*} [AddCommGroup H] [Module ℚ H] {weight : ℤ}

/-- A Hodge piece recovered from the filtration and its canonical conjugate. -/
def piece (S : PureRationalHodgeStructure H weight) (p q : ℤ) :
    Submodule ℂ (RationalComplexification.Space H) :=
  if p + q = weight then
    S.filtration p ⊓ RationalComplexification.conjugateSubmodule H (S.filtration q)
  else ⊥

/-- The required rational type-(p,p) target in even weight 2p. -/
def rationalHodgeClasses (p : ℤ) (S : PureRationalHodgeStructure H (2 * p)) :
    Submodule ℚ H := HodgeFiltration.rationalHodgeClasses S.filtration p

theorem mem_rationalHodgeClasses (p : ℤ) (S : PureRationalHodgeStructure H (2 * p)) (x : H) :
    x ∈ rationalHodgeClasses p S ↔ RationalComplexification.embedding H x ∈ S.piece p p := by
  simp only [rationalHodgeClasses, HodgeFiltration.mem_rationalHodgeClasses,
    piece, show p + p = 2 * p by omega, ite_true,
    Submodule.mem_inf, RationalComplexification.mem_conjugateSubmodule]

end PureRationalHodgeStructure

end HodgeConjecture
