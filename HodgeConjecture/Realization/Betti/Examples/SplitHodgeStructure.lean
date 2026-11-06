module

public import HodgeConjecture.Realization.Betti.Examples.SplitCycleClass
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Order.SupIndep

@[expose] public section

/-!
# The pure degree-zero Hodge structure of a finite split complex scheme

The rational space is the constructed singular cohomology of the actual
complex-point space. Its genuine tensor complexification is identified with
complex functions by extending the independently defined Betti coordinates.
In the finite reduced degree-zero specialization, the effective geometric
types have nonnegative indices with sum zero, hence only type `(0,0)`.
This specifies more than weight zero alone. Complex conjugation is induced
from the rational structure. The rational Hodge subspace
is defined by inverse image of the complex `(0,0)` piece, and only then proved
to be the whole rational space. No Chow class or cycle-class map is used in
these constructions.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitHodgeStructure

noncomputable section

open TensorProduct
open scoped ComplexConjugate

variable (I : Type) [Finite I]

/-- The actual tensor complexification of rational singular cohomology. -/
abbrev Complexification := ℂ ⊗[ℚ] SplitBetti.Cohomology I

/-- Complexification of Betti evaluation, independently of cycle classes. -/
def complexCoordinates : Complexification I ≃ₗ[ℂ] (I → ℂ) := by
  classical
  letI := Fintype.ofFinite I
  exact (LinearEquiv.baseChange ℚ ℂ _ _ (SplitBetti.coordinates I)).trans
    (TensorProduct.piScalarRight ℚ ℂ ℂ I)

@[simp]
theorem complexCoordinates_tmul (c : ℂ) (h : SplitBetti.Cohomology I) (i : I) :
    complexCoordinates I (c ⊗ₜ[ℚ] h) i = c * (SplitBetti.coordinates I h i : ℂ) := by
  simp only [complexCoordinates, LinearEquiv.trans_apply, LinearEquiv.baseChange,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.smul_def]
  exact mul_comm _ _

/-- The canonical rational-to-complex map is the pure tensor `1 ⊗ h`. -/
def rationalEmbedding : SplitBetti.Cohomology I →ₗ[ℚ] Complexification I :=
  TensorProduct.mk ℚ ℂ (SplitBetti.Cohomology I) 1

omit [Finite I] in
@[simp]
theorem rationalEmbedding_apply (h : SplitBetti.Cohomology I) :
    rationalEmbedding I h = (1 : ℂ) ⊗ₜ[ℚ] h := rfl

@[simp]
theorem complexCoordinates_rationalEmbedding (h : SplitBetti.Cohomology I) (i : I) :
    complexCoordinates I (rationalEmbedding I h) i = (SplitBetti.coordinates I h i : ℂ) := by
  simp

theorem rationalEmbedding_injective : Function.Injective (rationalEmbedding I) := by
  intro h k he
  apply (SplitBetti.coordinates I).injective
  ext i
  have hi := congrArg (fun z ↦ complexCoordinates I z i) he
  simpa using hi

instance cohomologyFiniteDimensional : FiniteDimensional ℚ (SplitBetti.Cohomology I) := by
  classical
  letI := Fintype.ofFinite I
  exact (SplitBetti.coordinates I).symm.finiteDimensional

instance complexificationFiniteDimensional : FiniteDimensional ℂ (Complexification I) := by
  classical
  letI := Fintype.ofFinite I
  exact (complexCoordinates I).symm.finiteDimensional

/-- Conjugation in the complexification induced by its rational Betti structure. -/
def conjugation (z : Complexification I) : Complexification I :=
  (complexCoordinates I).symm (fun i ↦ conj (complexCoordinates I z i))

@[simp]
theorem complexCoordinates_conjugation (z : Complexification I) (i : I) :
    complexCoordinates I (conjugation I z) i = conj (complexCoordinates I z i) := by
  simp [conjugation]

@[simp]
theorem conjugation_zero : conjugation I 0 = 0 := by
  apply (complexCoordinates I).injective
  ext i
  rw [complexCoordinates_conjugation, (complexCoordinates I).map_zero]
  exact map_zero (starRingEnd ℂ)

theorem conjugation_add (z w : Complexification I) :
    conjugation I (z + w) = conjugation I z + conjugation I w := by
  apply (complexCoordinates I).injective
  ext i
  rw [complexCoordinates_conjugation, (complexCoordinates I).map_add,
    (complexCoordinates I).map_add]
  simp only [Pi.add_apply, complexCoordinates_conjugation]
  exact map_add (starRingEnd ℂ) _ _

theorem conjugation_smul (c : ℂ) (z : Complexification I) :
    conjugation I (c • z) = conj c • conjugation I z := by
  apply (complexCoordinates I).injective
  ext i
  rw [complexCoordinates_conjugation, (complexCoordinates I).map_smul,
    (complexCoordinates I).map_smul]
  change conj (c * complexCoordinates I z i) = conj c * _
  rw [map_mul, complexCoordinates_conjugation]

@[simp]
theorem conjugation_involutive (z : Complexification I) :
    conjugation I (conjugation I z) = z := by
  apply (complexCoordinates I).injective
  ext i
  simp

@[simp]
theorem conjugation_eq_zero_iff (z : Complexification I) :
    conjugation I z = 0 ↔ z = 0 := by
  constructor
  · intro h
    simpa using congrArg (conjugation I) h
  · rintro rfl
    exact conjugation_zero I

/-- The conjugation is the canonical one: it conjugates only the complex
coefficient of a pure tensor and fixes the rational cohomology factor. -/
@[simp]
theorem conjugation_tmul (c : ℂ) (h : SplitBetti.Cohomology I) :
    conjugation I (c ⊗ₜ[ℚ] h) = conj c ⊗ₜ[ℚ] h := by
  apply (complexCoordinates I).injective
  ext i
  simp

@[simp]
theorem conjugation_rationalEmbedding (h : SplitBetti.Cohomology I) :
    conjugation I (rationalEmbedding I h) = rationalEmbedding I h := by
  simp

/-- The pure degree-zero bigrading on the independently complexified Betti space. -/
def bigrading (p q : ℤ) : Submodule ℂ (Complexification I) :=
  if p = 0 ∧ q = 0 then ⊤ else ⊥

omit [Finite I] in
@[simp]
theorem bigrading_zero_zero : bigrading I 0 0 = ⊤ := by
  simp [bigrading]

omit [Finite I] in
theorem bigrading_eq_bot (p q : ℤ) (h : ¬ (p = 0 ∧ q = 0)) :
    bigrading I p q = ⊥ := by
  simp [bigrading, h]

omit [Finite I] in
/-- All nonzero-weight pieces vanish. -/
theorem bigrading_pure_weight_zero (p q : ℤ) (h : p + q ≠ 0) :
    bigrading I p q = ⊥ := by
  apply bigrading_eq_bot
  rintro ⟨rfl, rfl⟩
  exact h rfl

omit [Finite I] in
/-- The geometric degree-zero specialization is effective: a negative Hodge
index has zero piece, including nontrivial weight-zero pairs `(p,-p)`. -/
theorem bigrading_effective (p q : ℤ) (h : p < 0 ∨ q < 0) :
    bigrading I p q = ⊥ := by
  apply bigrading_eq_bot
  rintro ⟨rfl, rfl⟩
  simp at h

omit [Finite I] in
/-- The complex Hodge pieces exhaust the genuine complexification. -/
theorem bigrading_exhaustive :
    (⨆ pq : ℤ × ℤ, bigrading I pq.1 pq.2) = ⊤ := by
  apply top_unique
  simpa using (le_iSup (fun pq : ℤ × ℤ ↦ bigrading I pq.1 pq.2) (0, 0))

omit [Finite I] in
/-- Independence against the sum of every other piece gives a direct
decomposition, not merely pairwise disjointness. -/
theorem bigrading_direct : iSupIndep (fun pq : ℤ × ℤ ↦ bigrading I pq.1 pq.2) := by
  intro pq
  by_cases hpq : pq.1 = 0 ∧ pq.2 = 0
  · have heq : pq = (0, 0) := Prod.ext hpq.1 hpq.2
    subst pq
    have hrest : (⨆ (pq : ℤ × ℤ) (_ : pq ≠ (0, 0)), bigrading I pq.1 pq.2) = ⊥ := by
      apply iSup_eq_bot.mpr
      intro pq
      apply iSup_eq_bot.mpr
      intro hpq
      exact bigrading_eq_bot I _ _ (fun h ↦ hpq (Prod.ext h.1 h.2))
    rw [hrest]
    exact disjoint_bot_right
  · dsimp only
    rw [bigrading_eq_bot I _ _ hpq]
    exact disjoint_bot_left

/-- Complex conjugation exchanges the two Hodge indices. -/
theorem conjugation_bigrading (p q : ℤ) (z : Complexification I) :
    conjugation I z ∈ bigrading I q p ↔ z ∈ bigrading I p q := by
  by_cases h : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (q = 0 ∧ p = 0) := fun h' ↦ h ⟨h'.2, h'.1⟩
    simp [bigrading_eq_bot I p q h, bigrading_eq_bot I q p h']

/-- Rational Hodge classes are defined by membership of the tensor image in
the independently specified complex `(0,0)` piece. -/
def rationalHodgeClasses : Submodule ℚ (SplitBetti.Cohomology I) :=
  ((bigrading I 0 0).restrictScalars ℚ).comap (rationalEmbedding I)

omit [Finite I] in
theorem mem_rationalHodgeClasses (h : SplitBetti.Cohomology I) :
    h ∈ rationalHodgeClasses I ↔ rationalEmbedding I h ∈ bigrading I 0 0 := Iff.rfl

omit [Finite I] in
/-- Every rational degree-zero class of a finite reduced complex scheme has
Hodge type `(0,0)`. -/
theorem all_hodge (h : SplitBetti.Cohomology I) : h ∈ rationalHodgeClasses I := by
  rw [mem_rationalHodgeClasses, bigrading_zero_zero]
  trivial

omit [Finite I] in
theorem rationalHodgeClasses_eq_top : rationalHodgeClasses I = ⊤ := by
  exact Submodule.eq_top_iff'.mpr (all_hodge I)

variable {I} {J : Type} [Finite J]

/-- Scalar extension of an actual rational map on singular cohomology. -/
def complexifyMap (f : SplitBetti.Cohomology I →ₗ[ℚ] SplitBetti.Cohomology J) :
    Complexification I →ₗ[ℂ] Complexification J := f.baseChange ℂ

omit [Finite I] [Finite J] in
@[simp]
theorem complexifyMap_tmul (f : SplitBetti.Cohomology I →ₗ[ℚ] SplitBetti.Cohomology J)
    (c : ℂ) (h : SplitBetti.Cohomology I) :
    complexifyMap f (c ⊗ₜ[ℚ] h) = c ⊗ₜ[ℚ] f h := rfl

/-- Hodge morphisms preserve every complex bigrading piece after the genuine
scalar extension of their underlying rational linear map. -/
def IsHodgeMorphism (f : SplitBetti.Cohomology I →ₗ[ℚ] SplitBetti.Cohomology J) : Prop :=
  ∀ p q, bigrading I p q ≤ (bigrading J p q).comap (complexifyMap f)

omit [Finite I] [Finite J] in
/-- Every rational linear map between these pure type-`(0,0)` cohomology
spaces is a Hodge morphism. -/
theorem all_isHodgeMorphism (f : SplitBetti.Cohomology I →ₗ[ℚ] SplitBetti.Cohomology J) :
    IsHodgeMorphism f := by
  intro p q
  by_cases h : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [bigrading_eq_bot I p q h]
    exact bot_le

end

end HodgeConjecture.SplitHodgeStructure
