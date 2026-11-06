module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Augmented chains on vertex tuples

The index counts vertices: degree `m` here consists of finite rational
linear combinations of ordered `m`-tuples, including the empty tuple as
the augmentation. Deleting vertices gives the actual alternating boundary;
prepending a vertex gives its cone. These concrete formulas are the
algebraic input for recursive barycentric subdivision.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.AffineSimplexChains

universe u v

/-- Ordered vertex tuples, with the empty tuple retained. -/
abbrev Vertices (E : Type u) (m : ℕ) := Fin m → E

/-- Finite rational chains on ordered vertex tuples. The index counts vertices. -/
abbrev Chain (E : Type u) (m : ℕ) := Vertices E m →₀ ℚ

/-- Delete one vertex of a tuple. -/
def face {E : Type u} {m : ℕ} (v : Vertices E (m + 1)) (i : Fin (m + 1)) :
    Vertices E m := i.removeNth v

/-- The oriented boundary of one ordered tuple, including the augmentation of a point. -/
def boundarySimplex {E : Type u} (m : ℕ) (v : Vertices E (m + 1)) : Chain E m :=
  ∑ i : Fin (m + 1), (-1 : ℚ) ^ (i : ℕ) • Finsupp.single (face v i) 1

/-- Linear extension of vertex deletion. -/
def boundary (E : Type u) (m : ℕ) : Chain E (m + 1) →ₗ[ℚ] Chain E m :=
  Finsupp.linearCombination ℚ (boundarySimplex m)

@[simp]
theorem boundary_single {E : Type u} (m : ℕ) (v : Vertices E (m + 1)) (a : ℚ) :
    boundary E m (Finsupp.single v a) = a • boundarySimplex m v :=
  by simp [boundary]

/-- Prepend the cone vertex to each actual tuple in a finite chain. -/
def cone {E : Type u} (p : E) (m : ℕ) : Chain E m →ₗ[ℚ] Chain E (m + 1) :=
  Finsupp.lmapDomain ℚ ℚ (fun v : Vertices E m ↦ Fin.cons p v)

@[simp]
theorem cone_single {E : Type u} (p : E) (m : ℕ) (v : Vertices E m) (a : ℚ) :
    cone p m (Finsupp.single v a) = Finsupp.single (Fin.cons p v) a :=
  by simp [cone]

@[simp]
theorem face_cons_zero {E : Type u} (p : E) {m : ℕ} (v : Vertices E m) :
    face (Fin.cons p v) 0 = v := by
  simp [face]

@[simp]
theorem face_cons_succ {E : Type u} (p : E) {m : ℕ} (v : Vertices E (m + 1))
    (i : Fin (m + 1)) :
    face (Fin.cons p v) i.succ = Fin.cons p (face v i) :=
  Fin.cons_comp_succ_succAbove p v i

/-- The cone boundary formula on a single nonempty tuple. -/
theorem boundarySimplex_cons {E : Type u} (p : E) (m : ℕ) (v : Vertices E (m + 1)) :
    boundarySimplex (m + 1) (Fin.cons p v) =
      Finsupp.single v 1 - cone p m (boundarySimplex m v) := by
  rw [boundarySimplex, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cons_zero, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, face_cons_succ]
  rw [boundarySimplex, map_sum]
  simp only [map_smul, cone_single, Finset.sum_neg_distrib]
  exact (sub_eq_add_neg _ _).symm

/-- On augmented chains, coning contracts the alternating boundary in every positive index. -/
theorem boundary_cone {E : Type u} (p : E) (m : ℕ) (c : Chain E (m + 1)) :
    boundary E (m + 1) (cone p (m + 1) c) = c - cone p m (boundary E m c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]; abel
  | single v a =>
    rw [cone_single, boundary_single, boundarySimplex_cons, boundary_single, map_smul, smul_sub]
    simp

/-- The cone of the empty tuple has its original augmentation. -/
theorem boundary_cone_zero {E : Type u} (p : E) (c : Chain E 0) :
    boundary E 0 (cone p 0 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a => simp [boundarySimplex]

/-- The actual alternating vertex boundary squares to zero, including at the augmentation. -/
theorem boundary_squared (E : Type u) (m : ℕ) (c : Chain E (m + 2)) :
    boundary E m (boundary E (m + 1) c) = 0 := by
  induction m with
  | zero =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd, add_zero]
    | single v a =>
      rw [← Fin.cons_self_tail v, ← cone_single, boundary_cone, map_sub,
        boundary_cone_zero, sub_self]
  | succ m ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd, add_zero]
    | single v a =>
      rw [← Fin.cons_self_tail v, ← cone_single, boundary_cone, map_sub,
        boundary_cone, ih, map_zero]
      abel

/-- Apply a function to all vertices of each original tuple. -/
def map {E : Type u} {F : Type v} (f : E → F) (m : ℕ) : Chain E m →ₗ[ℚ] Chain F m :=
  Finsupp.lmapDomain ℚ ℚ (fun v : Vertices E m ↦ f ∘ v)

@[simp]
theorem map_single {E : Type u} {F : Type v} (f : E → F) (m : ℕ)
    (v : Vertices E m) (a : ℚ) :
    map f m (Finsupp.single v a) = Finsupp.single (f ∘ v) a := by
  simp [map]

theorem boundary_map {E : Type u} {F : Type v} (f : E → F) (m : ℕ)
    (c : Chain E (m + 1)) :
    boundary F m (map f (m + 1) c) = map f m (boundary E m c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [map_single, boundary_single, map_smul]
    congr 1
    simp only [boundarySimplex, map_sum, map_smul, map_single]
    rfl

theorem map_cone {E : Type u} {F : Type v} (f : E → F) (p : E) (m : ℕ)
    (c : Chain E m) :
    map f (m + 1) (cone p m c) = cone (f p) m (map f m c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [cone_single, map_single]
    congr 1
    ext i
    cases i using Fin.cases <;> simp

end HodgeConjecture.AffineSimplexChains
