module

public import HodgeConjecture.Realization.Betti.SingularChainCoordinates
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-!
# Actual subcomplex chains and supported finite coordinates

The native chain map of a simplicial subcomplex inclusion is extension of
finite-support coordinates along subtype inclusion. Its range consists
exactly of the supported original chains, and its boundary is the original
native chain differential restricted to that submodule.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SubcomplexChainCoordinates

open CategoryTheory Opposite Simplicial SingularChainCoordinates

variable {S T : SSet.{0}}

/-- Natural finite coordinates on the original native simplicial chain maps. -/
theorem coordinates_map (f : S ⟶ T) (n : ℕ) (c : S.obj (op ⦋n⦌) →₀ ℚ) :
    (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n (coordinates S n c) =
      coordinates T n (Finsupp.lmapDomain ℚ ℚ (f.app (op ⦋n⦌)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    have h := congrArg (fun g : ModuleCat.of ℚ ℚ ⟶ (complex T).X n ↦ g a)
      (SSet.ι_chainComplexMap_f S T f (ModuleCat.of ℚ ℚ) σ)
    simpa only [coordinates_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The original inclusion of actual native chain objects. -/
abbrev inclusion (A : S.Subcomplex) := SSet.chainComplexMap A.ι (ModuleCat.of ℚ ℚ)

/-- Include a contained simplex coordinate into the original simplex indexing set. -/
def inclusionCoordinates (A : S.Subcomplex) (n : ℕ) :
    ((A : SSet).obj (op ⦋n⦌) →₀ ℚ) →ₗ[ℚ] (S.obj (op ⦋n⦌) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ Subtype.val

theorem inclusion_coordinates (A : S.Subcomplex) (n : ℕ)
    (c : (A : SSet).obj (op ⦋n⦌) →₀ ℚ) :
    (inclusion A).f n (coordinates A n c) = coordinates S n (inclusionCoordinates A n c) :=
  coordinates_map A.ι n c

/-- Native supported coordinates on the original whole-space simplex set. -/
def supportedCoordinates (A : S.Subcomplex) (n : ℕ) :
    Submodule ℚ (S.obj (op ⦋n⦌) →₀ ℚ) := Finsupp.supported ℚ ℚ (A.obj (op ⦋n⦌))

theorem range_inclusionCoordinates (A : S.Subcomplex) (n : ℕ) :
    LinearMap.range (inclusionCoordinates A n) = supportedCoordinates A n := by
  simpa [inclusionCoordinates, supportedCoordinates]
    using Finsupp.lmapDomain_supported ℚ ℚ
      (Subtype.val : (A : SSet).obj (op ⦋n⦌) → S.obj (op ⦋n⦌)) Set.univ

theorem inclusionCoordinates_injective (A : S.Subcomplex) (n : ℕ) :
    Function.Injective (inclusionCoordinates A n) := Finsupp.mapDomain_injective Subtype.val_injective

/-- A native chain inclusion is injective on its actual chain objects. -/
theorem inclusion_injective (A : S.Subcomplex) (n : ℕ) : Function.Injective ((inclusion A).f n) := by
  intro c d h
  obtain ⟨c, rfl⟩ := (coordinates A n).surjective c
  obtain ⟨d, rfl⟩ := (coordinates A n).surjective d
  apply congrArg (coordinates A n)
  apply inclusionCoordinates_injective A n
  apply (coordinates S n).injective
  simpa only [← inclusion_coordinates] using h

/-- The supported submodule of Mathlib's original whole-space chain object. -/
def chainSubmodule (A : S.Subcomplex) (n : ℕ) : Submodule ℚ ((complex S).X n) :=
  (supportedCoordinates A n).map (coordinates S n).toLinearMap

theorem mem_chainSubmodule_iff (A : S.Subcomplex) (n : ℕ) (c : (complex S).X n) :
    c ∈ chainSubmodule A n ↔ (coordinates S n).symm c ∈ supportedCoordinates A n := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa using hd
  · intro hc
    exact ⟨(coordinates S n).symm c, hc, (coordinates S n).apply_symm_apply c⟩

/-- The native supported-chain predicate is exactly a condition on its actual finite simplex support. -/
theorem mem_chainSubmodule_iff_support (A : S.Subcomplex) (n : ℕ) (c : (complex S).X n) :
    c ∈ chainSubmodule A n ↔
      ∀ σ ∈ ((coordinates S n).symm c).support, σ ∈ A.obj (op ⦋n⦌) := by
  rw [mem_chainSubmodule_iff]
  rfl

/-- A native generator is supported whenever its original singular simplex belongs to the subcomplex. -/
theorem ιChainComplex_mem_chainSubmodule (A : S.Subcomplex) (n : ℕ)
    (σ : S.obj (op ⦋n⦌)) (hσ : σ ∈ A.obj (op ⦋n⦌)) (a : ℚ) :
    (S.ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) a ∈ chainSubmodule A n := by
  rw [← coordinates_single, mem_chainSubmodule_iff, LinearEquiv.symm_apply_apply]
  exact Finsupp.single_mem_supported ℚ a hσ

/-- The actual inclusion range is exactly the supported submodule of the original native chains. -/
theorem range_inclusion (A : S.Subcomplex) (n : ℕ) :
    LinearMap.range ((inclusion A).f n).hom = chainSubmodule A n := by
  have hs : ((inclusion A).f n).hom.comp (coordinates A n).toLinearMap =
      (coordinates S n).toLinearMap.comp (inclusionCoordinates A n) := by
    apply LinearMap.ext
    intro c
    exact inclusion_coordinates A n c
  have h := congrArg LinearMap.range hs
  simpa only [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    range_inclusionCoordinates, chainSubmodule] using h

/-- The original small-chain object is linearly equivalent to its actual supported range. -/
def chainSubmoduleEquiv (A : S.Subcomplex) (n : ℕ) :
    (complex (A : SSet)).X n ≃ₗ[ℚ] chainSubmodule A n :=
  (LinearEquiv.ofInjective ((inclusion A).f n).hom (inclusion_injective A n)).trans
    (LinearEquiv.ofEq _ _ (range_inclusion A n))

@[simp]
theorem chainSubmoduleEquiv_coe (A : S.Subcomplex) (n : ℕ) (c : (complex (A : SSet)).X n) :
    (chainSubmoduleEquiv A n c : (complex S).X n) = (inclusion A).f n c := rfl

/-- The supported actual chain objects are closed under the original native boundary. -/
theorem boundary_mem_chainSubmodule (A : S.Subcomplex) (n : ℕ)
    (c : (complex S).X (n + 1)) (hc : c ∈ chainSubmodule A (n + 1)) :
    (complex S).d (n + 1) n c ∈ chainSubmodule A n := by
  rw [← range_inclusion] at hc ⊢
  obtain ⟨a, rfl⟩ := hc
  refine ⟨(complex (A : SSet)).d (n + 1) n a, ?_⟩
  exact (congrArg (fun f : (complex (A : SSet)).X (n + 1) ⟶ (complex S).X n ↦ f a)
    ((inclusion A).comm (n + 1) n)).symm

/-- Restricting the original native differential to the supported whole-chain submodule. -/
def boundary (A : S.Subcomplex) (n : ℕ) : chainSubmodule A (n + 1) →ₗ[ℚ] chainSubmodule A n :=
  (((complex S).d (n + 1) n).hom.comp (chainSubmodule A (n + 1)).subtype).codRestrict _
    (fun c ↦ boundary_mem_chainSubmodule A n c.val c.property)

/-- The supported-range equivalence commutes with the native differential on both sides. -/
theorem chainSubmoduleEquiv_boundary (A : S.Subcomplex) (n : ℕ)
    (c : (complex (A : SSet)).X (n + 1)) :
    boundary A n (chainSubmoduleEquiv A (n + 1) c) =
      chainSubmoduleEquiv A n ((complex (A : SSet)).d (n + 1) n c) := by
  apply Subtype.ext
  exact (congrArg (fun f : (complex (A : SSet)).X (n + 1) ⟶ (complex S).X n ↦ f c)
    ((inclusion A).comm (n + 1) n))

end HodgeConjecture.SubcomplexChainCoordinates
