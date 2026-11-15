module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section

/-!
# Rational cochains on a simplicial set

Rational functions on the simplices form a cosimplicial module. Its
alternating coface complex, differential and contravariant pullback are
constructed here once. Singular cochains specialize this construction to
the singular set of a topological space; subcomplex cochains apply it to
the actual subcomplex simplicial sets.
-/

set_option autoImplicit false

namespace HodgeConjecture.SimplicialCochains

open CategoryTheory Simplicial Opposite

noncomputable section

universe u

/-- Rational functions, contravariant in their actual indexing set. -/
def functionModule : (Type u)ᵒᵖ ⥤ ModuleCat.{u} ℚ where
  obj S := ModuleCat.of ℚ (S.unop → ℚ)
  map f := ModuleCat.ofHom
    { toFun := fun φ s ↦ φ (f.unop s)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Unrestricted rational functions on the actual degree-`n` simplices. -/
abbrev Cochain (S : SSet.{u}) (n : ℕ) := S.obj (op ⦋n⦌) → ℚ

/-- Actual rational simplex functions as a cosimplicial module. -/
def cosimplicial (S : SSet.{u}) : CosimplicialObject (ModuleCat.{u} ℚ) :=
  S.rightOp ⋙ functionModule

/-- The alternating coface complex of actual rational functions. -/
def complex (S : SSet.{u}) : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cosimplicial S)

/-- The alternating differential as a linear map on actual cochains. -/
def differential (S : SSet.{u}) (n : ℕ) : Cochain S n →ₗ[ℚ] Cochain S (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimplicial S) n).hom

@[simp]
theorem complex_d (S : SSet.{u}) (n : ℕ) :
    (complex S).d n (n + 1) = ModuleCat.ofHom (differential S n) := by
  simp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rfl

/-- The differential evaluates as the alternating sum over the original faces. -/
theorem differential_apply (S : SSet.{u}) (n : ℕ)
    (φ : Cochain S n) (σ : S.obj (op ⦋n + 1⦌)) :
    differential S n φ σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (S.δ i σ) := by
  simp [differential, AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    cosimplicial, functionModule, CosimplicialObject.δ, SimplicialObject.δ]

/-- The square-zero identity comes from the simplicial identities. -/
theorem differential_squared (S : SSet.{u}) (n : ℕ) (φ : Cochain S n) :
    differential S (n + 1) (differential S n φ) = 0 :=
  congrArg (fun f ↦ f.hom φ)
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cosimplicial S) n)

/-- Precomposition along an actual simplicial map, before taking the complex. -/
def cosimplicialPullback {S T : SSet.{u}} (f : S ⟶ T) :
    cosimplicial T ⟶ cosimplicial S :=
  Functor.whiskerRight f.rightOp functionModule

/-- Contravariant cochain pullback along an actual simplicial map. -/
def pullback {S T : SSet.{u}} (f : S ⟶ T) : complex T ⟶ complex S :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).map (cosimplicialPullback f)

@[simp]
theorem pullback_apply {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ)
    (φ : Cochain T n) (σ : S.obj (op ⦋n⦌)) :
    (pullback f).f n φ σ = φ (f.app (op ⦋n⦌) σ) := rfl

@[simp]
theorem pullback_id (S : SSet.{u}) : pullback (𝟙 S) = 𝟙 (complex S) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

@[simp]
theorem pullback_comp {S T U : SSet.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    pullback (f ≫ g) = pullback g ≫ pullback f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

/-- Pullback commutes with the original alternating differential. -/
theorem differential_pullback {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ)
    (φ : Cochain T n) :
    differential S n ((pullback f).f n φ) =
      (pullback f).f (n + 1) (differential T n φ) := by
  have h := (pullback f).comm n (n + 1)
  rw [complex_d, complex_d] at h
  exact congrArg (fun g ↦ g.hom φ) h

end

end HodgeConjecture.SimplicialCochains
