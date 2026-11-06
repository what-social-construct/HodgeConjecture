module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Finite coordinates on the original rational singular chain complex

The chain objects here are Mathlib's original coproduct objects. Their
finite-support coordinates are the canonical coproduct comparison, with
the standard alternating boundary formula proved on actual injections.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularChainCoordinates

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-- The original rational simplicial chain complex. -/
abbrev complex (S : SSet.{0}) := S.chainComplex (ModuleCat.of ℚ ℚ)

/-- The canonical finite-support realization of the native coproduct in each degree. -/
def coordinateIso (S : SSet.{0}) (n : ℕ) :
    ModuleCat.of ℚ (S.obj (op ⦋n⦌) →₀ ℚ) ≅ (complex S).X n :=
  (ModuleCat.finsuppCoconeIsColimit ℚ ℚ (S.obj (op ⦋n⦌))).coconePointUniqueUpToIso
    (S.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n)

@[reassoc (attr := simp)]
theorem lsingle_coordinateIso_hom (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n⦌)) :
    ModuleCat.ofHom (Finsupp.lsingle σ (R := ℚ) (M := ℚ)) ≫ (coordinateIso S n).hom =
      S.ιChainComplex σ :=
  (ModuleCat.finsuppCoconeIsColimit ℚ ℚ (S.obj (op ⦋n⦌))).comp_coconePointUniqueUpToIso_hom
    (S.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n) (Discrete.mk σ)

/-- A proved coordinate equivalence, rather than an alternative chain complex. -/
def coordinates (S : SSet.{0}) (n : ℕ) :
    (S.obj (op ⦋n⦌) →₀ ℚ) ≃ₗ[ℚ] (complex S).X n :=
  (coordinateIso S n).toLinearEquiv

@[simp]
theorem coordinates_single (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n⦌)) (a : ℚ) :
    coordinates S n (Finsupp.single σ a) = (S.ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) a :=
  congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ (complex S).X n ↦ f a)
    (lsingle_coordinateIso_hom S n σ)

/-- The alternating simplicial boundary, expressed in finite-support coordinates. -/
def boundary (S : SSet.{0}) (n : ℕ) :
    (S.obj (op ⦋n + 1⦌) →₀ ℚ) →ₗ[ℚ] (S.obj (op ⦋n⦌) →₀ ℚ) :=
  Finsupp.linearCombination ℚ fun σ ↦
    ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) • Finsupp.single (S.δ i σ) 1

@[simp]
theorem boundary_single (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n + 1⦌)) (a : ℚ) :
    boundary S n (Finsupp.single σ a) =
      ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) • Finsupp.single (S.δ i σ) a := by
  simp [boundary, Finset.smul_sum, mul_comm]

/-- The coordinate differential is exactly the native chain differential. -/
theorem coordinates_boundary (S : SSet.{0}) (n : ℕ) (c : S.obj (op ⦋n + 1⦌) →₀ ℚ) :
    (complex S).d (n + 1) n (coordinates S (n + 1) c) =
      coordinates S n (boundary S n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single σ a =>
    have h := congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ (complex S).X n ↦ f a)
      (S.ιChainComplex_d (R := ModuleCat.of ℚ ℚ) σ)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, coordinates_single,
      boundary_single, map_sum, map_smul,
      ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one] using h

end HodgeConjecture.SingularChainCoordinates
