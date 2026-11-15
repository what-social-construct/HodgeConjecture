module

public import HodgeConjecture.Realization.Betti.SubcomplexCochains
public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section

/-!
# Actual cochain coordinates on the dual of native rational chains

The canonical native coproduct coordinates and the free-module universal
property identify every algebraic functional on the original chain module
with an unrestricted rational function on actual simplices. The original
chain differential is dual to the actual alternating coface differential,
and the identification is natural for original simplicial maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CochainDualCoordinates

open CategoryTheory Opposite Simplicial

/-- The original simplex-function coordinates on the algebraic dual of native chains. -/
def coordinates (S : SSet.{0}) (n : ℕ) :
    Module.Dual ℚ ((SingularChainCoordinates.complex S).X n) ≃ₗ[ℚ]
      SubcomplexCochains.Cochain S n :=
  (SingularChainCoordinates.coordinates S n).dualMap.trans
    (Finsupp.llift ℚ ℚ ℚ (S.obj (op ⦋n⦌))).symm

@[simp]
theorem coordinates_apply (S : SSet.{0}) (n : ℕ)
    (φ : Module.Dual ℚ ((SingularChainCoordinates.complex S).X n))
    (σ : S.obj (op ⦋n⦌)) :
    coordinates S n φ σ = φ (SingularChainCoordinates.coordinates S n (Finsupp.single σ 1)) :=
  rfl

theorem coordinates_symm_apply (S : SSet.{0}) (n : ℕ)
    (φ : SubcomplexCochains.Cochain S n) (c : (SingularChainCoordinates.complex S).X n) :
    (coordinates S n).symm φ c =
      Finsupp.llift ℚ ℚ ℚ (S.obj (op ⦋n⦌)) φ
        ((SingularChainCoordinates.coordinates S n).symm c) := rfl

@[simp]
theorem coordinates_symm_coordinates_single (S : SSet.{0}) (n : ℕ)
    (φ : SubcomplexCochains.Cochain S n) (σ : S.obj (op ⦋n⦌)) (a : ℚ) :
    (coordinates S n).symm φ (SingularChainCoordinates.coordinates S n (Finsupp.single σ a)) =
      a * φ σ := by
  rw [coordinates_symm_apply, LinearEquiv.symm_apply_apply]
  simp [Finsupp.llift_apply, Finsupp.lift_apply]

/-- The cochain differential is the actual alternating original simplex-face formula. -/
theorem differential_apply (S : SSet.{0}) (n : ℕ)
    (φ : SubcomplexCochains.Cochain S n) (σ : S.obj (op ⦋n + 1⦌)) :
    SubcomplexCochains.differential S n φ σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (S.δ i σ) :=
  SimplicialCochains.differential_apply S n φ σ

/-- The dual of the original native chain boundary is the actual cochain coboundary. -/
theorem coordinates_differential (S : SSet.{0}) (n : ℕ)
    (φ : Module.Dual ℚ ((SingularChainCoordinates.complex S).X n)) :
    coordinates S (n + 1)
      (((SingularChainCoordinates.complex S).d (n + 1) n).hom.dualMap φ) =
        SubcomplexCochains.differential S n (coordinates S n φ) := by
  funext σ
  rw [coordinates_apply, LinearMap.dualMap_apply,
    SingularChainCoordinates.coordinates_boundary, SingularChainCoordinates.boundary_single]
  simp only [map_sum, map_smul, differential_apply, coordinates_apply,
    ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Actual simplicial pullback is the dual of the native chain map. -/
theorem coordinates_naturality {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (φ : Module.Dual ℚ ((SingularChainCoordinates.complex T).X n)) :
    coordinates S n (((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n).hom.dualMap φ) =
      (SubcomplexCochains.pullback f).f n (coordinates T n φ) := by
  funext σ
  rw [coordinates_apply, LinearMap.dualMap_apply, SubcomplexChainCoordinates.coordinates_map]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    SubcomplexCochains.pullback_apply, coordinates_apply]

end HodgeConjecture.CochainDualCoordinates
