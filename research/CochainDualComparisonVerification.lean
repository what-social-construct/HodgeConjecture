module

public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Actual unrestricted rational duals, original differential signs, simplicial
map naturality and two-open singular cochain comparison. The constant
simplicial set on ℕ tests genuinely infinite simplex indexing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Opposite Simplicial HomologicalComplex
open HodgeConjecture CochainDualCoordinates CochainDualComparison

namespace CochainDualComparisonVerification

/-- Actual infinitely many simplices in every degree. -/
abbrev naturalPoints : SSet.{0} :=
  (CategoryTheory.Functor.const (SimplexCategoryᵒᵖ)).obj (ℕ : Type)

/-- The original simplicial map translating every indexing point. -/
def successorMap : naturalPoints ⟶ naturalPoints where
  app _ := ↾Nat.succ
  naturality _ _ _ := rfl

-- A cochain may be nonzero on every simplex in an infinite indexing set.
example (k : ℕ) :
    coordinates naturalPoints 3 ((coordinates naturalPoints 3).symm (fun _ ↦ 1)) k = 1 := by
  rw [LinearEquiv.apply_symm_apply]

example (k : ℕ) :
    (coordinates naturalPoints 3).symm (fun _ ↦ 1)
      (SingularChainCoordinates.coordinates naturalPoints 3 (Finsupp.single k 7)) = 7 := by
  rw [coordinates_symm_coordinates_single, mul_one]

-- Its functional evaluates actual finite chains in the native coproduct.
example : (coordinates naturalPoints 3).symm (fun _ ↦ 1)
    (SingularChainCoordinates.coordinates naturalPoints 3
      (Finsupp.single (17 : ℕ) 2 + Finsupp.single (5 : ℕ) (-3))) = -1 := by
  rw [map_add, map_add, coordinates_symm_coordinates_single,
    coordinates_symm_coordinates_single]
  norm_num

-- Contravariant naturality uses the actual simplicial successor map.
example : (SubcomplexCochains.pullback successorMap).f 2
    (fun k ↦ ((show ℕ from k) : ℚ)) (17 : ℕ) = 18 := by
  rfl

example : (comparisonIso naturalPoints).hom.f 2
    ((coordinates naturalPoints 2).symm (fun k ↦ ((show ℕ from k) : ℚ))) (17 : ℕ) = 17 := by
  rw [comparisonIso_hom_f_apply, LinearEquiv.apply_symm_apply]
  norm_num

example {S T : SSet.{0}} (f : S ⟶ T) :
    RationalDual.dualMap (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)) ≫ (comparisonIso S).hom =
      (comparisonIso T).hom ≫ SubcomplexCochains.pullback f := comparisonIso_naturality f

-- The original +,- signs are preserved at the first positive coboundary.
example (S : SSet.{0}) (φ : Module.Dual ℚ ((SingularChainCoordinates.complex S).X 0))
    (σ : S.obj (op ⦋1⦌)) :
    coordinates S 1 (((SingularChainCoordinates.complex S).d 1 0).hom.dualMap φ) σ =
      coordinates S 0 φ (S.δ 0 σ) - coordinates S 0 φ (S.δ 1 σ) := by
  rw [coordinates_differential, differential_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

example (S : SSet.{0}) (φ : Module.Dual ℚ ((SingularChainCoordinates.complex S).X 1))
    (σ : S.obj (op ⦋2⦌)) :
    coordinates S 2 (((SingularChainCoordinates.complex S).d 2 1).hom.dualMap φ) σ =
      coordinates S 1 φ (S.δ 0 σ) - coordinates S 1 φ (S.δ 1 σ) +
        coordinates S 1 φ (S.δ 2 σ) := by
  rw [coordinates_differential, differential_apply, Fin.sum_univ_three]
  simp
  abel

example (X : TopCat.{0}) : QuasiIso (smallRestriction X Set.univ ∅) :=
  smallRestriction_quasiIso X Set.univ ∅ isOpen_univ isOpen_empty (by simp)

example : QuasiIso (smallRestriction (TopCat.of Empty) ∅ ∅) :=
  smallRestriction_quasiIso (TopCat.of Empty) ∅ ∅ isOpen_empty isOpen_empty
    (by ext x; exact x.elim)

/-- A genuine nontrivial open cover of the real line. -/
public theorem real_cover : Set.Iio (1 : ℝ) ∪ Set.Ioi (-1 : ℝ) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ, iff_true]
  by_cases h : x < 1
  · exact Or.inl h
  · exact Or.inr (by linarith)

example : QuasiIso (smallRestriction (TopCat.of ℝ) (Set.Iio 1) (Set.Ioi (-1))) :=
  smallRestriction_quasiIso (TopCat.of ℝ) _ _ isOpen_Iio isOpen_Ioi real_cover

example (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    (smallCohomologyIso X U V hU hV hcover 2).hom =
      homologyMap (smallRestriction X U V) 2 := smallCohomologyIso_hom X U V hU hV hcover 2

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CochainDualCoordinates.coordinates,
      `HodgeConjecture.CochainDualCoordinates.coordinates_apply,
      `HodgeConjecture.CochainDualCoordinates.coordinates_symm_apply,
      `HodgeConjecture.CochainDualCoordinates.coordinates_symm_coordinates_single,
      `HodgeConjecture.CochainDualCoordinates.differential_apply,
      `HodgeConjecture.CochainDualCoordinates.coordinates_differential,
      `HodgeConjecture.CochainDualCoordinates.coordinates_naturality,
      `HodgeConjecture.CochainDualComparison.comparisonIso,
      `HodgeConjecture.CochainDualComparison.comparisonIso_hom_f_apply,
      `HodgeConjecture.CochainDualComparison.comparisonIso_naturality,
      `HodgeConjecture.CochainDualComparison.pullback_eq_dualMap,
      `HodgeConjecture.CochainDualComparison.pullback_quasiIso,
      `HodgeConjecture.CochainDualComparison.smallRestriction,
      `HodgeConjecture.CochainDualComparison.smallRestriction_apply,
      `HodgeConjecture.CochainDualComparison.smallRestriction_quasiIso,
      `HodgeConjecture.CochainDualComparison.smallCohomologyIso,
      `HodgeConjecture.CochainDualComparison.smallCohomologyIso_hom,
      `CochainDualComparisonVerification.real_cover] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"

end CochainDualComparisonVerification
