module

public import HodgeConjecture.Realization.Betti.SingularSubcomplexes
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Contained singular simplices retain the actual subtype topology and all
simplicial restrictions. In particular, a two-open cover covers every
zero-simplex but need not contain a crossing one-simplex in either member.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open HodgeConjecture.SingularSubcomplexes

noncomputable section

universe u

example (X : TopCat.{u}) (U : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (subsetSingular X U).obj n ↔
      Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ U :=
  mem_subsetSingular_iff_range X U n σ

example (X : TopCat.{u}) (U : Set X) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) (hσ : σ ∈ (subsetSingular X U).obj n) :
    (TopCat.toSSet.obj X).map f σ ∈ (subsetSingular X U).obj m :=
  (subsetSingular X U).map f hσ

example (X : TopCat.{u}) (U V : Set X) :
    subsetSingular X (U ∩ V) = subsetSingular X U ⊓ subsetSingular X V :=
  subsetSingular_inter X U V

example (X : TopCat.{u}) (U : Set X) :
    (subsetSingularIso X U).inv ≫ (subsetSingular X U).ι =
      TopCat.toSSet.map (subsetInclusion X U) := subtypeToSubset_ι X U

example (X : TopCat.{u}) (U V : Set X) (hUV : U ∪ V = Set.univ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) :
    σ ∈ (smallSingular X U V).obj (op ⦋0⦌) :=
  zeroSimplex_mem_smallSingular X U V hUV σ

example (X : TopCat.{u}) (U : Set X) : subsetSingular X (∅ ∩ U) = ⊥ := by simp

namespace SingularSubcomplexVerification

/-- Two genuine open sets covering the real line. -/
def leftOpen : Set ℝ := Set.Iio (2 / 3)
def rightOpen : Set ℝ := Set.Ioi (1 / 3)

theorem leftOpen_isOpen : IsOpen leftOpen := isOpen_Iio
theorem rightOpen_isOpen : IsOpen rightOpen := isOpen_Ioi

theorem twoOpen_cover : leftOpen ∪ rightOpen = Set.univ := by
  ext x
  simp only [leftOpen, rightOpen, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ,
    iff_true]
  by_cases hx : x < 2 / 3
  · exact Or.inl hx
  · exact Or.inr (by linarith)

/-- The actual singular interval taking its two vertices to zero and one. -/
def crossingSimplex :
    (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) :=
  ⟨TopCat.ofHom
    ⟨fun t : SimplexCategory.toTop.obj ⦋1⦌ ↦ t.down.weights 1,
      (Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).comp continuous_uliftDown⟩⟩

theorem crossingSimplex_not_small :
    crossingSimplex ∉ (smallSingular (TopCat.of ℝ) leftOpen rightOpen).obj (op ⦋1⦌) := by
  intro h
  rcases h with hL | hR
  · have ht := hL (ULift.up (Convexity.StdSimplex.single (1 : Fin 2)))
    change (Convexity.StdSimplex.single (1 : Fin 2)).weights 1 < (2 / 3 : ℝ) at ht
    norm_num at ht
  · have ht := hR (ULift.up (Convexity.StdSimplex.single (0 : Fin 2)))
    change (1 / 3 : ℝ) < (Convexity.StdSimplex.single (0 : Fin 2)).weights 1 at ht
    norm_num at ht

-- Even an open cover does not identify its small singular subcomplex with all simplices.
example : smallSingular (TopCat.of ℝ) leftOpen rightOpen ≠ ⊤ := by
  intro h
  apply crossingSimplex_not_small
  rw [h]
  trivial

example : subsetSingular (TopCat.of ℝ) (leftOpen ∪ rightOpen) = ⊤ := by
  rw [twoOpen_cover, subsetSingular_univ]

end SingularSubcomplexVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularSubcomplexes.subsetSingular,
      `HodgeConjecture.SingularSubcomplexes.mem_subsetSingular_iff_range,
      `HodgeConjecture.SingularSubcomplexes.subsetSingular_mono,
      `HodgeConjecture.SingularSubcomplexes.subsetMap,
      `HodgeConjecture.SingularSubcomplexes.subsetMap_ι,
      `HodgeConjecture.SingularSubcomplexes.subsetSingular_inter,
      `HodgeConjecture.SingularSubcomplexes.subsetSingular_empty,
      `HodgeConjecture.SingularSubcomplexes.subsetSingularIso,
      `HodgeConjecture.SingularSubcomplexes.subtypeToSubset_ι,
      `HodgeConjecture.SingularSubcomplexes.mem_smallSingular,
      `HodgeConjecture.SingularSubcomplexes.smallSingular_le_union,
      `HodgeConjecture.SingularSubcomplexes.zeroSimplex_mem_smallSingular,
      `HodgeConjecture.SingularSubcomplexes.smallSingular_isPushout,
      `SingularSubcomplexVerification.twoOpen_cover,
      `SingularSubcomplexVerification.crossingSimplex_not_small] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
