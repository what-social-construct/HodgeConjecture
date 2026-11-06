module

import HodgeConjecture.Realization.Betti.SubcomplexCochains
import Lean.Util.CollectAxioms

/-!
Regression checks for actual rational cochains on unions and intersections.
The concrete three-point simplicial example has two overlapping pieces,
so its compatibility and signed difference are tested on a genuine overlap.
No topological excision or small-to-full comparison is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Opposite Simplicial
open HodgeConjecture.SubcomplexCochains

namespace SubcomplexCochainsVerification

/-- The constant simplicial set on three actual points. -/
def threePoints : SSet := (Functor.const _).obj (Fin 3)

/-- Points zero and one form the first simplicial subcomplex. -/
def firstTwo : threePoints.Subcomplex where
  obj _ := {i | i.val < 2}
  map _ _ h := h

/-- Points one and two form the second simplicial subcomplex. -/
def lastTwo : threePoints.Subcomplex where
  obj _ := {i | 0 < i.val}
  map _ _ h := h

-- These pieces really cover all three simplices in every degree.
example : firstTwo ⊔ lastTwo = ⊤ := by
  apply le_antisymm le_top
  intro n i _
  change i.val < 2 ∨ 0 < i.val
  omega

-- The overlap is the actual middle point, in every degree.
example (n : ℕ) (i : Fin 3) :
    i ∈ (firstTwo ⊓ lastTwo).obj (op ⦋n⦌) ↔ i = 1 := by
  change (i.val < 2 ∧ 0 < i.val) ↔ i = 1
  constructor
  · intro h
    apply Fin.ext
    dsimp
    omega
  · rintro rfl
    decide

-- First-minus-second fixes the signed convention before any connecting map is used.
example (n : ℕ) :
    coverDifferenceLinear firstTwo lastTwo n
      ((fun _ ↦ 2), (fun _ ↦ 5))
        ⟨(1 : Fin 3), by constructor <;> norm_num [firstTwo, lastTwo]⟩ = -3 := by
  rw [coverDifferenceLinear_apply]
  norm_num

-- Compatible restrictions reconstruct the actual function on the union.
example (n : ℕ) :
    coverRestrictionLinear firstTwo lastTwo n
      (glueFunction firstTwo lastTwo n ((fun _ ↦ 7), (fun _ ↦ 7))) =
        ((fun _ ↦ 7), (fun _ ↦ 7)) := by
  apply coverRestrictionLinear_glueFunction
  funext σ
  exact sub_self _

-- Every actual overlap cochain, including a nonzero one, is a restriction difference.
example (n : ℕ) :
    ∃ φ : PairCochain firstTwo lastTwo n,
      coverDifferenceLinear firstTwo lastTwo n φ = fun _ ↦ 11 :=
  coverDifferenceLinear_surjective firstTwo lastTwo n (fun _ ↦ 11)

example : (coverShortComplex firstTwo lastTwo).ShortExact :=
  coverShortComplex_shortExact firstTwo lastTwo

section General

universe u

variable (S : SSet.{u}) (A B : S.Subcomplex)

-- Restriction maps, not supplied cohomological maps, form the actual short exact complex.
example : coverRestriction A B ≫ coverDifference A B = 0 :=
  coverRestriction_comp_coverDifference A B

example (n : ℕ) :
    ((coverShortComplex A B).map (HomologicalComplex.eval _ _ n)).ShortExact :=
  coverShortComplex_degreewise_shortExact A B n

-- All three positions of the genuine long exact sequence are available.
example (n : ℕ) :
    ((coverShortComplex A B).map (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  homology_exact_pair A B n

example (n : ℕ) : connecting A B n ≫
    HomologicalComplex.homologyMap (coverRestriction A B) (n + 1) = 0 :=
  (coverShortComplex_shortExact A B).δ_comp n (n + 1) (by simp)

example (X : TopCat.{u}) :
    complex (TopCat.toSSet.obj X) ≅ HodgeConjecture.SingularCochains.complex X :=
  singularComplexIso X

example {X Y : TopCat.{u}} (f : X ⟶ Y) :
    pullback (TopCat.toSSet.map f) = HodgeConjecture.SingularCochains.pullback f :=
  singular_pullback f

end General

end SubcomplexCochainsVerification

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SubcomplexCochains.cosimplicial,
    `HodgeConjecture.SubcomplexCochains.complex,
    `HodgeConjecture.SubcomplexCochains.complex_d,
    `HodgeConjecture.SubcomplexCochains.differential_squared,
    `HodgeConjecture.SubcomplexCochains.pullback,
    `HodgeConjecture.SubcomplexCochains.pullback_comp,
    `HodgeConjecture.SubcomplexCochains.singularComplexIso,
    `HodgeConjecture.SubcomplexCochains.singular_pullback,
    `HodgeConjecture.SubcomplexCochains.restriction,
    `HodgeConjecture.SubcomplexCochains.pairDifferential_squared,
    `HodgeConjecture.SubcomplexCochains.pairComplex,
    `HodgeConjecture.SubcomplexCochains.coverRestriction,
    `HodgeConjecture.SubcomplexCochains.coverDifference,
    `HodgeConjecture.SubcomplexCochains.coverRestriction_comp_coverDifference,
    `HodgeConjecture.SubcomplexCochains.coverRestrictionLinear_injective,
    `HodgeConjecture.SubcomplexCochains.coverDifferenceLinear_surjective,
    `HodgeConjecture.SubcomplexCochains.glueFunction,
    `HodgeConjecture.SubcomplexCochains.coverRestrictionLinear_glueFunction,
    `HodgeConjecture.SubcomplexCochains.coverShortComplex_degreewise_shortExact,
    `HodgeConjecture.SubcomplexCochains.coverShortComplex_shortExact,
    `HodgeConjecture.SubcomplexCochains.connecting,
    `HodgeConjecture.SubcomplexCochains.homology_exact_union,
    `HodgeConjecture.SubcomplexCochains.homology_exact_pair,
    `HodgeConjecture.SubcomplexCochains.homology_exact_intersection]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
