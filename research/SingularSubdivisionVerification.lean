module

import HodgeConjecture.Realization.Betti.SingularSubdivisionHomology
import HodgeConjecture.Realization.Betti.SmallSingularSubdivisionHomotopy
import Lean.Util.CollectAxioms

/-!
Actual singular subdivision, its explicit homotopy, and the identity on
native rational homology in every degree. No sphere calculation or
small-chain homology equivalence is supplied to these examples.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HodgeConjecture HodgeConjecture.SingularSubdivision

example (X : TopCat) (c : (complex X).X 0) :
    (complex X).d 1 0 (homotopyComponent X 0 c) = c - subdivisionComponent X 0 c :=
  homotopyComponent_identity_zero X c

example (X : TopCat) (c : (complex X).X 2) :
    (complex X).d 3 2 (homotopyComponent X 2 c) +
      homotopyComponent X 1 ((complex X).d 2 1 c) = c - subdivisionComponent X 2 c :=
  homotopyComponent_identity X 1 c

example (X : TopCat) (c : (complex X).X 3) :
    (complex X).d 3 2 (subdivisionComponent X 3 c) =
      subdivisionComponent X 2 ((complex X).d 3 2 c) :=
  subdivisionComponent_boundary X 2 c

example (X : TopCat) : Homotopy (𝟙 (complex X)) (subdivision X) := subdivisionHomotopy X

-- The bundled native homotopy retains the exact original constructed component.
example (X : TopCat) :
    (subdivisionHomotopy X).hom 2 3 = ModuleCat.ofHom (homotopyComponent X 2) :=
  homotopyDegree_succ X 2

example (X : TopCat) : (subdivisionHomotopy X).hom 2 2 = 0 := by
  change homotopyDegree X 2 2 = 0
  simp [homotopyDegree]

example (X : TopCat) (n : ℕ) :
    HomologicalComplex.homologyMap (subdivision X) n = 𝟙 ((complex X).homology n) :=
  homologyMap_subdivision X n

example (X : TopCat) : IsIso (HomologicalComplex.homologyMap (subdivision X) 2) := by
  rw [homologyMap_subdivision]
  infer_instance

-- Literal rational homology classes are fixed, including non-integral scalar combinations.
example (X : TopCat) (c : (complex X).homology 2) :
    HomologicalComplex.homologyMap (subdivision X) 2 ((3 / 2 : ℚ) • c) = (3 / 2 : ℚ) • c := by
  rw [homologyMap_subdivision]
  rfl

example (X : TopCat) (k : ℕ) :
    HomologicalComplex.homologyMap (subdivisionPower X k) 2 = 𝟙 ((complex X).homology 2) :=
  homologyMap_subdivision_pow X k 2

example (X : TopCat) (k n : ℕ) (c : (complex X).X n) :
    (subdivisionPower X k).f n c =
      ((subdivisionComponent X n : (complex X).X n → (complex X).X n)^[k]) c :=
  subdivisionPower_apply X k n c

example (X : TopCat) : subdivisionPower X 0 = 𝟙 (complex X) := subdivisionPower_zero X

-- The restricted construction applies to arbitrary subsets, before any open-cover theorem.
example (X : TopCat) (U V : Set X) :
    Homotopy (𝟙 (smallComplex X U V)) (smallSubdivision X U V) :=
  smallSubdivisionHomotopy X U V

example (X : TopCat) (U V : Set X) :
    smallSubdivision X U V ≫ smallInclusion X U V =
      smallInclusion X U V ≫ subdivision X := smallSubdivision_inclusion X U V

example (X : TopCat) (U V : Set X) (k : ℕ) :
    smallSubdivisionPower X U V k ≫ smallInclusion X U V =
      smallInclusion X U V ≫ subdivisionPower X k := smallSubdivisionPower_inclusion X U V k

example (X : TopCat) (U V : Set X) (k : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivisionPower X U V k) 2 =
      𝟙 ((smallComplex X U V).homology 2) := homologyMap_smallSubdivision_pow X U V k 2

example (X : TopCat) (U V : Set X) (c : (smallComplex X U V).X 0) :
    (smallComplex X U V).d 1 0 (smallHomotopyComponent X U V 0 c) =
      c - smallSubdivisionComponent X U V 0 c := smallHomotopyComponent_identity_zero X U V c

example (X : TopCat) (U V : Set X) (c : (smallComplex X U V).X 2) :
    (smallInclusion X U V).f 3 (smallHomotopyComponent X U V 2 c) =
      homotopyComponent X 2 ((smallInclusion X U V).f 2 c) :=
  inclusion_smallHomotopyComponent X U V 2 c

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SingularSubdivision.centers,
    `HodgeConjecture.SingularSubdivision.centers_map,
    `HodgeConjecture.SingularSubdivision.simplex,
    `HodgeConjecture.SingularSubdivision.simplex_face,
    `HodgeConjecture.SingularSubdivision.realize,
    `HodgeConjecture.SingularSubdivision.realize_single,
    `HodgeConjecture.SingularSubdivision.realize_boundary,
    `HodgeConjecture.SingularSubdivision.realize_target_map,
    `HodgeConjecture.SingularSubdivision.realize_reference,
    `HodgeConjecture.SingularSubdivision.boundary_reference,
    `HodgeConjecture.SingularSubdivision.subdividedSimplex,
    `HodgeConjecture.SingularSubdivision.subdivisionComponent,
    `HodgeConjecture.SingularSubdivision.boundary_subdividedSimplex,
    `HodgeConjecture.SingularSubdivision.subdivisionComponent_boundary,
    `HodgeConjecture.SingularSubdivision.subdivision,
    `HodgeConjecture.SingularSubdivision.homotopySimplex,
    `HodgeConjecture.SingularSubdivision.homotopyComponent,
    `HodgeConjecture.SingularSubdivision.homotopyComponent_coordinates_single,
    `HodgeConjecture.SingularSubdivision.realize_homotopy_boundary_reference,
    `HodgeConjecture.SingularSubdivision.boundary_homotopySimplex,
    `HodgeConjecture.SingularSubdivision.boundary_homotopySimplex_zero,
    `HodgeConjecture.SingularSubdivision.chainLinearMap_ext,
    `HodgeConjecture.SingularSubdivision.homotopyComponent_identity,
    `HodgeConjecture.SingularSubdivision.homotopyComponent_identity_zero,
    `HodgeConjecture.SingularSubdivision.homotopyDegree,
    `HodgeConjecture.SingularSubdivision.homotopyDegree_succ,
    `HodgeConjecture.SingularSubdivision.subdivisionHomotopy,
    `HodgeConjecture.SingularSubdivision.homologyMap_subdivision,
    `HodgeConjecture.SingularSubdivision.subdivisionPower,
    `HodgeConjecture.SingularSubdivision.subdivisionPower_zero,
    `HodgeConjecture.SingularSubdivision.subdivisionPower_succ,
    `HodgeConjecture.SingularSubdivision.homologyMap_subdivision_pow,
    `HodgeConjecture.SingularSubdivision.subdivisionPower_apply,
    `HodgeConjecture.SingularSubdivision.smallChains_eq_chainSubmodule,
    `HodgeConjecture.SingularSubdivision.original_range_small,
    `HodgeConjecture.SingularSubdivision.homotopySimplex_mem_small,
    `HodgeConjecture.SingularSubdivision.homotopyComponent_mem_small,
    `HodgeConjecture.SingularSubdivision.restrictSmallOperator,
    `HodgeConjecture.SingularSubdivision.inclusion_restrictSmallOperator,
    `HodgeConjecture.SingularSubdivision.smallInclusion_boundary,
    `HodgeConjecture.SingularSubdivision.smallSubdivisionComponent,
    `HodgeConjecture.SingularSubdivision.smallSubdivision,
    `HodgeConjecture.SingularSubdivision.smallSubdivision_inclusion,
    `HodgeConjecture.SingularSubdivision.smallHomotopyComponent,
    `HodgeConjecture.SingularSubdivision.inclusion_smallHomotopyComponent,
    `HodgeConjecture.SingularSubdivision.smallHomotopyComponent_identity_zero,
    `HodgeConjecture.SingularSubdivision.smallHomotopyComponent_identity,
    `HodgeConjecture.SingularSubdivision.smallSubdivisionHomotopy,
    `HodgeConjecture.SingularSubdivision.homologyMap_smallSubdivision,
    `HodgeConjecture.SingularSubdivision.smallSubdivisionPower_inclusion,
    `HodgeConjecture.SingularSubdivision.homologyMap_smallSubdivision_pow]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
