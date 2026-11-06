module

public import HodgeConjecture.Realization.Betti.AffineSingularRealization
public import HodgeConjecture.Realization.Betti.SingularCochains
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Finite coordinates are proved coordinates on Mathlib's original chain
objects. These checks compare actual boundaries, affine vertices, convex
support and the dual differential of the existing singular cochains.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HodgeConjecture
open AffineSingularRealization

namespace AffineSingularVerification

noncomputable section

example (S : SSet.{0}) (n : ℕ) (c : S.obj (op ⦋n⦌) →₀ ℚ) :
    (SingularChainCoordinates.coordinates S n).symm
      (SingularChainCoordinates.coordinates S n c) = c :=
  (SingularChainCoordinates.coordinates S n).symm_apply_apply c

example (S : SSet.{0}) (n : ℕ) (c : (SingularChainCoordinates.complex S).X n) :
    SingularChainCoordinates.coordinates S n
      ((SingularChainCoordinates.coordinates S n).symm c) = c :=
  (SingularChainCoordinates.coordinates S n).apply_symm_apply c

example (S : SSet.{0}) (n : ℕ) (c : S.obj (op ⦋n + 1⦌) →₀ ℚ) :
    (SingularChainCoordinates.complex S).d (n + 1) n
      (SingularChainCoordinates.coordinates S (n + 1) c) =
        SingularChainCoordinates.coordinates S n (SingularChainCoordinates.boundary S n c) :=
  SingularChainCoordinates.coordinates_boundary S n c

-- The one-simplex boundary retains terminal-minus-initial orientation.
example (S : SSet.{0}) (σ : S.obj (op ⦋1⦌)) :
    SingularChainCoordinates.boundary S 0 (Finsupp.single σ 1) =
      Finsupp.single (S.δ (0 : Fin 2) σ) 1 - Finsupp.single (S.δ (1 : Fin 2) σ) 1 := by
  simp [SingularChainCoordinates.boundary_single, Fin.sum_univ_two, sub_eq_add_neg]

/-- Pair an actual finite chain coordinate with a rational cochain. -/
def pairing (S : SSet.{0}) (n : ℕ) (φ : S.obj (op ⦋n⦌) → ℚ) :
    (S.obj (op ⦋n⦌) →₀ ℚ) →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ φ

/-- The already constructed rational singular coboundary is exactly dual to the
native singular chain boundary, through the proved finite coordinates. -/
theorem pairing_boundary (X : TopCat.{0}) (n : ℕ) (φ : SingularCochains.Cochain X n)
    (c : SingularCochains.Simplex X (n + 1) →₀ ℚ) :
    pairing (TopCat.toSSet.obj X) n φ (SingularChainCoordinates.boundary (TopCat.toSSet.obj X) n c) =
      pairing (TopCat.toSSet.obj X) (n + 1) (SingularCochains.differential X n φ) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using congrArg₂ (· + ·) hc hd
  | single σ a =>
    simp [pairing, SingularChainCoordinates.boundary_single, SingularCochains.differential_apply,
      SingularCochains.face, SimplicialObject.δ, Finset.mul_sum,
      mul_assoc, mul_comm]

def lineVertices : Fin 2 → ℝ := ![0, 1]

example : TopCat.toSSetObjEquiv (TopCat.of ℝ) (op ⦋1⦌) (simplex 1 lineVertices)
    (.single 0) = 0 := by
  rw [simplex_continuous, SubdivisionGeometry.realization_single]
  rfl

example : TopCat.toSSetObjEquiv (TopCat.of ℝ) (op ⦋1⦌) (simplex 1 lineVertices)
    (.single 1) = 1 := by
  rw [simplex_continuous, SubdivisionGeometry.realization_single]
  rfl

example : simplex 1 lineVertices ≠ simplex 1 (fun _ ↦ (0 : ℝ)) := by
  intro h
  have hv := simplex_injective 1 h
  have h1 := congrFun hv 1
  norm_num [lineVertices] at h1

example (c : AffineSimplexChains.Chain ℝ 3) :
    (singularComplex ℝ).d 2 1 (chainRealization 2 c) =
      chainRealization 1 (AffineSimplexChains.boundary ℝ 2 c) :=
  chainRealization_boundary 1 c

example (c : AffineSimplexChains.Chain ℝ 2) (hc : chainRealization 1 c = 0) : c = 0 := by
  apply chainRealization_injective 1
  simpa using hc

example : simplex 1 lineVertices ∈
    (SingularSubcomplexes.subsetSingular (TopCat.of ℝ) (Set.Icc 0 1)).obj (op ⦋1⦌) := by
  apply simplex_mem_subset (convex_Icc 0 1) 1 lineVertices
  intro i
  fin_cases i <;> norm_num [lineVertices]

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularChainCoordinates.coordinateIso,
      `HodgeConjecture.SingularChainCoordinates.lsingle_coordinateIso_hom,
      `HodgeConjecture.SingularChainCoordinates.coordinates,
      `HodgeConjecture.SingularChainCoordinates.coordinates_single,
      `HodgeConjecture.SingularChainCoordinates.boundary,
      `HodgeConjecture.SingularChainCoordinates.boundary_single,
      `HodgeConjecture.SingularChainCoordinates.coordinates_boundary,
      `HodgeConjecture.AffineSingularRealization.simplex,
      `HodgeConjecture.AffineSingularRealization.simplex_face,
      `HodgeConjecture.AffineSingularRealization.simplex_injective,
      `HodgeConjecture.AffineSingularRealization.chainRealization,
      `HodgeConjecture.AffineSingularRealization.chainRealization_single,
      `HodgeConjecture.AffineSingularRealization.chainRealization_injective,
      `HodgeConjecture.AffineSingularRealization.chainRealization_boundary,
      `HodgeConjecture.AffineSingularRealization.simplex_mem_subset,
      `AffineSingularVerification.pairing_boundary] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end

end AffineSingularVerification
