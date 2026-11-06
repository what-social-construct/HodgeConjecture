module

import HodgeConjecture.Realization.Betti.NativeSimplexGeometry
import Lean.Util.CollectAxioms

/-!
Native-simplex topology, affine face compatibility and actual barycenters.
The cover-radius statements below use genuine openness and compactness;
they do not assume metric compatibility or a desired subdivision bound.
-/

set_option autoImplicit false

noncomputable section

open Convexity HodgeConjecture.NativeSimplexGeometry

-- The original native simplex, with its original topology, realizes its own vertices as identity.
example (n : ℕ) :
    realization (StdSimplex.single (R := ℝ) (X := Fin (n + 1))) = ContinuousMap.id _ :=
  realization_vertices

-- Every actual affine face restriction deletes precisely the requested vertex.
example (m n : ℕ) (v : Fin (n + 2) → StdSimplex ℝ (Fin (m + 1)))
    (i : Fin (n + 2)) (t : StdSimplex ℝ (Fin (n + 1))) :
    realization v (StdSimplex.map i.succAbove t) = realization (i.removeNth v) t :=
  realization_face n v i t

-- Constant vertex tuples really give constant native maps, including at arbitrary weights.
example (t : StdSimplex ℝ (Fin 3)) :
    realization (fun _ : Fin 3 ↦ (StdSimplex.single (R := ℝ) (1 : Fin 2))) t =
      StdSimplex.single 1 := by
  exact iConvexComb_const t _

-- The two-vertex center retains both coordinate halves.
example : (center (StdSimplex.single (R := ℝ) (X := Fin 2))).weights 0 = 1 / 2 := by
  rw [center_vertices, StdSimplex.weights_barycenter_apply]
  norm_num

-- A face barycenter remains in that actual face, rather than acquiring an extra coordinate.
example : (center (fun i : Fin 2 ↦ StdSimplex.single (R := ℝ) i.castSucc)).weights
      (2 : Fin 3) = 0 := by
  rw [center_weights, Fin.sum_univ_two]
  norm_num [StdSimplex.weights_single]

example (m n : ℕ) (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) :
    ((center v).weights : Fin (m + 1) → ℝ) =
      (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ • ∑ i, ((v i).weights : Fin (m + 1) → ℝ) :=
  center_weights_vector v

-- Target face embeddings preserve the actual chosen centers.
example (m n : ℕ) (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1)))
    (j : Fin (m + 2)) :
    StdSimplex.map j.succAbove (center v) =
      center (fun i ↦ StdSimplex.map j.succAbove (v i)) :=
  center_target_map v j.succAbove

example (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
    (coordinateHomeomorph t).val = (t.weights : Fin (n + 1) → ℝ) :=
  coordinateHomeomorph_val t

example (n : ℕ) (U V : Set (StdSimplex ℝ (Fin (n + 1))))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ ε > 0, ∀ p : StdSimplex ℝ (Fin (n + 1)),
      ({q : StdSimplex ℝ (Fin (n + 1)) |
        dist (q.weights : Fin (n + 1) → ℝ) (p.weights : Fin (n + 1) → ℝ) < ε} ⊆ U) ∨
      ({q : StdSimplex ℝ (Fin (n + 1)) |
        dist (q.weights : Fin (n + 1) → ℝ) (p.weights : Fin (n + 1) → ℝ) < ε} ⊆ V) :=
  lebesgue_number_two U V hU hV hcover

example (n : ℕ) (U V : Set (StdSimplex ℝ (Fin (n + 1))))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ ε > 0, ∀ s : Set (StdSimplex ℝ (Fin (n + 1))), s.Nonempty →
      Metric.diam ((fun t : StdSimplex ℝ (Fin (n + 1)) ↦
        (t.weights : Fin (n + 1) → ℝ)) '' s) < ε → s ⊆ U ∨ s ⊆ V :=
  lebesgue_number_two_diam U V hU hV hcover

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.NativeSimplexGeometry.weights_affineMapMk,
    `HodgeConjecture.NativeSimplexGeometry.weights_affineMapMk_apply,
    `HodgeConjecture.NativeSimplexGeometry.continuous_affineMapMk,
    `HodgeConjecture.NativeSimplexGeometry.realization,
    `HodgeConjecture.NativeSimplexGeometry.realization_single,
    `HodgeConjecture.NativeSimplexGeometry.realization_weights,
    `HodgeConjecture.NativeSimplexGeometry.realization_map,
    `HodgeConjecture.NativeSimplexGeometry.realization_vertices,
    `HodgeConjecture.NativeSimplexGeometry.realization_face,
    `HodgeConjecture.NativeSimplexGeometry.realization_comp,
    `HodgeConjecture.NativeSimplexGeometry.realization_target_map,
    `HodgeConjecture.NativeSimplexGeometry.center,
    `HodgeConjecture.NativeSimplexGeometry.center_weights,
    `HodgeConjecture.NativeSimplexGeometry.center_weights_vector,
    `HodgeConjecture.NativeSimplexGeometry.center_vertices,
    `HodgeConjecture.NativeSimplexGeometry.center_target_map,
    `HodgeConjecture.NativeSimplexGeometry.center_realization,
    `HodgeConjecture.NativeSimplexGeometry.coordinateHomeomorph,
    `HodgeConjecture.NativeSimplexGeometry.coordinateHomeomorph_val,
    `HodgeConjecture.NativeSimplexGeometry.lebesgue_number,
    `HodgeConjecture.NativeSimplexGeometry.lebesgue_number_two,
    `HodgeConjecture.NativeSimplexGeometry.lebesgue_number_two_diam]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
