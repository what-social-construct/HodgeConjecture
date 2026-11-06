module

import HodgeConjecture.Realization.Betti.SubdivisionGeometry
import Lean.Util.CollectAxioms

/-!
Actual affine face evaluation, nested barycenters and quantitative iterated
mesh shrinking. No comparison on singular-chain homology is assumed.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture.SubdivisionGeometry Convexity

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (v : Fin 3 → E) (i : Fin 3) : realization v (.single i) = v i :=
  realization_single v i

-- The actual geometric face agrees with deleting the same original vertex.
example (v : Fin 4 → E) (i : Fin 4) (t : StdSimplex ℝ (Fin 3)) :
    realization v (StdSimplex.map i.succAbove t) = realization (i.removeNth v) t :=
  realization_map v i.succAbove t

example : mean (fun i : Fin 3 ↦ (i : ℝ)) Finset.univ = 1 := by
  norm_num [mean, Fin.sum_univ_succ]

example (v : Fin 3 → E) :
    realization v StdSimplex.barycenter = mean v Finset.univ :=
  realization_barycenter v

example (v : Fin 4 → E) (s t : Finset (Fin 4)) (hs : s.Nonempty) (hst : s ⊆ t) :
    dist (mean v s) (mean v t) ≤
      (1 - (s.card : ℝ) / t.card) * Metric.diam (v '' (t : Set (Fin 4))) :=
  dist_mean_mean_le v s t hs hst

example (v : Fin 3 → E) (e : Equiv.Perm (Fin 3)) :
    Metric.diam (Set.range (barycentricSimplex v e)) ≤
      (2 / 3 : ℝ) * Metric.diam (Set.range v) := by
  convert diam_range_barycentricSimplex_le v e using 1; norm_num

example (v : Fin 2 → E) (e : Equiv.Perm (Fin 2)) :
    Metric.diam (Set.range (barycentricSimplex v e)) ≤
      (1 / 2 : ℝ) * Metric.diam (Set.range v) := by
  convert diam_range_barycentricSimplex_le v e using 1; norm_num

example (v : Fin 4 → E) (e : Equiv.Perm (Fin 4)) :
    Metric.diam (Set.range (barycentricSimplex v e)) ≤
      (3 / 4 : ℝ) * Metric.diam (Set.range v) := by
  convert diam_range_barycentricSimplex_le v e using 1; norm_num

-- Every path of three actual triangle refinements has this same bound.
example (v : Fin 3 → E) (a b c : Equiv.Perm (Fin 3)) :
    Metric.diam (Set.range (iteratedVertices v [a, b, c])) ≤
      (8 / 27 : ℝ) * Metric.diam (Set.range v) := by
  convert diam_range_iteratedVertices_le v [a, b, c] using 1; norm_num

example (v : Fin 4 → E) :
    ∃ k : ℕ, ∀ es : List (Equiv.Perm (Fin 4)), es.length = k →
      Metric.diam (Set.range (realization (iteratedVertices v es))) < 1 / 1000 :=
  exists_iterated_mesh_lt v _ (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SubdivisionGeometry.realization,
    `HodgeConjecture.SubdivisionGeometry.realization_map,
    `HodgeConjecture.SubdivisionGeometry.realization_mem_convexHull,
    `HodgeConjecture.SubdivisionGeometry.mean_mem_convexHull,
    `HodgeConjecture.SubdivisionGeometry.mean_sub_mean,
    `HodgeConjecture.SubdivisionGeometry.dist_mean_vertex_le_diam,
    `HodgeConjecture.SubdivisionGeometry.dist_mean_mean_le,
    `HodgeConjecture.SubdivisionGeometry.realization_barycenter,
    `HodgeConjecture.SubdivisionGeometry.diam_range_realization_le,
    `HodgeConjecture.SubdivisionGeometry.dist_mean_mean_le_uniform,
    `HodgeConjecture.SubdivisionGeometry.flagRealization,
    `HodgeConjecture.SubdivisionGeometry.diam_range_flagRealization_le,
    `HodgeConjecture.SubdivisionGeometry.permutationFlag_nested,
    `HodgeConjecture.SubdivisionGeometry.barycentricSimplex,
    `HodgeConjecture.SubdivisionGeometry.diam_range_barycentricSimplex_le,
    `HodgeConjecture.SubdivisionGeometry.exists_barycentric_power_mul_lt,
    `HodgeConjecture.SubdivisionGeometry.diam_range_subdividedVertices_le,
    `HodgeConjecture.SubdivisionGeometry.diam_range_iteratedVertices_le,
    `HodgeConjecture.SubdivisionGeometry.exists_iterated_mesh_lt]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
