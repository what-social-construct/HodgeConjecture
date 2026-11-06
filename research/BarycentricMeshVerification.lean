module

import HodgeConjecture.Realization.Betti.BarycentricMesh
import Lean.Util.CollectAxioms

/-!
Checks on the support of the actual recursive chain operator, its uniform
iterated mesh shrinking and its locality for convex subsets.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture HodgeConjecture.AffineSimplexChains
open HodgeConjecture.VertexSubdivision HodgeConjecture.SubdivisionGeometry
open HodgeConjecture.BarycentricMesh

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (v : Vertices E 4) :
    subdivide (barycentricCenters E) 4 (Finsupp.single v 1) ∈ flagChains v 4 :=
  subdivide_single_mem_flagChains 4 v

-- The actual recursively generated segment cells have diameter at most half the input.
example (v w : Vertices E 2)
    (hw : w ∈ (subdivide (barycentricCenters E) 2 (Finsupp.single v 1)).support) :
    Metric.diam (Set.range (realization w)) ≤ (1 / 2 : ℝ) * Metric.diam (Set.range v) := by
  convert mesh_subdivide_single_le 1 v w hw using 1; norm_num

-- This bound uses the actual tetrahedron-chain support, including cancellations.
example (v w : Vertices E 4)
    (hw : w ∈ (subdivide (barycentricCenters E) 4 (Finsupp.single v 1)).support) :
    Metric.diam (Set.range (realization w)) ≤ (3 / 4 : ℝ) * Metric.diam (Set.range v) := by
  convert mesh_subdivide_single_le 3 v w hw using 1; norm_num

example (c : Chain E 3) (r : ℝ) (hc : c ∈ MeshBound E 3 r) :
    iteratedSubdivision 2 3 c ∈ MeshBound E 3 ((8 / 27 : ℝ) * r) := by
  convert iteratedSubdivision_mem_meshBound 2 3 r c hc using 1; norm_num

-- A single subdivision count makes every surviving tuple of an arbitrary finite chain small.
example (c : Chain E 4) :
    ∃ k : ℕ, ∀ w ∈ (iteratedSubdivision 3 k c).support,
      Metric.diam (Set.range (realization w)) < 1 / 1000 :=
  exists_iteratedSubdivision_mesh_lt 3 c _ (by norm_num)

example (U : Set E) (hU : Convex ℝ U) (c : Chain E 3) (hc : c ∈ Supported U 3) :
    subdivide (barycentricCenters E) 3 c ∈ Supported U 3 :=
  subdivide_mem_supported_convex U hU 3 c hc

example (U : Set E) (hU : Convex ℝ U) (c : Chain E 3) (hc : c ∈ Supported U 3) :
    homotopy (barycentricCenters E) 3 c ∈ Supported U 4 :=
  homotopy_mem_supported_convex U hU 3 c hc

-- Choosing barycentric centers supplies no hypothesis to the actual homotopy identity.
example (c : Chain E 3) :
    boundary E 3 (homotopy (barycentricCenters E) 3 c) +
      homotopy (barycentricCenters E) 2 (boundary E 2 c) =
        c - subdivide (barycentricCenters E) 3 c :=
  homotopy_identity (barycentricCenters E) 2 c

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.BarycentricMesh.barycentricCenters,
    `HodgeConjecture.BarycentricMesh.IsFlag,
    `HodgeConjecture.BarycentricMesh.mean_comp_injective,
    `HodgeConjecture.BarycentricMesh.IsFlag.embed,
    `HodgeConjecture.BarycentricMesh.IsFlag.cons,
    `HodgeConjecture.BarycentricMesh.cone_mem_flagChains,
    `HodgeConjecture.BarycentricMesh.subdivide_single_mem_flagChains,
    `HodgeConjecture.BarycentricMesh.mesh_subdivide_single_le,
    `HodgeConjecture.BarycentricMesh.vertex_mesh_subdivide_single_le,
    `HodgeConjecture.BarycentricMesh.subdivide_mem_meshBound,
    `HodgeConjecture.BarycentricMesh.iteratedSubdivision_mem_meshBound,
    `HodgeConjecture.BarycentricMesh.exists_meshBound,
    `HodgeConjecture.BarycentricMesh.exists_iteratedSubdivision_mesh_lt,
    `HodgeConjecture.BarycentricMesh.barycentricCenters_mem_convex,
    `HodgeConjecture.BarycentricMesh.subdivide_mem_supported_convex,
    `HodgeConjecture.BarycentricMesh.homotopy_mem_supported_convex]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
