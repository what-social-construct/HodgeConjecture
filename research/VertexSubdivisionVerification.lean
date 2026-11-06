module

import HodgeConjecture.Realization.Betti.VertexSubdivisionNaturality
import HodgeConjecture.Realization.Betti.VertexSubdivisionLocality
import HodgeConjecture.Realization.Betti.BarycentricMesh
import Lean.Util.CollectAxioms

/-!
Pure augmented boundary signs, explicit cone identities, recursive
subdivision and homotopy, and locality/naturality checks.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture.AffineSimplexChains HodgeConjecture.VertexSubdivision
open HodgeConjecture.BarycentricMesh

universe u v

variable {E : Type u} {F : Type v}

-- Point boundaries retain their augmentation, which makes coning contractible in index zero.
example (a : E) : boundarySimplex 0 ![a] = Finsupp.single ![] 1 := by
  simp [boundarySimplex, face]

example (a b : E) : boundarySimplex 1 ![a, b] =
    Finsupp.single ![b] 1 - Finsupp.single ![a] 1 := by
  have h1 : Fin.removeNth (1 : Fin 2) ![a, b] = ![a] := by
    ext i; fin_cases i; rfl
  simp [boundarySimplex, Fin.sum_univ_succ, face, h1, sub_eq_add_neg]

example (a b c : E) : boundarySimplex 2 ![a, b, c] =
    Finsupp.single ![b, c] 1 - Finsupp.single ![a, c] 1 + Finsupp.single ![a, b] 1 := by
  have h1 : Fin.removeNth (1 : Fin 3) ![a, b, c] = ![a, c] := by
    ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![a, b, c] = ![a, b] := by
    ext i; fin_cases i <;> rfl
  simp [boundarySimplex, Fin.sum_univ_succ, face, h1, h2]
  abel

example (p : E) (c : Chain E 0) : boundary E 0 (cone p 0 c) = c :=
  boundary_cone_zero p c

example (p : E) (c : Chain E 3) :
    boundary E 3 (cone p 3 c) = c - cone p 2 (boundary E 2 c) :=
  boundary_cone p 2 c

example (c : Chain E 4) : boundary E 2 (boundary E 3 c) = 0 := boundary_squared E 2 c

example (center : Centers E) (c : Chain E 0) : subdivide center 0 c = c :=
  subdivide_zero center c

example (center : Centers E) (c : Chain E 4) :
    boundary E 3 (subdivide center 4 c) = subdivide center 3 (boundary E 3 c) :=
  boundary_subdivide center 3 c

example (center : Centers E) (c : Chain E 4) :
    boundary E 4 (homotopy center 4 c) + homotopy center 3 (boundary E 3 c) =
      c - subdivide center 4 c := homotopy_identity center 3 c

-- Choosing the first vertex is a legitimate algebraic center and is natural under every map.
example (f : E → F) (c : Chain E 3) :
    subdivide (fun _ v ↦ v 0) 3 (HodgeConjecture.AffineSimplexChains.map f 3 c) =
      HodgeConjecture.AffineSimplexChains.map f 3 (subdivide (fun _ v ↦ v 0) 3 c) :=
  subdivide_map (fun _ v ↦ v 0) (fun _ v ↦ v 0) f (fun _ _ ↦ rfl) 3 c

example (f : E → F) (c : Chain E 3) :
    homotopy (fun _ v ↦ v 0) 3 (HodgeConjecture.AffineSimplexChains.map f 3 c) =
      HodgeConjecture.AffineSimplexChains.map f 4 (homotopy (fun _ v ↦ v 0) 3 c) :=
  homotopy_map (fun _ v ↦ v 0) (fun _ v ↦ v 0) f (fun _ _ ↦ rfl) 3 c

example (U : Set E) (c : Chain E 3) (hc : c ∈ Supported U 3) :
    subdivide (fun _ v ↦ v 0) 3 c ∈ Supported U 3 :=
  subdivide_mem_supported (fun _ v ↦ v 0) U (fun _ _ hv ↦ hv 0) 3 c hc

example (U : Set E) (c : Chain E 3) (hc : c ∈ Supported U 3) :
    homotopy (fun _ v ↦ v 0) 3 c ∈ Supported U 4 :=
  homotopy_mem_supported (fun _ v ↦ v 0) U (fun _ _ hv ↦ hv 0) 3 c hc

-- The geometric specialization actually chooses the midpoint of this scalar segment.
example : barycentricCenters ℝ 1 ![0, 2] = 1 := by
  norm_num [barycentricCenters, HodgeConjecture.SubdivisionGeometry.mean, Fin.sum_univ_succ]

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.AffineSimplexChains.Vertices,
    `HodgeConjecture.AffineSimplexChains.Chain,
    `HodgeConjecture.AffineSimplexChains.face,
    `HodgeConjecture.AffineSimplexChains.boundarySimplex,
    `HodgeConjecture.AffineSimplexChains.boundary,
    `HodgeConjecture.AffineSimplexChains.boundary_single,
    `HodgeConjecture.AffineSimplexChains.cone,
    `HodgeConjecture.AffineSimplexChains.cone_single,
    `HodgeConjecture.AffineSimplexChains.face_cons_zero,
    `HodgeConjecture.AffineSimplexChains.face_cons_succ,
    `HodgeConjecture.AffineSimplexChains.boundarySimplex_cons,
    `HodgeConjecture.AffineSimplexChains.boundary_cone,
    `HodgeConjecture.AffineSimplexChains.boundary_cone_zero,
    `HodgeConjecture.AffineSimplexChains.boundary_squared,
    `HodgeConjecture.AffineSimplexChains.map,
    `HodgeConjecture.AffineSimplexChains.map_single,
    `HodgeConjecture.AffineSimplexChains.boundary_map,
    `HodgeConjecture.AffineSimplexChains.map_cone,
    `HodgeConjecture.VertexSubdivision.subdivide,
    `HodgeConjecture.VertexSubdivision.Centers,
    `HodgeConjecture.VertexSubdivision.subdivide_zero,
    `HodgeConjecture.VertexSubdivision.subdivide_single,
    `HodgeConjecture.VertexSubdivision.boundary_subdivide,
    `HodgeConjecture.VertexSubdivision.homotopy,
    `HodgeConjecture.VertexSubdivision.homotopy_zero,
    `HodgeConjecture.VertexSubdivision.homotopy_single,
    `HodgeConjecture.VertexSubdivision.homotopy_identity_map,
    `HodgeConjecture.VertexSubdivision.homotopy_identity,
    `HodgeConjecture.VertexSubdivision.Supported,
    `HodgeConjecture.VertexSubdivision.supported_single,
    `HodgeConjecture.VertexSubdivision.supported_map_le,
    `HodgeConjecture.VertexSubdivision.boundary_mem_supported,
    `HodgeConjecture.VertexSubdivision.cone_mem_supported,
    `HodgeConjecture.VertexSubdivision.subdivide_mem_supported,
    `HodgeConjecture.VertexSubdivision.homotopy_mem_supported,
    `HodgeConjecture.VertexSubdivision.subdivide_map,
    `HodgeConjecture.VertexSubdivision.homotopy_map]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
