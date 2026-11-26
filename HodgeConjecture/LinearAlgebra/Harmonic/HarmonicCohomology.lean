module

/-
Adapted from `galois-obstruction-theory`,
`GaloisObstructionTheory/Homotopical/Sheaf/HarmonicCohomology.lean`.
Source SHA-256: bccd03005c0c82becb49c8bb11311b2fe7e39d76ff51e5c10eacae6c1f47213d

Copyright (c) 2026 what-social-construct. Distributed under the MIT license;
the original notice and permission are retained in `LinearAlgebra/Harmonic/LICENSE`.
The copied declarations retain the same finite real cochains and oriented complex.
Only import paths, enclosing namespaces, and the explicitly documented bridge
added below differ from the source.
-/

public import HodgeConjecture.LinearAlgebra.Harmonic.Cohomology
public import HodgeConjecture.LinearAlgebra.Harmonic.Morphism

@[expose] public section

/-!
# Harmonic representatives of cellular cohomology in degree one

The actual cellular cocycles split into the exact and harmonic
subspaces. The quotient by exact cochains identifies with the harmonic
subspace through orthogonal projection.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace

noncomputable section

namespace HodgeConjecture.Harmonic.CellularSheaf

variable {Vertex Edge Face : Type*} [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face} (F : CellularSheaf X)

/-- The degree-one cocycles of the cellular sheaf. -/
abbrev oneCycles : Submodule ℝ F.C1 := LinearMap.ker F.delta1

/-- The image of `δ₀` viewed as a submodule of the degree-one cocycles. -/
def oneBoundaries : Submodule ℝ F.oneCycles := F.exactOneSubspace.comap F.oneCycles.subtype

/-- The copied boundary submodule is exactly the existing closed-cochain boundary submodule. -/
@[simp]
theorem oneBoundaries_eq_exactClosedOneSubspace :
    F.oneBoundaries = F.exactClosedOneSubspace := rfl

/-- Degree-one cohomology of the actual cellular coboundaries. -/
abbrev CohomologyOne := F.oneCycles ⧸ F.oneBoundaries

/-- The copied cohomology is the existing native kernel/range quotient. -/
def cohomologyOneEquivExactClosedQuotient :
    F.CohomologyOne ≃ₗ[ℝ] (LinearMap.ker F.delta1) ⧸ F.exactClosedOneSubspace :=
  LinearEquiv.refl ℝ _

@[simp]
theorem cohomologyOneEquivExactClosedQuotient_mk (c : F.oneCycles) :
    F.cohomologyOneEquivExactClosedQuotient (F.oneBoundaries.mkQ c) =
      (Submodule.Quotient.mk c : (LinearMap.ker F.delta1) ⧸ F.exactClosedOneSubspace) := rfl

theorem exactOneSubspace_le_oneCycles : F.exactOneSubspace ≤ F.oneCycles :=
  LinearMap.range_le_ker_iff.mpr F.delta1_comp_delta0

theorem harmonicOneSubspace_le_oneCycles : F.harmonicOneSubspace ≤ F.oneCycles := by
  rw [harmonicOneSubspace, F.ker_degreeOneLaplacian]
  exact inf_le_right

/-- In the cocycle space, the orthogonal complement of the boundaries is
the harmonic subspace. -/
theorem oneBoundaries_orthogonal :
    F.oneBoundariesᗮ = F.harmonicOneSubspace.comap F.oneCycles.subtype := by
  have h : F.exactOneSubspace ≤ F.oneCycles.subtypeₗᵢ.range := by
    change F.exactOneSubspace ≤ LinearMap.range F.oneCycles.subtype
    rw [Submodule.range_subtype]
    exact F.exactOneSubspace_le_oneCycles
  calc
    F.oneBoundariesᗮ = (F.exactOneSubspaceᗮ).comap F.oneCycles.subtype :=
      (Submodule.comap_orthogonal_of_le h).symm
    _ = _ := by
      rw [exactOneSubspace, LinearMap.orthogonal_range, harmonicOneSubspace,
        F.ker_degreeOneLaplacian]
      ext x
      change F.delta0.adjoint x.val = 0 ↔ F.delta0.adjoint x.val = 0 ∧ F.delta1 x.val = 0
      exact (and_iff_left (LinearMap.mem_ker.mp x.property)).symm

/-- Orthogonal projection identifies a cohomology class with its unique
harmonic representative. -/
def cohomologyOneEquivHarmonic : F.CohomologyOne ≃ₗ[ℝ] F.harmonicOneSubspace :=
  (F.oneBoundaries.quotientEquivOfIsCompl _ F.oneBoundaries.isCompl_orthogonal).trans
    ((LinearEquiv.ofEq _ _ F.oneBoundaries_orthogonal).trans
      (Submodule.comapSubtypeEquivOfLe F.harmonicOneSubspace_le_oneCycles))

/-- A harmonic vector maps back to its class as a cocycle. -/
@[simp]
theorem cohomologyOneEquivHarmonic_symm_apply (h : F.harmonicOneSubspace) :
    F.cohomologyOneEquivHarmonic.symm h =
      F.oneBoundaries.mkQ (Submodule.inclusion F.harmonicOneSubspace_le_oneCycles h) := by
  rw [cohomologyOneEquivHarmonic, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  rfl

namespace Morphism

variable {F} {G : CellularSheaf X}

/-- A cellular-sheaf morphism preserves cocycles. -/
theorem mapC1_mem_oneCycles (η : Morphism F G) {b : F.C1} (hb : b ∈ F.oneCycles) :
    η.mapC1 b ∈ G.oneCycles := by
  change G.delta1 (η.mapC1 b) = 0
  have h := LinearMap.congr_fun η.mapC2_delta1 b
  simp only [LinearMap.comp_apply] at h
  rw [← h, LinearMap.mem_ker.mp hb, map_zero]

/-- A cellular-sheaf morphism preserves coboundaries. -/
theorem mapC1_mem_exactOneSubspace (η : Morphism F G) {b : F.C1}
    (hb : b ∈ F.exactOneSubspace) : η.mapC1 b ∈ G.exactOneSubspace := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨η.mapC0 a, (LinearMap.congr_fun η.mapC1_delta0 a).symm⟩

/-- The degree-one map on cocycles induced by a cellular-sheaf morphism. -/
def mapOneCycles (η : Morphism F G) : F.oneCycles →ₗ[ℝ] G.oneCycles :=
  (η.mapC1.comp F.oneCycles.subtype).codRestrict G.oneCycles
    (fun b ↦ mapC1_mem_oneCycles η b.property)

/-- The induced map on degree-one cellular cohomology. -/
def mapCohomologyOne (η : Morphism F G) : F.CohomologyOne →ₗ[ℝ] G.CohomologyOne :=
  F.oneBoundaries.mapQ G.oneBoundaries η.mapOneCycles
    (fun _ hb ↦ mapC1_mem_exactOneSubspace η hb)

/-- A symmetric degree-one map preserves harmonic cochains. -/
theorem mapC1_mem_harmonicOneSubspace (η : Morphism F F) (hη : η.mapC1.IsSymmetric)
    {b : F.C1} (hb : b ∈ F.harmonicOneSubspace) : η.mapC1 b ∈ F.harmonicOneSubspace := by
  have horthogonal : b ∈ F.exactOneSubspaceᗮ := by
    rw [exactOneSubspace, LinearMap.orthogonal_range]
    exact (F.degreeOneLaplacian_apply_eq_zero_iff b).mp (LinearMap.mem_ker.mp hb) |>.1
  rw [harmonicOneSubspace, F.ker_degreeOneLaplacian, ← LinearMap.orthogonal_range]
  refine ⟨(Submodule.mem_orthogonal _ _).mpr ?_,
    mapC1_mem_oneCycles η (F.harmonicOneSubspace_le_oneCycles hb)⟩
  intro a ha
  rw [← hη a b]
  exact (Submodule.mem_orthogonal _ _).mp horthogonal _ (mapC1_mem_exactOneSubspace η ha)

/-- A symmetric degree-one map of a cellular endomorphism restricts to the
harmonic subspace. -/
def mapHarmonicOne (η : Morphism F F) (hη : η.mapC1.IsSymmetric) :
    F.harmonicOneSubspace →ₗ[ℝ] F.harmonicOneSubspace :=
  (η.mapC1.comp F.harmonicOneSubspace.subtype).codRestrict F.harmonicOneSubspace
    (fun b ↦ mapC1_mem_harmonicOneSubspace η hη b.property)

/-- The harmonic-representative comparison intertwines the two maps
induced by a cellular endomorphism whose degree-one map is symmetric. -/
theorem cohomologyOneEquivHarmonic_naturality (η : Morphism F F) (hη : η.mapC1.IsSymmetric)
    (b : F.CohomologyOne) :
    F.cohomologyOneEquivHarmonic (η.mapCohomologyOne b) =
      η.mapHarmonicOne hη (F.cohomologyOneEquivHarmonic b) := by
  apply F.cohomologyOneEquivHarmonic.symm.injective
  rw [LinearEquiv.symm_apply_apply, cohomologyOneEquivHarmonic_symm_apply]
  have hb := F.cohomologyOneEquivHarmonic.symm_apply_apply b
  rw [cohomologyOneEquivHarmonic_symm_apply] at hb
  conv_lhs => rw [← hb]
  rfl

end Morphism

end HodgeConjecture.Harmonic.CellularSheaf

end
