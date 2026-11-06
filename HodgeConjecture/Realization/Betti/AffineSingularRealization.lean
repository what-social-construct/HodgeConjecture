module

public import HodgeConjecture.Realization.Betti.AffineSimplexChains
public import HodgeConjecture.Realization.Betti.SubdivisionGeometry
public import HodgeConjecture.Realization.Betti.SingularSubcomplexes
public import HodgeConjecture.Realization.Betti.SingularChainCoordinates

@[expose] public section

/-!
# Affine vertex chains in the actual singular complex

Finite ordered vertex tuples evaluate as actual continuous affine singular
simplices. Linear extension lands in Mathlib's original rational singular
chain complex and commutes with its alternating boundary. Convex containment
of the original vertices gives containment of each realized simplex.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.AffineSingularRealization

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual singular simplicial set of the normed real vector space. -/
abbrev singularSet (E : Type) [NormedAddCommGroup E] := TopCat.toSSet.obj (TopCat.of E)

/-- Mathlib's original rational singular chain complex. -/
abbrev singularComplex (E : Type) [NormedAddCommGroup E] :=
  (singularSet E).chainComplex (ModuleCat.of ℚ ℚ)

/-- Ordered vertices give the original continuous affine singular simplex. -/
def simplex (n : ℕ) (v : Fin (n + 1) → E) : (singularSet E).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌)).symm (SubdivisionGeometry.realization v)

@[simp]
theorem simplex_continuous (n : ℕ) (v : Fin (n + 1) → E) :
    TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌) (simplex n v) =
      SubdivisionGeometry.realization v := Equiv.apply_symm_apply _ _

/-- Deleting a vertex is the actual singular face restriction. -/
theorem simplex_face (n : ℕ) (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (singularSet E).δ i (simplex (n + 1) v) = simplex n (AffineSimplexChains.face v i) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌)).injective
  ext t
  exact SubdivisionGeometry.realization_map v i.succAbove t

/-- Distinct ordered vertex families give distinct actual affine singular simplices. -/
theorem simplex_injective (n : ℕ) : Function.Injective (simplex (E := E) n) := by
  intro v w h
  funext i
  have hv := congrArg (fun σ ↦ TopCat.toSSetObjEquiv (TopCat.of E) (op ⦋n⦌) σ
    (Convexity.StdSimplex.single i)) h
  rw [simplex_continuous, simplex_continuous, SubdivisionGeometry.realization_single,
    SubdivisionGeometry.realization_single] at hv
  exact hv

/-- Realize a finite rational vertex chain in the original singular chain coproduct. -/
def chainRealization (n : ℕ) :
    AffineSimplexChains.Chain E (n + 1) →ₗ[ℚ] (singularComplex E).X n :=
  (SingularChainCoordinates.coordinates (singularSet E) n).toLinearMap.comp
    (Finsupp.lmapDomain ℚ ℚ (simplex n))

@[simp]
theorem chainRealization_single (n : ℕ) (v : Fin (n + 1) → E) (a : ℚ) :
    chainRealization n (Finsupp.single v a) =
      ((singularSet E).ιChainComplex (simplex n v) (R := ModuleCat.of ℚ ℚ)) a := by
  simp [chainRealization]

/-- Affine vertex chains embed faithfully into the actual singular chain module. -/
theorem chainRealization_injective (n : ℕ) : Function.Injective (chainRealization (E := E) n) :=
  (SingularChainCoordinates.coordinates (singularSet E) n).injective.comp
    (Finsupp.mapDomain_injective (simplex_injective n))

/-- The vertex-chain boundary agrees with Mathlib's actual singular boundary. -/
theorem chainRealization_boundary (n : ℕ) (c : AffineSimplexChains.Chain E (n + 2)) :
    (singularComplex E).d (n + 1) n (chainRealization (n + 1) c) =
      chainRealization n (AffineSimplexChains.boundary E (n + 1) c) := by
  change (singularComplex E).d (n + 1) n
    (SingularChainCoordinates.coordinates (singularSet E) (n + 1)
      (Finsupp.lmapDomain ℚ ℚ (simplex (n + 1)) c)) = _
  rw [SingularChainCoordinates.coordinates_boundary]
  apply congrArg (SingularChainCoordinates.coordinates (singularSet E) n)
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using congrArg₂ (· + ·) hc hd
  | single v a =>
    simp [AffineSimplexChains.boundarySimplex, simplex_face,
      SingularChainCoordinates.boundary_single, Finset.smul_sum, mul_comm]

/-- Convexity converts vertex containment into genuine whole-simplex containment. -/
theorem simplex_mem_subset {U : Set E} (hU : Convex ℝ U) (n : ℕ)
    (v : Fin (n + 1) → E) (hv : ∀ i, v i ∈ U) :
    simplex n v ∈ (SingularSubcomplexes.subsetSingular (TopCat.of E) U).obj (op ⦋n⦌) := by
  rw [SingularSubcomplexes.mem_subsetSingular_iff_range, simplex_continuous]
  rintro _ ⟨t, rfl⟩
  exact (convexHull_min (Set.range_subset_iff.mpr hv) hU)
    (SubdivisionGeometry.realization_mem_convexHull v t)

end HodgeConjecture.AffineSingularRealization
