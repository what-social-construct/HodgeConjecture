module

public import HodgeConjecture.Realization.Betti.SingularSubdivisionSmallness
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Checks that actual singular-chain subdivision eventually becomes small for
genuine open covers. The crossing real interval starts outside the small
chain submodule and therefore requires a strictly positive iteration count.
Native cell mesh, actual iteration naturality and finite-chain uniformity
are checked independently of a homology-equivalence conclusion.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Convexity HodgeConjecture
open HodgeConjecture.SingularSubdivision HodgeConjecture.SingularSubdivisionSmallness
open scoped Simplicial

namespace SingularSubdivisionSmallnessVerification

def leftOpen : Set ℝ := Set.Iio (2 / 3)
def rightOpen : Set ℝ := Set.Ioi (1 / 3)

theorem twoOpen_cover : leftOpen ∪ rightOpen = Set.univ := by
  ext x
  simp only [leftOpen, rightOpen, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ,
    iff_true]
  by_cases hx : x < 2 / 3
  · exact Or.inl hx
  · exact Or.inr (by linarith)

/-- The actual singular interval from zero to one. -/
def crossingSimplex : (TopCat.toSSet.obj (TopCat.of ℝ)).obj (op ⦋1⦌) :=
  ⟨TopCat.ofHom
    ⟨fun t : SimplexCategory.toTop.obj ⦋1⦌ ↦ t.down.weights 1,
      (StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).comp continuous_uliftDown⟩⟩

theorem crossingSimplex_not_small :
    crossingSimplex ∉
      (SingularSubcomplexes.smallSingular (TopCat.of ℝ) leftOpen rightOpen).obj (op ⦋1⦌) := by
  intro h
  rcases h with hL | hR
  · have ht := hL (ULift.up (StdSimplex.single (1 : Fin 2)))
    change (StdSimplex.single (1 : Fin 2)).weights 1 < (2 / 3 : ℝ) at ht
    norm_num at ht
  · have ht := hR (ULift.up (StdSimplex.single (0 : Fin 2)))
    change (1 / 3 : ℝ) < (StdSimplex.single (0 : Fin 2)).weights 1 at ht
    norm_num at ht

/-- Its canonical coefficient-one chain in the original singular coproduct. -/
def crossingChain : (complex (TopCat.of ℝ)).X 1 :=
  ((TopCat.toSSet.obj (TopCat.of ℝ)).ιChainComplex crossingSimplex
    (R := ModuleCat.of ℚ ℚ)) 1

theorem crossingChain_not_small :
    crossingChain ∉ smallChains (TopCat.of ℝ) leftOpen rightOpen 1 := by
  rw [crossingChain, ← SingularChainCoordinates.coordinates_single, coordinates_mem_smallChains,
    Finsupp.mem_supported]
  intro h
  exact crossingSimplex_not_small (h (by simp))

-- The theorem supplies actual shrinking; the example needs at least one real subdivision.
theorem crossing_eventually_small : ∃ k : ℕ, 0 < k ∧
    iteration (TopCat.of ℝ) 1 k crossingChain ∈
      smallChains (TopCat.of ℝ) leftOpen rightOpen 1 := by
  obtain ⟨k, hk⟩ := exists_iteration_small (TopCat.of ℝ) leftOpen rightOpen isOpen_Iio isOpen_Ioi
    twoOpen_cover 1 crossingChain
  refine ⟨k, ?_, hk⟩
  by_contra h
  have hk0 : k = 0 := by omega
  subst k
  exact crossingChain_not_small hk

section General

variable (X : TopCat) (U V : Set X)

-- One count works for the entire support of an arbitrary finite rational chain.
example (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (c : (complex X).X n) :
    ∃ k : ℕ, iteration X n k c ∈ smallChains X U V n :=
  exists_iteration_small X U V hU hV hcover n c

-- The same count can also be chosen for two independently specified actual chains.
theorem common_iteration (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (c d : (complex X).X n) :
    ∃ k : ℕ, iteration X n k c ∈ smallChains X U V n ∧
      iteration X n k d ∈ smallChains X U V n := by
  obtain ⟨k, hk⟩ := exists_iteration_small X U V hU hV hcover n c
  obtain ⟨l, hl⟩ := exists_iteration_small X U V hU hV hcover n d
  exact ⟨max k l,
    iteration_mem_smallChains_of_le X U V n k (max k l) (le_max_left _ _) c hk,
    iteration_mem_smallChains_of_le X U V n l (max k l) (le_max_right _ _) d hl⟩

example (n k : ℕ) (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    iteration X n k c ∈ smallChains X U V n := iteration_mem_smallChains X U V n k c hc

example (n k : ℕ) (c : (complex X).X n) :
    iteration X n k ((-3 / 2 : ℚ) • c) = (-3 / 2 : ℚ) • iteration X n k c :=
  iteration_smul X n k _ c

example (n k : ℕ) (c d : (complex X).X n) :
    iteration X n k (c + d) = iteration X n k c + iteration X n k d :=
  iteration_add X n k c d

end General

-- The same actual native operator acquires arbitrarily small whole-cell coordinate diameter.
example (n : ℕ)
    (c : AffineSimplexChains.Chain (StdSimplex ℝ (Fin 3)) (n + 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ v ∈ (nativeIteration n k c).support,
      Metric.diam (weights '' Set.range (NativeSimplexGeometry.realization v)) < ε :=
  exists_nativeIteration_mesh_lt n c ε hε

example (X : TopCat) (f : C(StdSimplex ℝ (Fin 3), X)) (n k : ℕ)
    (c : AffineSimplexChains.Chain (StdSimplex ℝ (Fin 3)) (n + 1)) :
    iteration X n k (realize f n c) = realize f n (nativeIteration n k c) :=
  iteration_realize f n k c

end SingularSubdivisionSmallnessVerification

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SingularSubdivisionSmallness.weights,
    `HodgeConjecture.SingularSubdivisionSmallness.weights_injective,
    `HodgeConjecture.SingularSubdivisionSmallness.centers_weights,
    `HodgeConjecture.SingularSubdivisionSmallness.nativeIteration,
    `HodgeConjecture.SingularSubdivisionSmallness.weights_nativeIteration,
    `HodgeConjecture.SingularSubdivisionSmallness.weights_realization,
    `HodgeConjecture.SingularSubdivisionSmallness.map_weights_support,
    `HodgeConjecture.SingularSubdivisionSmallness.exists_nativeIteration_mesh_lt,
    `HodgeConjecture.SingularSubdivisionSmallness.exists_nativeIteration_small,
    `HodgeConjecture.SingularSubdivisionSmallness.centers_realization,
    `HodgeConjecture.SingularSubdivisionSmallness.simplex_realization_comp,
    `HodgeConjecture.SingularSubdivisionSmallness.realize_realization_comp,
    `HodgeConjecture.SingularSubdivisionSmallness.map_realization_reference,
    `HodgeConjecture.SingularSubdivisionSmallness.subdivisionComponent_realize,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration_realize,
    `HodgeConjecture.SingularSubdivisionSmallness.smallChains,
    `HodgeConjecture.SingularSubdivisionSmallness.coordinates_mem_smallChains,
    `HodgeConjecture.SingularSubdivisionSmallness.simplex_mem_small,
    `HodgeConjecture.SingularSubdivisionSmallness.realize_mem_smallChains,
    `HodgeConjecture.SingularSubdivisionSmallness.exists_iteration_simplex_small,
    `HodgeConjecture.SingularSubdivisionSmallness.subdivisionComponent_mem_smallChains,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration_mem_smallChains,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration_mem_smallChains_of_le,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration_add,
    `HodgeConjecture.SingularSubdivisionSmallness.iteration_smul,
    `HodgeConjecture.SingularSubdivisionSmallness.exists_iteration_small,
    `SingularSubdivisionSmallnessVerification.twoOpen_cover,
    `SingularSubdivisionSmallnessVerification.crossingSimplex_not_small,
    `SingularSubdivisionSmallnessVerification.crossingChain_not_small,
    `SingularSubdivisionSmallnessVerification.crossing_eventually_small,
    `SingularSubdivisionSmallnessVerification.common_iteration]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
