module

public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates
public import HodgeConjecture.Realization.Betti.SingularSubcomplexes
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The small-chain modules are the original native subcomplex chain objects.
Their actual inclusions, supported ranges, native boundaries and cycle
lifting are checked without a homology-comparison premise.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HodgeConjecture
open SingularChainCoordinates SubcomplexChainCoordinates

namespace SubcomplexChainVerification

noncomputable section

example {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) (c : S.obj (op ⦋n⦌) →₀ ℚ) :
    (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n (coordinates S n c) =
      coordinates T n (Finsupp.lmapDomain ℚ ℚ (f.app (op ⦋n⦌)) c) :=
  coordinates_map f n c

example {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (c : (A : SSet).obj (op ⦋n⦌) →₀ ℚ) :
    (inclusion A).f n (coordinates A n c) =
      coordinates S n (Finsupp.mapDomain Subtype.val c) := inclusion_coordinates A n c

example {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (a b : (complex (A : SSet)).X n) (h : (inclusion A).f n a = (inclusion A).f n b) :
    a = b := inclusion_injective A n h

example {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ) (c : (complex S).X n) :
    c ∈ chainSubmodule A n ↔
      ∀ σ ∈ ((coordinates S n).symm c).support, σ ∈ A.obj (op ⦋n⦌) :=
  mem_chainSubmodule_iff_support A n c

example (X : TopCat.{0}) (U : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : Set.range (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) ⊆ U) (a : ℚ) :
    ((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) a ∈
      chainSubmodule (SingularSubcomplexes.subsetSingular X U) n :=
  ιChainComplex_mem_chainSubmodule _ _ σ
    ((SingularSubcomplexes.mem_subsetSingular_iff_range X U _ σ).mpr hσ) a

example {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (c : (complex S).X (n + 1)) (hc : c ∈ chainSubmodule A (n + 1)) :
    (complex S).d (n + 1) n c ∈ chainSubmodule A n :=
  boundary_mem_chainSubmodule A n c hc

example {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (c : (complex (A : SSet)).X (n + 1)) :
    SubcomplexChainCoordinates.boundary A n (chainSubmoduleEquiv A (n + 1) c) =
      chainSubmoduleEquiv A n ((complex (A : SSet)).d (n + 1) n c) :=
  chainSubmoduleEquiv_boundary A n c

theorem supported_native_chain_lifts {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (c : (complex S).X n) (hc : c ∈ chainSubmodule A n) :
    ∃ a : (complex (A : SSet)).X n, (inclusion A).f n a = c := by
  rw [← range_inclusion] at hc
  exact hc

/-- Supported actual cycles lift to actual cycles, with no independently supplied boundary rule. -/
theorem supported_native_cycle_lifts {S : SSet.{0}} (A : S.Subcomplex) (n : ℕ)
    (c : (complex S).X (n + 1)) (hc : c ∈ chainSubmodule A (n + 1))
    (hd : (complex S).d (n + 1) n c = 0) :
    ∃ a : (complex (A : SSet)).X (n + 1),
      (inclusion A).f (n + 1) a = c ∧ (complex (A : SSet)).d (n + 1) n a = 0 := by
  obtain ⟨a, ha⟩ := supported_native_chain_lifts A (n + 1) c hc
  refine ⟨a, ha, inclusion_injective A n ?_⟩
  have h := congrArg (fun f : (complex (A : SSet)).X (n + 1) ⟶ (complex S).X n ↦ f a)
    ((inclusion A).comm (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ha, hd, map_zero] using h.symm

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SubcomplexChainCoordinates.coordinates_map,
      `HodgeConjecture.SubcomplexChainCoordinates.inclusionCoordinates,
      `HodgeConjecture.SubcomplexChainCoordinates.inclusion_coordinates,
      `HodgeConjecture.SubcomplexChainCoordinates.range_inclusionCoordinates,
      `HodgeConjecture.SubcomplexChainCoordinates.inclusionCoordinates_injective,
      `HodgeConjecture.SubcomplexChainCoordinates.inclusion_injective,
      `HodgeConjecture.SubcomplexChainCoordinates.chainSubmodule,
      `HodgeConjecture.SubcomplexChainCoordinates.mem_chainSubmodule_iff,
      `HodgeConjecture.SubcomplexChainCoordinates.mem_chainSubmodule_iff_support,
      `HodgeConjecture.SubcomplexChainCoordinates.ιChainComplex_mem_chainSubmodule,
      `HodgeConjecture.SubcomplexChainCoordinates.range_inclusion,
      `HodgeConjecture.SubcomplexChainCoordinates.chainSubmoduleEquiv,
      `HodgeConjecture.SubcomplexChainCoordinates.chainSubmoduleEquiv_coe,
      `HodgeConjecture.SubcomplexChainCoordinates.boundary_mem_chainSubmodule,
      `HodgeConjecture.SubcomplexChainCoordinates.boundary,
      `HodgeConjecture.SubcomplexChainCoordinates.chainSubmoduleEquiv_boundary,
      `SubcomplexChainVerification.supported_native_chain_lifts,
      `SubcomplexChainVerification.supported_native_cycle_lifts] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end

end SubcomplexChainVerification
