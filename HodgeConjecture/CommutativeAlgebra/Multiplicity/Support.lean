/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Source: StacksFrontier/RingTheory/Support/Basic.lean
Only the submodule-support inclusion used by the multiplicity proofs is retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import Mathlib.RingTheory.Support

@[expose] public section

/-- A submodule's support is contained in that of its ambient module. -/
theorem support_submodule_subset
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Module.support R N ⊆ Module.support R M :=
  Module.support_subset_of_injective N.subtype Subtype.val_injective
