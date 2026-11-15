module

public import HodgeConjecture.Realization.Betti.SingularSubdivision
public import HodgeConjecture.Realization.Betti.SubcomplexOperators

@[expose] public section

/-!
# Support of actual affine singular-chain realization

This is the shared finite-support argument for any original singular
subcomplex, independent of how a cover is indexed.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory Opposite Convexity AffineSimplexChains SubcomplexChainCoordinates
open scoped Simplicial

/-- Realizing a finite chain retains containment of every actual supported simplex. -/
theorem realize_mem_chainSubmodule {κ : Type} [Finite κ] {X : TopCat.{0}}
    (f : C(StdSimplex ℝ κ, X)) (A : (TopCat.toSSet.obj X).Subcomplex) (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (hc : ∀ v ∈ c.support, simplex f n v ∈ A.obj (op ⦋n⦌)) :
    realize f n c ∈ chainSubmodule A n := by
  classical
  rw [mem_chainSubmodule_iff_support]
  change ∀ σ ∈ ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm
    ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n)
      (Finsupp.lmapDomain ℚ ℚ (simplex f n) c))).support, σ ∈ A.obj (op ⦋n⦌)
  rw [LinearEquiv.symm_apply_apply]
  intro σ hσ
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  exact hc v hv

end HodgeConjecture.SingularSubdivision
