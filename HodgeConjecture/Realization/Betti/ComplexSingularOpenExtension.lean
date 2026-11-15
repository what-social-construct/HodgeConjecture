module

public import HodgeConjecture.Realization.Betti.ComplexSingularPresheaf
public import HodgeConjecture.Realization.Betti.SingularSubcomplexes

@[expose] public noncomputable section

/-!
# Extension of the original complex-valued singular cochains from an open

The existing unrestricted complex simplex coordinates extend a cochain on
an actual open subtype by zero on simplices that are not contained in it.
Restriction along the original open inclusion recovers the given cochain.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite Simplicial

namespace HodgeConjecture.SingularCoefficientChange

open SingularSubcomplexes

variable (X : TopCat.{0})

/-- Actual zero extension of a complex-valued cochain on an open subspace. -/
def openExtension (U : Opens X) (n : ℕ)
    (φ : (complexCochains ((Opens.toTopCat X).obj U)).X n) :
    (complexCochains X).X n := by
  classical
  exact (complexCoordinates X n).symm (fun σ ↦
    if h : σ ∈ (subsetSingular X U).obj (op ⦋n⦌) then
      complexCoordinates ((Opens.toTopCat X).obj U) n φ
        ((subsetToSubtype X U).app (op ⦋n⦌) ⟨σ, h⟩)
    else 0)

/-- Pullback to the original open subspace is a left inverse to zero extension. -/
theorem pullback_openExtension (U : Opens X) (n : ℕ)
    (φ : (complexCochains ((Opens.toTopCat X).obj U)).X n) :
    (pullback (Opens.inclusion' U)).f n (openExtension X U n φ) = φ := by
  apply (complexCoordinates ((Opens.toTopCat X).obj U) n).injective
  funext σ
  rw [pullback_coordinates]
  let τ : SingularCochains.Simplex X n :=
    (TopCat.toSSet.map (Opens.inclusion' U)).app (op ⦋n⦌) σ
  have hτ : τ ∈ (subsetSingular X U).obj (op ⦋n⦌) := by
    intro t
    exact (SingularSubcomplexes.simplexMap ((Opens.toTopCat X).obj U) (op ⦋n⦌) σ t).property
  change complexCoordinates X n (openExtension X U n φ) τ =
    complexCoordinates ((Opens.toTopCat X).obj U) n φ σ
  rw [openExtension, (complexCoordinates X n).apply_symm_apply]
  rw [dite_eq_left hτ]
  change complexCoordinates ((Opens.toTopCat X).obj U) n φ
    ((subsetToSubtype X U).app (op ⦋n⦌)
      ((subtypeToSubset X U).app (op ⦋n⦌) σ)) = _
  rfl

end HodgeConjecture.SingularCoefficientChange
