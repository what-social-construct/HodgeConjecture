module

public import HodgeConjecture.Realization.Betti.SingularHomotopy
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Cohomology of a product with a contractible factor

Projection from `X × Y` to `Y` is a homotopy equivalence when `X` is
contractible. The resulting isomorphism uses the original singular
cohomology pullback, so a generator of `Hⁿ(Y, ℚ)` generates
`Hⁿ(X × Y, ℚ)` after projection pullback. This is the reusable local
calculation for an affine chart of `P¹ × P¹`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProductContractibleFactor

open CategoryTheory ContinuousMap

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
  [ContractibleSpace X]

/-- The actual projection to the second factor is a homotopy equivalence
when the first factor is contractible. -/
def projectionHomotopyEquiv : (X × Y) ≃ₕ Y := by
  let e : X ≃ₕ Unit := Classical.choice (ContractibleSpace.hequiv_unit X)
  exact (e.prodCongr (ContinuousMap.HomotopyEquiv.refl Y)).trans
    (Homeomorph.uniqueProd Unit Y).toHomotopyEquiv

@[simp] theorem projectionHomotopyEquiv_apply (p : X × Y) :
    projectionHomotopyEquiv X Y p = p.2 := rfl

/-- The original singular-cohomology map induced by projection is an
isomorphism in every degree. -/
def cohomologyIso (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of Y) n ≅
      SingularCochains.Cohomology (TopCat.of (X × Y)) n :=
  SingularHomotopy.homotopyEquivIso (projectionHomotopyEquiv X Y) n

/-- The isomorphism is the actual pullback along the second projection. -/
theorem cohomologyIso_hom (n : ℕ) :
    (cohomologyIso X Y n).hom =
      SingularCochains.cohomologyPullback
        (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y))) n := by
  change SingularCochains.cohomologyPullback
    (TopCat.ofHom (projectionHomotopyEquiv X Y).toFun) n = _
  congr 1

/-- A generator of the second factor's singular cohomology generates the
product cohomology after pullback along the actual projection. -/
theorem cohomology_generated (n : ℕ)
    (η : SingularCochains.Cohomology (TopCat.of Y) n)
    (hη : ∀ y : SingularCochains.Cohomology (TopCat.of Y) n,
      ∃ a : ℚ, y = a • η)
    (z : SingularCochains.Cohomology (TopCat.of (X × Y)) n) :
    ∃ a : ℚ, z = a • (cohomologyIso X Y n).hom η := by
  obtain ⟨a, ha⟩ := hη ((cohomologyIso X Y n).inv z)
  refine ⟨a, ?_⟩
  calc
    z = (cohomologyIso X Y n).hom ((cohomologyIso X Y n).inv z) :=
      (Iso.inv_hom_id_apply (cohomologyIso X Y n) z).symm
    _ = a • (cohomologyIso X Y n).hom η := by rw [ha, map_smul]

end HodgeConjecture.ProductContractibleFactor

end
