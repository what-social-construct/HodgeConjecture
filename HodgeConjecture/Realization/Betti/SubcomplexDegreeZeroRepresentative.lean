module

public import HodgeConjecture.Realization.Betti.SubcomplexConnectingRepresentative
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality

@[expose] public section

/-!
# The original degree-zero value of a native cocycle class

In degree zero, no coboundaries are present. The canonical representative
of the native class of a zero-cocycle is therefore that original cochain.
This identifies simplex values used in connecting-representative calculations
with the existing actual degree-zero cohomology coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SubcomplexDegreeZeroRepresentative

open CategoryTheory HomologicalComplex SubcomplexConnectingRepresentative

universe u

theorem representative_cocycleClass (X : Type u) [TopologicalSpace X]
    (φ : Cocycle (TopCat.toSSet.obj (TopCat.of X)) 0) :
    SingularDegreeZeroNaturality.representative X (cocycleClass _ 0 φ) = φ.val := by
  let K := SingularCochains.complex (TopCat.of X)
  let c := K.cyclesMk φ.val 1 (by simp) (by
    rw [SingularCochains.complex_d]
    exact φ.property)
  change K.iCycles 0
    ((CochainComplex.isoHomologyπ₀ K).toLinearEquiv.symm
      ((CochainComplex.isoHomologyπ₀ K).toLinearEquiv c)) = φ.val
  rw [LinearEquiv.symm_apply_apply]
  exact K.i_cyclesMk φ.val 1 (by simp) _

/-- The established H⁰ coordinate recovers the original continuous zero-cochain values. -/
theorem cohomologyZeroIso_cocycleClass (X : Type u) [TopologicalSpace X]
    (φ : Cocycle (TopCat.toSSet.obj (TopCat.of X)) 0) :
    ((SingularCochains.cohomologyZeroIso X).hom (cocycleClass _ 0 φ)).val =
      SingularCochains.continuousCochainEquiv X 0 φ.val := by
  rw [SingularDegreeZeroNaturality.cohomologyZeroIso_apply, representative_cocycleClass]

/-- Actual evaluation at a point uses precisely the original constant singular zero-simplex. -/
theorem eval_cocycleClass (X : Type u) [TopologicalSpace X]
    (φ : Cocycle (TopCat.toSSet.obj (TopCat.of X)) 0) (x : X) :
    SingularDegreeZero.eval X ((SingularCochains.cohomologyZeroIso X).hom
      (cocycleClass _ 0 φ)) x =
      φ.val (SingularDegreeZero.simplexEquivSingularSet X 0
        (SingularDegreeZero.pointSimplex X x)) := by
  change ((SingularCochains.cohomologyZeroIso X).hom (cocycleClass _ 0 φ)).val
    (SingularDegreeZero.pointSimplex X x) = _
  rw [cohomologyZeroIso_cocycleClass]
  rfl

end HodgeConjecture.SubcomplexDegreeZeroRepresentative
