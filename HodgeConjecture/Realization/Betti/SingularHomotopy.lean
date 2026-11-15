module

public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# Homotopy invariance of actual rational singular cohomology

Apply the native opposite-homotopy and additive-functor constructions, then
identify the resulting dual complex with the original singular cochains. Original
continuous homotopies therefore induce equal cohomology pullbacks in all
degrees, and original homotopy equivalences induce cohomology isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularHomotopy

open CategoryTheory HomologicalComplex

/-- The transpose of an actual rational chain homotopy, with no degree shift or extra sign. -/
def dualHomotopy {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) : Homotopy (RationalDual.dualMap f) (RationalDual.dualMap g) :=
  RationalDual.functor.mapHomotopy h.op

/-- A native continuous homotopy gives a homotopy on the original singular cochain complexes. -/
def cochainHomotopy {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : TopCat.Homotopy f g) :
    Homotopy (SingularCochains.pullback f) (SingularCochains.pullback g) := by
  let hc := h.toSSet.chainComplexMap (ModuleCat.of ℚ ℚ)
  let hd := dualHomotopy hc
  have hn := (hd.compRight (CochainDualComparison.comparisonIso (TopCat.toSSet.obj X)).hom).compLeft
    (CochainDualComparison.comparisonIso (TopCat.toSSet.obj Y)).inv
  change Homotopy (SubcomplexCochains.pullback (TopCat.toSSet.map f))
    (SubcomplexCochains.pullback (TopCat.toSSet.map g))
  rw [CochainDualComparison.pullback_eq_dualMap, CochainDualComparison.pullback_eq_dualMap]
  exact hn

/-- Original continuously homotopic maps have the same pullback on actual singular cohomology. -/
theorem cohomologyPullback_eq_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : TopCat.Homotopy f g) (n : ℕ) :
    SingularCochains.cohomologyPullback f n = SingularCochains.cohomologyPullback g n :=
  (cochainHomotopy h).homologyMap_eq n

/-- The same equality for the existing continuous-map homotopy relation. -/
theorem cohomologyPullback_eq_of_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (n : ℕ) :
    SingularCochains.cohomologyPullback (TopCat.ofHom f) n =
      SingularCochains.cohomologyPullback (TopCat.ofHom g) n := by
  obtain ⟨h⟩ := h
  exact cohomologyPullback_eq_of_homotopy h n

/-- A proved topological homotopy equivalence acts contravariantly on actual cohomology. -/
def homotopyEquivIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of Y) n ≅ SingularCochains.Cohomology (TopCat.of X) n where
  hom := SingularCochains.cohomologyPullback (TopCat.ofHom e.toFun) n
  inv := SingularCochains.cohomologyPullback (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← SingularCochains.cohomologyPullback_comp]
    have h := cohomologyPullback_eq_of_homotopic e.right_inv n
    simpa using h
  inv_hom_id := by
    rw [← SingularCochains.cohomologyPullback_comp]
    have h := cohomologyPullback_eq_of_homotopic e.left_inv n
    simpa using h

/-- Homeomorphism invariance uses the original continuous maps in both directions. -/
def homeomorphIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of Y) n ≅ SingularCochains.Cohomology (TopCat.of X) n :=
  homotopyEquivIso e.toHomotopyEquiv n

end HodgeConjecture.SingularHomotopy
