module

public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# Homotopy invariance of actual rational singular cohomology

Transpose the components of a native rational chain homotopy and identify
the resulting dual complex with the original singular cochains. Original
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
    (h : Homotopy f g) : Homotopy (RationalDual.dualMap f) (RationalDual.dualMap g) where
  hom i j := ModuleCat.ofHom (h.hom j i).hom.dualMap
  zero i j hij := by
    rw [h.zero j i hij]
    apply ModuleCat.hom_ext
    ext φ x
    simp
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex, add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      let ψ : Module.Dual ℚ (L.X 0) := φ
      change ψ (f.f 0 x) = ψ (L.d 1 0 (h.hom 0 1 x)) + ψ (g.f 0 x)
      have he := congrArg (fun p : K.X 0 ⟶ L.X 0 ↦ ψ (p x)) (h.comm 0)
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at he
      simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, map_add] using he
    | succ n =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      let ψ : Module.Dual ℚ (L.X (n + 1)) := φ
      change ψ (f.f (n + 1) x) =
        ψ (L.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x)) +
          ψ (h.hom n (n + 1) (K.d (n + 1) n x)) + ψ (g.f (n + 1) x)
      have he := congrArg (fun p : K.X (n + 1) ⟶ L.X (n + 1) ↦ ψ (p x)) (h.comm (n + 1))
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at he
      simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, map_add, add_comm, add_left_comm, add_assoc] using he

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
