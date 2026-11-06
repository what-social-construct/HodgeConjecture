module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.SingularMayerVietoris

@[expose] public section

/-!
# The actual projective-line connecting isomorphism

The original two analytic charts are contractible. The native singular
Mayer–Vietoris connecting morphism therefore identifies degree one of
their actual overlap with degree two of the original projective-line
space. The explicit radial homotopy equivalence identifies its source
with degree one of the native circle, through the actual pullback.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSingularCohomology

open CategoryTheory CategoryTheory.Limits
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

/-- Both original analytic chart groups vanish in every positive degree. -/
theorem isZero_pairCohomology (n : ℕ) (hn : n ≠ 0) :
    IsZero (ModuleCat.of ℚ
      (SingularCochains.Cohomology (TopCat.of finiteOpen) n ×
        SingularCochains.Cohomology (TopCat.of reciprocalOpen) n)) := by
  have := ModuleCat.isZero_iff_subsingleton.mp
    (SingularContractible.isZero_cohomology finiteOpen n hn)
  have := ModuleCat.isZero_iff_subsingleton.mp
    (SingularContractible.isZero_cohomology reciprocalOpen n hn)
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- The actual chart-difference map has zero source in positive degree. -/
theorem difference_eq_zero (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.difference (TopCat.of Point) finiteOpen reciprocalOpen n = 0 :=
  (isZero_pairCohomology n hn).eq_of_src _ _

/-- The actual restriction to both charts has zero target in positive degree. -/
theorem restriction_eq_zero (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.restriction (TopCat.of Point) finiteOpen reciprocalOpen n = 0 :=
  (isZero_pairCohomology n hn).eq_of_tgt _ _

/-- The original native degree-one Mayer–Vietoris connecting morphism. -/
def connecting :
    SingularCochains.Cohomology (TopCat.of ↥(finiteOpen ∩ reciprocalOpen)) 1 ⟶
      SingularCochains.Cohomology (TopCat.of Point) 2 :=
  SingularMayerVietoris.connecting (TopCat.of Point) finiteOpen reciprocalOpen
    isOpen_finiteOpen isOpen_reciprocalOpen cover 1

instance connecting_mono : Mono connecting := by
  have h := (SingularMayerVietoris.intersectionSequence_exact (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1).mono_g
      (by simpa using difference_eq_zero 1 (by decide))
  exact h

instance connecting_epi : Epi connecting := by
  have h := (SingularMayerVietoris.unionSequence_exact (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1).epi_f
      (by simpa using restriction_eq_zero 2 (by decide))
  exact h

instance connecting_isIso : IsIso connecting := isIso_of_mono_of_epi connecting

/-- Exactness proves that the original connecting map itself is an isomorphism. -/
def connectingIso :
    SingularCochains.Cohomology (TopCat.of ↥(finiteOpen ∩ reciprocalOpen)) 1 ≅
      SingularCochains.Cohomology (TopCat.of Point) 2 :=
  asIso connecting

@[simp]
theorem connectingIso_hom : connectingIso.hom = connecting := rfl

/-- Its forward map is exactly the existing native singular connecting map. -/
theorem connectingIso_hom_eq_mayerVietoris :
    connectingIso.hom = SingularMayerVietoris.connecting (TopCat.of Point)
      finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1 := rfl

/-- Actual radial pullback followed by the original connecting isomorphism. -/
def circleIso :
    SingularCochains.Cohomology (TopCat.of Circle) 1 ≅
      SingularCochains.Cohomology (TopCat.of Point) 2 :=
  SingularHomotopy.homotopyEquivIso overlapCircleHomotopyEquiv 1 ≪≫ connectingIso

/-- This identification uses the original radial map and the original connecting map. -/
theorem circleIso_hom :
    circleIso.hom =
      SingularCochains.cohomologyPullback (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 ≫
        connecting := rfl

end HodgeConjecture.ProjectiveLineSingularCohomology
