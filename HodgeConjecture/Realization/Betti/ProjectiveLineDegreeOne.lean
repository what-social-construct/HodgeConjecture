module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology
public import HodgeConjecture.Realization.Betti.Examples.CircleTopology
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality

/-!
# Vanishing of the first rational cohomology of the projective line

The original two affine charts are contractible and their punctured
intersection is path connected. The degree-zero difference is therefore
surjective. Exactness of the already constructed singular Mayer–Vietoris
sequence gives the actual degree-one vanishing theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDegreeOne

open CategoryTheory CategoryTheory.Limits ProjectiveLineComplexPoints
open ProjectiveLineAnalyticCover

abbrev Overlap := ↥(finiteOpen ∩ reciprocalOpen)

/-- The actual overlap of the two affine charts is path connected. -/
instance overlapPathConnected : PathConnectedSpace Overlap := by
  letI : PathConnectedSpace PuncturedComplexCircle.Radius :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioi (0 : ℝ)).isPathConnected ⟨1, zero_lt_one⟩)
  letI : PathConnectedSpace PuncturedComplexCircle.Plane :=
    PuncturedComplexCircle.polarHomeomorph.symm.pathConnectedSpace
  exact overlapHomeomorph.pathConnectedSpace

def overlapPoint : Overlap :=
  overlapHomeomorph ⟨1, one_ne_zero⟩

/-- Every original degree-zero class on the overlap is constant. -/
theorem overlapH0_eq_constant (z : SingularCochains.Cohomology (TopCat.of Overlap) 0) :
    ∃ q : ℚ, z = SingularDegreeZeroNaturality.constantClass Overlap q := by
  let h := (SingularCochains.cohomologyZeroIso Overlap).hom z
  let q := SingularDegreeZero.equivConstants Overlap overlapPoint h
  refine ⟨q, ?_⟩
  apply (SingularCochains.cohomologyZeroIso Overlap).toLinearEquiv.injective
  have hh : h = SingularDegreeZero.constantClass Overlap q := by
    calc
      h = (SingularDegreeZero.equivConstants Overlap overlapPoint).symm q := by
        exact ((SingularDegreeZero.equivConstants Overlap overlapPoint).symm_apply_apply h).symm
      _ = SingularDegreeZero.constantClass Overlap q :=
        SingularDegreeZero.equivConstants_symm_apply Overlap overlapPoint q
  change (SingularCochains.cohomologyZeroIso Overlap).hom z =
    (SingularCochains.cohomologyZeroIso Overlap).hom
      ((SingularCochains.cohomologyZeroIso Overlap).inv
        (SingularDegreeZero.constantClass Overlap q))
  rw [Iso.inv_hom_id_apply]
  exact hh

/-- The actual chart difference is surjective in degree zero. -/
theorem difference_zero_surjective :
    Function.Surjective
      (SingularMayerVietoris.difference (TopCat.of Point) finiteOpen reciprocalOpen 0) := by
  intro z
  obtain ⟨q, rfl⟩ := overlapH0_eq_constant z
  refine ⟨(SingularDegreeZeroNaturality.constantClass finiteOpen q, 0), ?_⟩
  rw [SingularMayerVietoris.difference_apply]
  simp only [map_zero, sub_zero]
  let inc : C(Overlap, finiteOpen) :=
    ⟨fun x ↦ ⟨x.val, x.property.1⟩,
      continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)⟩
  change SingularCochains.cohomologyPullback (TopCat.ofHom inc) 0
      (SingularDegreeZeroNaturality.constantClass finiteOpen q) =
    SingularDegreeZeroNaturality.constantClass Overlap q
  exact SingularDegreeZeroNaturality.pullback_constantClass inc q

/-- The original rational singular `H¹(P¹(ℂ), ℚ)` vanishes. -/
theorem isZero_h1 :
    IsZero (SingularCochains.Cohomology (TopCat.of Point) 1) := by
  letI : Epi (SingularMayerVietoris.difference (TopCat.of Point)
      finiteOpen reciprocalOpen 0) :=
    (ModuleCat.epi_iff_surjective _).mpr difference_zero_surjective
  have hconnect : SingularMayerVietoris.connecting (TopCat.of Point)
      finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 0 = 0 := by
    apply (cancel_epi (SingularMayerVietoris.difference (TopCat.of Point)
      finiteOpen reciprocalOpen 0)).mp
    exact SingularMayerVietoris.difference_comp_connecting (TopCat.of Point)
      finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 0
  letI : Epi (SingularMayerVietoris.connecting (TopCat.of Point)
      finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 0) := by
    have h := (SingularMayerVietoris.unionSequence_exact (TopCat.of Point)
      finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 0).epi_f
        (by simpa using ProjectiveLineSingularCohomology.restriction_eq_zero 1 (by decide))
    exact h
  exact IsZero.of_epi_eq_zero _ hconnect

end HodgeConjecture.ProjectiveLineDegreeOne

end
