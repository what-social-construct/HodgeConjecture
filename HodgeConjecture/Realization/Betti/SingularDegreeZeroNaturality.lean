module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import HodgeConjecture.Realization.Betti.SingularPathConnected

@[expose] public section

/-!
# Naturality of the original degree-zero coordinates

The canonical identification of actual cohomology with singular zero-cocycles
intertwines continuous pullback and the original simplex precomposition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularDegreeZeroNaturality

open CategoryTheory HomologicalComplex

universe u

/-- The unique zero-cocycle representative of an actual degree-zero class. -/
def representative (X : Type u) [TopologicalSpace X] :
    SingularCochains.Cohomology (TopCat.of X) 0 ⟶ (SingularCochains.complex (TopCat.of X)).X 0 :=
  (CochainComplex.isoHomologyπ₀ (SingularCochains.complex (TopCat.of X))).inv ≫
    (SingularCochains.complex (TopCat.of X)).iCycles 0

/-- The existing degree-zero isomorphism evaluates the canonical cocycle representative. -/
theorem cohomologyZeroIso_apply (X : Type u) [TopologicalSpace X]
    (z : SingularCochains.Cohomology (TopCat.of X) 0) :
    ((SingularCochains.cohomologyZeroIso X).hom z).val =
      SingularCochains.continuousCochainEquiv X 0 (representative X z) := by
  unfold SingularCochains.cohomologyZeroIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  change SingularCochains.continuousCochainEquiv X 0 _ = _
  apply congrArg (SingularCochains.continuousCochainEquiv X 0)
  let K := SingularCochains.complex (TopCat.of X)
  change ((K.cyclesIsoSc' 0 0 1 (by simp) ((ComplexShape.up ℕ).next_eq' (by decide))).hom ≫
    (K.sc' 0 0 1).moduleCatCyclesIso.hom ≫ (K.sc' 0 0 1).moduleCatLeftHomologyData.i)
      ((CochainComplex.isoHomologyπ₀ K).inv z) =
    (K.iCycles 0) ((CochainComplex.isoHomologyπ₀ K).inv z)
  rw [ShortComplex.moduleCatCyclesIso_hom_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  rfl

/-- The canonical cocycle representatives commute with continuous pullback. -/
theorem representative_pullback {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SingularCochains.cohomologyPullback (TopCat.ofHom f) 0 ≫ representative X =
      representative Y ≫ (SingularCochains.pullback (TopCat.ofHom f)).f 0 := by
  simp only [representative, SingularCochains.cohomologyPullback,
    CochainComplex.isoHomologyπ₀_inv_naturality_assoc, HomologicalComplex.cyclesMap_i,
    Category.assoc]

/-- Continuous pullback on actual cohomology agrees with the established H⁰ model. -/
theorem cohomologyZeroIso_pullback {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (z : SingularCochains.Cohomology (TopCat.of Y) 0) :
    (SingularCochains.cohomologyZeroIso X).hom
        (SingularCochains.cohomologyPullback (TopCat.ofHom f) 0 z) =
      SingularDegreeZero.pullback f ((SingularCochains.cohomologyZeroIso Y).hom z) := by
  apply Subtype.ext
  rw [cohomologyZeroIso_apply]
  funext σ
  rw [SingularDegreeZero.pullback_apply, cohomologyZeroIso_apply]
  have hr := congrArg (fun p ↦ p z) (representative_pullback f)
  change representative X (SingularCochains.cohomologyPullback (TopCat.ofHom f) 0 z) =
    (SingularCochains.pullback (TopCat.ofHom f)).f 0 (representative Y z) at hr
  rw [hr]
  exact SingularCochains.continuousCochainEquiv_pullback f 0 _ σ

/-- The inverse coordinate map also commutes with actual continuous pullback. -/
theorem cohomologyZeroIso_inv_pullback {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (z : SingularDegreeZero.H0 Y) :
    SingularCochains.cohomologyPullback (TopCat.ofHom f) 0
        ((SingularCochains.cohomologyZeroIso Y).inv z) =
      (SingularCochains.cohomologyZeroIso X).inv (SingularDegreeZero.pullback f z) := by
  apply (SingularCochains.cohomologyZeroIso X).toLinearEquiv.injective
  change (SingularCochains.cohomologyZeroIso X).hom _ =
    (SingularCochains.cohomologyZeroIso X).hom _
  rw [cohomologyZeroIso_pullback]
  simp

/-- The actual degree-zero class represented by the original constant cocycle. -/
def constantClass (X : Type u) [TopologicalSpace X] (q : ℚ) :
    SingularCochains.Cohomology (TopCat.of X) 0 :=
  (SingularCochains.cohomologyZeroIso X).inv (SingularDegreeZero.constantClass X q)

/-- Pullback preserves the original constant cohomology classes. -/
theorem pullback_constantClass {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (q : ℚ) :
    SingularCochains.cohomologyPullback (TopCat.ofHom f) 0 (constantClass Y q) =
      constantClass X q := by
  rw [constantClass, cohomologyZeroIso_inv_pullback, SingularDegreeZero.pullback_constantClass]
  rfl

end HodgeConjecture.SingularDegreeZeroNaturality
