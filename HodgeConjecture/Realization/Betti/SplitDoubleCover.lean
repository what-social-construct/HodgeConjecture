module

public import HodgeConjecture.Realization.Betti.SingularDoubleCover
public import HodgeConjecture.Geometry.SplitDoubleCover
public import HodgeConjecture.Geometry.ComplexPointsCoproduct
public import HodgeConjecture.Realization.Betti.Scheme
public import HodgeConjecture.Realization.Betti.SingularHomotopy

@[expose] public section

/-!
# Native singular transfer for the actual scheme split double cover

The canonical analytic coproduct homeomorphism identifies the original
scheme-valued complex points with the actual topological disjoint sum.
The independently proved singular cochain decomposition computes the
upstairs native cohomology in every degree. Transfer is the sum of the
pullbacks along the original scheme inclusions, and has degree two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SplitDoubleCoverBetti

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SingularCochains

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))

abbrev BaseBetti (n : ℕ) := SchemeBetti.Cohomology p n
abbrev CoverBetti (n : ℕ) := SchemeBetti.Cohomology (SplitDoubleCover.sourceStructure p) n

/-- Canonical analytic identification of the original scheme coproduct,
retaining its exact composite structure morphism. -/
def pointHomeomorph :
    (Scheme.ComplexPoints p ⊕ Scheme.ComplexPoints p) ≃ₜ
      Scheme.ComplexPoints (SplitDoubleCover.sourceStructure p) :=
  Scheme.ComplexPoints.coprodHomeomorph p p (SplitDoubleCover.sourceStructure p)
    (SplitDoubleCover.inl_sourceStructure p) (SplitDoubleCover.inr_sourceStructure p)

private def comparisonMap : SingularDoubleCover.space (SchemeBetti.space p) ⟶
    SchemeBetti.space (SplitDoubleCover.sourceStructure p) :=
  TopCat.ofHom ⟨pointHomeomorph p, (pointHomeomorph p).continuous_toFun⟩

private theorem comparison_inl :
    SingularDoubleCover.inclusion (SchemeBetti.space p) false ≫ comparisonMap p =
      SchemeBetti.map (SplitDoubleCover.inl X)
        (SplitDoubleCover.inl_sourceStructure p) := by
  ext z : 1
  exact Scheme.ComplexPoints.coprodHomeomorph_inl p p
    (SplitDoubleCover.sourceStructure p) (SplitDoubleCover.inl_sourceStructure p)
    (SplitDoubleCover.inr_sourceStructure p) z

private theorem comparison_inr :
    SingularDoubleCover.inclusion (SchemeBetti.space p) true ≫ comparisonMap p =
      SchemeBetti.map (SplitDoubleCover.inr X)
        (SplitDoubleCover.inr_sourceStructure p) := by
  ext z : 1
  exact Scheme.ComplexPoints.coprodHomeomorph_inr p p
    (SplitDoubleCover.sourceStructure p) (SplitDoubleCover.inl_sourceStructure p)
    (SplitDoubleCover.inr_sourceStructure p) z

/-- The native upstairs group decomposes by the canonical analytic
homeomorphism and the proved decomposition of the actual singular complex. -/
def cohomologyEquiv (n : ℕ) : CoverBetti p n ≃ₗ[ℚ] BaseBetti p n × BaseBetti p n :=
  (SingularHomotopy.homeomorphIso (pointHomeomorph p) n).toLinearEquiv.trans
    (SingularDoubleCover.cohomologyEquiv (SchemeBetti.space p) n)

theorem cohomologyEquiv_fst (n : ℕ) (z : CoverBetti p n) :
    (cohomologyEquiv p n z).1 =
      SchemeBetti.pullback (SplitDoubleCover.inl X)
        (SplitDoubleCover.inl_sourceStructure p) n z := by
  change cohomologyPullback (SingularDoubleCover.inclusion (SchemeBetti.space p) false) n
    (cohomologyPullback (comparisonMap p) n z) = _
  have h := cohomologyPullback_comp
    (SingularDoubleCover.inclusion (SchemeBetti.space p) false) (comparisonMap p) n
  rw [comparison_inl] at h
  exact congrArg (fun f ↦ f z) h.symm

theorem cohomologyEquiv_snd (n : ℕ) (z : CoverBetti p n) :
    (cohomologyEquiv p n z).2 =
      SchemeBetti.pullback (SplitDoubleCover.inr X)
        (SplitDoubleCover.inr_sourceStructure p) n z := by
  change cohomologyPullback (SingularDoubleCover.inclusion (SchemeBetti.space p) true) n
    (cohomologyPullback (comparisonMap p) n z) = _
  have h := cohomologyPullback_comp
    (SingularDoubleCover.inclusion (SchemeBetti.space p) true) (comparisonMap p) n
  rw [comparison_inr] at h
  exact congrArg (fun f ↦ f z) h.symm

/-- Original singular pullback of the actual scheme fold. -/
def actualPull (n : ℕ) : BaseBetti p n →ₗ[ℚ] CoverBetti p n :=
  (SchemeBetti.pullback (SplitDoubleCover.fold X) rfl n).hom

/-- The actual cochain transfer is the sum of pullbacks along the two
original scheme inclusions. -/
def cochainPush :
    complex (SchemeBetti.space (SplitDoubleCover.sourceStructure p)) ⟶
      complex (SchemeBetti.space p) :=
  SingularCochains.pullback (SchemeBetti.map (SplitDoubleCover.inl X)
      (SplitDoubleCover.inl_sourceStructure p)) +
    SingularCochains.pullback (SchemeBetti.map (SplitDoubleCover.inr X)
      (SplitDoubleCover.inr_sourceStructure p))

/-- Native cohomological transfer, defined as the sum of the actual
inclusion pullbacks rather than by a proposed coordinate formula. -/
def actualPush (n : ℕ) : CoverBetti p n →ₗ[ℚ] BaseBetti p n :=
  (SchemeBetti.pullback (SplitDoubleCover.inl X)
      (SplitDoubleCover.inl_sourceStructure p) n).hom +
    (SchemeBetti.pullback (SplitDoubleCover.inr X)
      (SplitDoubleCover.inr_sourceStructure p) n).hom

theorem actualPush_eq_homologyMap (n : ℕ) :
    actualPush p n = (HomologicalComplex.homologyMap (cochainPush p) n).hom := by
  simp only [actualPush, cochainPush, HomologicalComplex.homologyMap_add]
  rfl

private theorem inl_pull_actualPull (n : ℕ) :
    (SchemeBetti.pullback (SplitDoubleCover.inl X)
      (SplitDoubleCover.inl_sourceStructure p) n).hom.comp (actualPull p n) =
        LinearMap.id := by
  have h := SchemeBetti.pullback_comp (SplitDoubleCover.inl X)
    (SplitDoubleCover.inl_sourceStructure p) (SplitDoubleCover.fold X) rfl n
  simp only [SplitDoubleCover.inl_fold, SchemeBetti.pullback_id] at h
  exact congrArg ModuleCat.Hom.hom h.symm

private theorem inr_pull_actualPull (n : ℕ) :
    (SchemeBetti.pullback (SplitDoubleCover.inr X)
      (SplitDoubleCover.inr_sourceStructure p) n).hom.comp (actualPull p n) =
        LinearMap.id := by
  have h := SchemeBetti.pullback_comp (SplitDoubleCover.inr X)
    (SplitDoubleCover.inr_sourceStructure p) (SplitDoubleCover.fold X) rfl n
  simp only [SplitDoubleCover.inr_fold, SchemeBetti.pullback_id] at h
  exact congrArg ModuleCat.Hom.hom h.symm

/-- The diagonal formula is a consequence of the actual inclusion/fold
identities and the independently proved native cohomology decomposition. -/
theorem cohomologyEquiv_pull (n : ℕ) (z : BaseBetti p n) :
    cohomologyEquiv p n (actualPull p n z) = (z, z) := by
  apply Prod.ext
  · rw [cohomologyEquiv_fst]
    exact LinearMap.congr_fun (inl_pull_actualPull p n) z
  · rw [cohomologyEquiv_snd]
    exact LinearMap.congr_fun (inr_pull_actualPull p n) z

/-- The sum formula is proved for the transfer already defined by native
inclusion pullbacks. -/
theorem actualPush_eq_sum (n : ℕ) (z : CoverBetti p n) :
    actualPush p n z = (cohomologyEquiv p n z).1 + (cohomologyEquiv p n z).2 := by
  rw [cohomologyEquiv_fst, cohomologyEquiv_snd]
  rfl

theorem actualPush_actualPull (n : ℕ) :
    (actualPush p n).comp (actualPull p n) = (2 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro z
  change actualPush p n (actualPull p n z) = (2 : ℚ) • z
  rw [actualPush_eq_sum, cohomologyEquiv_pull]
  simp only [two_smul]

/-- Positive-degree native singular transfer for the original finite étale
scheme fold, in every cohomological degree. -/
def degreeTransfer (n : ℕ) : RationalDegreeTransfer (CoverBetti p n) (BaseBetti p n) where
  pull := actualPull p n
  push := actualPush p n
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := actualPush_actualPull p n

end HodgeConjecture.SplitDoubleCoverBetti

end
