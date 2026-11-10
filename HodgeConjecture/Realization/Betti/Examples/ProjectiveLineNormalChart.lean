module

public import HodgeConjecture.Realization.Betti.Examples.ComplexPointThom
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
public import HodgeConjecture.Realization.Betti.RelativeUnion

@[expose] public section

/-!
# The original finite normal chart as an actual map of relative pairs

The original finite chart identifies the complex line with its actual
open range in the projective-line point space. Its punctured complement
is precisely the preimage of the reciprocal chart. Original simplex maps
therefore identify the actual local relative cochain complexes. The
source comparison retains the original punctured finite coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineNormalChart

open CategoryTheory HomologicalComplex Opposite Simplicial
open ProjectiveLineAnalyticCover ProjectiveLineComplexPoints

abbrev space : TopCat := TopCat.of Point
abbrev first := SingularSubcomplexes.subsetSingular space finiteOpen
abbrev second := SingularSubcomplexes.subsetSingular space reciprocalOpen
abbrev localBoundary := RelativeUnion.localBoundary first second

/-- The original punctured finite chart as its actual continuous map. -/
def puncturedChart : C(PuncturedComplexCircle.Plane, ↥(finiteOpen ∩ reciprocalOpen)) :=
  ⟨overlapHomeomorph, overlapHomeomorph.continuous_toFun⟩

/-- The original finite homeomorphism, followed by the original contained-simplex comparison. -/
def finiteSSetIso : TopCat.toSSet.obj (TopCat.of ℂ) ≅ first.toSSet :=
  TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo (X := TopCat.of ℂ) (Y := TopCat.of finiteOpen) finiteHomeomorph) ≪≫
    (SingularSubcomplexes.subsetSingularIso space finiteOpen).symm

/-- The normal chart uses the original finite evaluation at every simplex point. -/
theorem finiteSSetIso_simplexMap (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of ℂ)).obj n)
    (t : SimplexCategory.toTop.obj n.unop) :
    SingularSubcomplexes.simplexMap space n (finiteSSetIso.hom.app n σ).val t =
      finite (SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) := rfl

/-- The actual punctured plane is exactly the original reciprocal-chart preimage in the finite chart. -/
theorem punctured_preimage : ComplexPointThom.puncturedSubcomplex =
    localBoundary.preimage finiteSSetIso.hom := by
  ext n σ
  change (∀ t, SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t ≠ 0) ↔
    ∀ t, finite (SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) ∈ reciprocalOpen
  constructor
  · intro h t
    exact (finite_mem_reciprocal_iff _).mpr (h t)
  · intro h t
    exact (finite_mem_reciprocal_iff _).mp (h t)

/-- The original normal-chart map restricted to the actual punctured subcomplexes. -/
def puncturedSSetMap : ComplexPointThom.puncturedSubcomplex.toSSet ⟶ localBoundary.toSSet :=
  RelativeCochains.subcomplexMap finiteSSetIso.hom punctured_preimage.le

/-- Pullback under the actual finite chart identifies the actual relative complexes. -/
def normalPullbackIso : RelativeCochains.complex localBoundary ≅
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullbackIso finiteSSetIso punctured_preimage

/-- The inverse chart pullback transports local complex-line classes to the actual normal-chart pair. -/
def normalClassIso (n : ℕ) :
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n ≅
      RelativeCochains.Cohomology localBoundary n :=
  (homologyMapIso normalPullbackIso n).symm

@[simp]
theorem normalClassIso_inv (n : ℕ) : (normalClassIso n).inv =
    homologyMap (RelativeCochains.pullback finiteSSetIso.hom punctured_preimage.le) n := rfl

@[simp]
theorem normalClassIso_hom (n : ℕ) :
    (normalClassIso n).hom = homologyMap normalPullbackIso.inv n := rfl

/-- Both original punctured-chart routes give the same original intersection simplex. -/
theorem punctured_map_intersection :
    SingularSubcomplexes.subtypeToSubset (TopCat.of ℂ) ComplexPointThom.punctured ≫
        puncturedSSetMap ≫ (RelativeUnion.intersectionIso first second).hom =
      TopCat.toSSet.map (TopCat.ofHom puncturedChart) ≫
        SingularSubcomplexes.subtypeToSubset space (finiteOpen ∩ reciprocalOpen) ≫
          (SSet.Subcomplex.eqToIso
            (SingularSubcomplexes.subsetSingular_inter space finiteOpen reciprocalOpen)).hom := by
  ext n σ
  apply Subtype.ext
  rfl

/-- The original contained-simplex comparisons intertwine the actual punctured finite-coordinate pullback. -/
theorem punctured_cohomology_comparison (n : ℕ) :
    homologyMap (SubcomplexCochains.pullback (RelativeUnion.intersectionIso first second).hom) n ≫
        homologyMap (SubcomplexCochains.pullback puncturedSSetMap) n ≫
          (ComplexPointThom.puncturedCohomologyIso n).hom =
      (SingularMayerVietoris.intersectionCohomologyIso space finiteOpen reciprocalOpen n).hom ≫
        SingularCochains.cohomologyPullback (TopCat.ofHom puncturedChart) n := by
  have h := congrArg
    (fun f ↦ homologyMap (SubcomplexCochains.pullback f) n) punctured_map_intersection
  change homologyMap (SubcomplexCochains.pullback
      (RelativeUnion.intersectionIso first second).hom) n ≫
      homologyMap (SubcomplexCochains.pullback puncturedSSetMap) n ≫
      homologyMap (SubcomplexCochains.pullback
        (SingularSubcomplexes.subtypeToSubset (TopCat.of ℂ) ComplexPointThom.punctured)) n =
    homologyMap (SubcomplexCochains.pullback
      (SSet.Subcomplex.eqToIso
        (SingularSubcomplexes.subsetSingular_inter space finiteOpen reciprocalOpen)).hom) n ≫
      homologyMap (SubcomplexCochains.pullback
        (SingularSubcomplexes.subtypeToSubset space (finiteOpen ∩ reciprocalOpen))) n ≫
      homologyMap (SubcomplexCochains.pullback
        (TopCat.toSSet.map (TopCat.ofHom puncturedChart))) n
  simpa only [SubcomplexCochains.pullback_comp, homologyMap_comp, Category.assoc] using h

end HodgeConjecture.ProjectiveLineNormalChart
