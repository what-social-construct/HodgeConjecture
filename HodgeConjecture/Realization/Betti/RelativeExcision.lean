module

public import HodgeConjecture.Realization.Betti.RelativeUnion
public import HodgeConjecture.Realization.Betti.ShortExactQuasiIso

@[expose] public section

/-!
# Actual relative singular excision for a two-open cover

The original full-to-small cochain quasi-isomorphism induces a
quasi-isomorphism on relative kernels, using the actual short exact
sequences and the original quotient identification. The strict simplicial
union comparison then gives excision by the original restriction map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeExcision

open CategoryTheory HomologicalComplex

variable {S : SSet.{0}} (A B : S.Subcomplex)

/-- Original relative pullback from the ambient simplicial set to its actual union. -/
def toUnion : RelativeCochains.complex B ⟶
    RelativeCochains.complex (RelativeUnion.unionBoundary A B) :=
  RelativeCochains.pullback (A := RelativeUnion.unionBoundary A B) (B := B)
    (A ⊔ B).ι le_rfl

/-- Original relative restriction to the first subcomplex and its actual overlap. -/
def restriction : RelativeCochains.complex B ⟶
    RelativeCochains.complex (RelativeUnion.localBoundary A B) :=
  RelativeCochains.pullback (A := RelativeUnion.localBoundary A B) (B := B) A.ι le_rfl

theorem toUnion_excisionIso :
    toUnion A B ≫ (RelativeUnion.excisionIso A B).hom = restriction A B := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- The quotient in the full/small relative diagram is the original B-cochain complex,
through its proved actual simplex isomorphism. -/
theorem quotient_quasiIso :
    QuasiIso (SubcomplexCochains.pullback
      (RelativeCochains.subcomplexMap (A := RelativeUnion.unionBoundary A B) (B := B)
        (A ⊔ B).ι le_rfl)) := by
  change QuasiIso (SubcomplexCochains.pullback (RelativeUnion.boundaryIso A B).hom)
  have : IsIso (SubcomplexCochains.pullback (RelativeUnion.boundaryIso A B).hom) :=
    inferInstanceAs (IsIso (SingularMayerVietoris.pullbackIso (RelativeUnion.boundaryIso A B)).hom)
  infer_instance

/-- The proved original absolute quasi-isomorphism induces one on actual relative kernels. -/
theorem toUnion_quasiIso
    (h : QuasiIso (SubcomplexCochains.pullback (A ⊔ B).ι)) : QuasiIso (toUnion A B) :=
  ShortExactQuasiIso.left
    (RelativeCochains.shortComplexMap (A := RelativeUnion.unionBoundary A B) (B := B)
      (A ⊔ B).ι le_rfl)
    (RelativeCochains.shortComplex_shortExact B)
    (RelativeCochains.shortComplex_shortExact (RelativeUnion.unionBoundary A B)) h
    (quotient_quasiIso A B)

/-- Excision is induced by original relative restriction, after a proved full/small comparison. -/
theorem restriction_quasiIso
    (h : QuasiIso (SubcomplexCochains.pullback (A ⊔ B).ι)) : QuasiIso (restriction A B) := by
  rw [← toUnion_excisionIso]
  have := toUnion_quasiIso A B h
  infer_instance

/-- Relative restriction retains the original absolute restriction and relative forgetting. -/
@[reassoc]
theorem toUnion_forget :
    toUnion A B ≫ RelativeCochains.inclusion (RelativeUnion.unionBoundary A B) =
      RelativeCochains.inclusion B ≫ SubcomplexCochains.pullback (A ⊔ B).ι :=
  RelativeCochains.pullback_inclusion (A ⊔ B).ι le_rfl

section Topological

variable (X : TopCat.{0}) (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

local notation "A" => SingularSubcomplexes.subsetSingular X U
local notation "B" => SingularSubcomplexes.subsetSingular X V

include hU hV hcover

/-- Genuine open-cover subdivision and dualization prove relative full/small excision. -/
theorem smallRestriction_quasiIso : QuasiIso (toUnion A B) :=
  toUnion_quasiIso A B (CochainDualComparison.smallRestriction_quasiIso X U V hU hV hcover)

/-- Original relative restriction is a quasi-isomorphism for the genuine two-open cover. -/
theorem relativeRestriction_quasiIso : QuasiIso (restriction A B) :=
  restriction_quasiIso A B (CochainDualComparison.smallRestriction_quasiIso X U V hU hV hcover)

/-- The relative full/small cohomology comparison has the original restriction as forward map. -/
def smallCohomologyIso (n : ℕ) : RelativeCochains.Cohomology B n ≅
    RelativeCochains.Cohomology (RelativeUnion.unionBoundary A B) n := by
  have := smallRestriction_quasiIso X U V hU hV hcover
  exact isoOfQuasiIsoAt (toUnion A B) n

@[simp]
theorem smallCohomologyIso_hom (n : ℕ) :
    (smallCohomologyIso X U V hU hV hcover n).hom = homologyMap (toUnion A B) n := rfl

/-- Actual relative excision, from the original ambient pair to the original first-chart pair. -/
def excisionIso (n : ℕ) : RelativeCochains.Cohomology B n ≅
    RelativeCochains.Cohomology (RelativeUnion.localBoundary A B) n :=
  smallCohomologyIso X U V hU hV hcover n ≪≫
    homologyMapIso (RelativeUnion.excisionIso A B) n

/-- Its forward map is exactly the original relative restriction to the first chart. -/
@[simp]
theorem excisionIso_hom (n : ℕ) :
    (excisionIso X U V hU hV hcover n).hom = homologyMap (restriction A B) n := by
  rw [excisionIso, Iso.trans_hom, smallCohomologyIso_hom]
  change homologyMap (toUnion A B) n ≫ homologyMap (RelativeUnion.excisionIso A B).hom n = _
  rw [← homologyMap_comp, toUnion_excisionIso]

/-- Original relative-to-absolute forgetting commutes with the proved full/small comparisons. -/
@[reassoc]
theorem smallCohomologyIso_forget (n : ℕ) :
    (smallCohomologyIso X U V hU hV hcover n).hom ≫
        RelativeCochains.forget (RelativeUnion.unionBoundary A B) n =
      RelativeCochains.forget B n ≫
        (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).hom := by
  rw [smallCohomologyIso_hom, CochainDualComparison.smallCohomologyIso_hom]
  change homologyMap (toUnion A B) n ≫
      homologyMap (RelativeCochains.inclusion (RelativeUnion.unionBoundary A B)) n =
    homologyMap (RelativeCochains.inclusion B) n ≫
      homologyMap (SubcomplexCochains.pullback (A ⊔ B).ι) n
  rw [← homologyMap_comp, ← homologyMap_comp, toUnion_forget]

end Topological

end HodgeConjecture.RelativeExcision
