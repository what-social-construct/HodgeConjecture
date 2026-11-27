module

public import HodgeConjecture.Realization.Betti.RelativeUnionSplit

@[expose] public section

/-!
# Original relative support extensions split a genuine two-open cover

The sum of the original identity-pair extensions is an isomorphism from
`H*(X,U) × H*(X,V)` to `H*(X,U ∩ V)` when `U,V` form an open cover.
The proof uses actual compatible cochain gluing, the original full/small
quasi-isomorphism, and the original restriction-based excision maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeAdditivity

open CategoryTheory HomologicalComplex SingularSubcomplexes

section Simplicial

variable {S : SSet.{0}}

/-- The original identity pair map: vanishing on a larger boundary implies
vanishing on its smaller subcomplex. -/
def extension (C D : S.Subcomplex) (h : C ≤ D) :
    RelativeCochains.complex D ⟶ RelativeCochains.complex C :=
  RelativeCochains.pullback (𝟙 S) (by simpa only [SSet.Subcomplex.preimage_id] using h)

@[simp]
theorem extension_val (C D : S.Subcomplex) (h : C ≤ D) (n : ℕ)
    (φ : RelativeCochains.Cochain D n) : ((extension C D h).f n φ).val = φ.val := rfl

@[simp]
theorem extension_self (C : S.Subcomplex) : extension C C le_rfl = 𝟙 _ := by
  ext n φ
  apply Subtype.ext
  rfl

theorem extension_trans (C D E : S.Subcomplex) (hCD : C ≤ D) (hDE : D ≤ E) :
    extension D E hDE ≫ extension C D hCD = extension C E (hCD.trans hDE) := by
  ext n φ
  apply Subtype.ext
  rfl

@[reassoc]
theorem extension_inclusion (C D : S.Subcomplex) (h : C ≤ D) :
    extension C D h ≫ RelativeCochains.inclusion C = RelativeCochains.inclusion D := by
  ext n φ
  rfl

@[reassoc]
theorem extension_forget (C D : S.Subcomplex) (h : C ≤ D) (n : ℕ) :
    homologyMap (extension C D h) n ≫ RelativeCochains.forget C n =
      RelativeCochains.forget D n := by
  change homologyMap (extension C D h) n ≫ homologyMap (RelativeCochains.inclusion C) n = _
  rw [← homologyMap_comp, extension_inclusion]
  rfl

end Simplicial

section Topological

variable (X : TopCat.{0}) (U V : Set X)

local notation "A" => subsetSingular X U
local notation "B" => subsetSingular X V
local notation "W" => subsetSingular X (U ∩ V)

/-- Original identity-pair transport across the proved equality of intersection boundaries. -/
def intersectionBoundaryIso : RelativeCochains.complex W ≅ RelativeCochains.complex (A ⊓ B) :=
  RelativeCochains.pullbackIso (Iso.refl (TopCat.toSSet.obj X)) (by
    change A ⊓ B = (subsetSingular X (U ∩ V)).preimage (𝟙 (TopCat.toSSet.obj X))
    rw [SSet.Subcomplex.preimage_id]
    exact (subsetSingular_inter X U V).symm)

def leftExtension : RelativeCochains.complex A ⟶ RelativeCochains.complex W :=
  extension W A (subsetSingular_mono X Set.inter_subset_left)

def rightExtension : RelativeCochains.complex B ⟶ RelativeCochains.complex W :=
  extension W B (subsetSingular_mono X Set.inter_subset_right)

/-- The complete original restriction from the full relative pair to the first local pair. -/
def localRestrictionLeft : RelativeCochains.complex W ⟶
    RelativeCochains.complex (RelativeUnionSplit.leftBoundary A B) :=
  (intersectionBoundaryIso X U V).hom ≫ RelativeUnionSplit.toUnion A B ≫
    RelativeUnionSplit.restrictionLeft A B

/-- The complete original restriction from the full relative pair to the second local pair. -/
def localRestrictionRight : RelativeCochains.complex W ⟶
    RelativeCochains.complex (RelativeUnionSplit.rightBoundary A B) :=
  (intersectionBoundaryIso X U V).hom ≫ RelativeUnionSplit.toUnion A B ≫
    RelativeUnionSplit.restrictionRight A B

theorem leftExtension_localLeft : leftExtension X U V ≫ localRestrictionLeft X U V = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val σ.val = 0
  exact RelativeCochains.cochain_vanish A n φ σ

theorem leftExtension_localRight : leftExtension X U V ≫ localRestrictionRight X U V =
    RelativeExcision.restriction B A := by
  ext n φ
  apply Subtype.ext
  rfl

theorem rightExtension_localLeft : rightExtension X U V ≫ localRestrictionLeft X U V =
    RelativeExcision.restriction A B := by
  ext n φ
  apply Subtype.ext
  rfl

theorem rightExtension_localRight : rightExtension X U V ≫ localRestrictionRight X U V = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val σ.val = 0
  exact RelativeCochains.cochain_vanish B n φ σ

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

theorem toUnion_quasiIso : QuasiIso (RelativeUnionSplit.toUnion A B) :=
  RelativeUnionSplit.toUnion_quasiIso A B
    (CochainDualComparison.smallRestriction_quasiIso X U V hU hV hcover)

/-- The forward map remains the original full-to-small relative restriction. -/
def smallCohomologyIso (n : ℕ) : RelativeCochains.Cohomology (A ⊓ B) n ≅
    RelativeCochains.Cohomology (RelativeUnionSplit.unionBoundary A B) n := by
  have := toUnion_quasiIso X U V hU hV hcover
  exact isoOfQuasiIsoAt (RelativeUnionSplit.toUnion A B) n

@[simp]
theorem smallCohomologyIso_hom (n : ℕ) :
    (smallCohomologyIso X U V hU hV hcover n).hom =
      homologyMap (RelativeUnionSplit.toUnion A B) n := rfl

def localSplitEquiv (n : ℕ) : RelativeCochains.Cohomology W n ≃ₗ[ℚ]
    (RelativeCochains.Cohomology (RelativeUnionSplit.leftBoundary A B) n ×
      RelativeCochains.Cohomology (RelativeUnionSplit.rightBoundary A B) n) :=
  ((homologyMapIso (intersectionBoundaryIso X U V) n).toLinearEquiv.trans
    (smallCohomologyIso X U V hU hV hcover n).toLinearEquiv).trans
      (RelativeUnionSplit.cohomologyEquiv A B n)

/-- The full/small splitting still has exactly the original local restrictions as coordinates. -/
theorem localSplitEquiv_apply (n : ℕ) (z : RelativeCochains.Cohomology W n) :
    localSplitEquiv X U V hU hV hcover n z =
      (homologyMap (localRestrictionLeft X U V) n z,
        homologyMap (localRestrictionRight X U V) n z) := by
  change (homologyMap (RelativeUnionSplit.restrictionLeft A B) n
      ((smallCohomologyIso X U V hU hV hcover n).hom
        ((homologyMapIso (intersectionBoundaryIso X U V) n).hom z)),
    homologyMap (RelativeUnionSplit.restrictionRight A B) n
      ((smallCohomologyIso X U V hU hV hcover n).hom
        ((homologyMapIso (intersectionBoundaryIso X U V) n).hom z))) = _
  simp only [smallCohomologyIso_hom, homologyMapIso_hom, localRestrictionLeft,
    localRestrictionRight, homologyMap_comp, ModuleCat.comp_apply]

theorem localSplitEquiv_leftExtension (n : ℕ) (z : RelativeCochains.Cohomology A n) :
    localSplitEquiv X U V hU hV hcover n (homologyMap (leftExtension X U V) n z) =
      (0, (RelativeExcision.excisionIso X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv z) := by
  rw [localSplitEquiv_apply]
  apply Prod.ext
  · change (homologyMap (leftExtension X U V) n ≫
      homologyMap (localRestrictionLeft X U V) n) z = 0
    simp only [← homologyMap_comp, leftExtension_localLeft, homologyMap_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply]
  · change (homologyMap (leftExtension X U V) n ≫
      homologyMap (localRestrictionRight X U V) n) z =
        (RelativeExcision.excisionIso X V U hV hU
          (by simpa only [Set.union_comm] using hcover) n).hom z
    rw [← homologyMap_comp, leftExtension_localRight, RelativeExcision.excisionIso_hom]

theorem localSplitEquiv_rightExtension (n : ℕ) (z : RelativeCochains.Cohomology B n) :
    localSplitEquiv X U V hU hV hcover n (homologyMap (rightExtension X U V) n z) =
      ((RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv z, 0) := by
  rw [localSplitEquiv_apply]
  apply Prod.ext
  · change (homologyMap (rightExtension X U V) n ≫
      homologyMap (localRestrictionLeft X U V) n) z =
        (RelativeExcision.excisionIso X U V hU hV hcover n).hom z
    rw [← homologyMap_comp, rightExtension_localLeft, RelativeExcision.excisionIso_hom]
  · change (homologyMap (rightExtension X U V) n ≫
      homologyMap (localRestrictionRight X U V) n) z = 0
    simp only [← homologyMap_comp, rightExtension_localRight, homologyMap_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply]

/-- Canonical splitting into the two original ambient relative groups. -/
def splitEquiv (n : ℕ) : RelativeCochains.Cohomology W n ≃ₗ[ℚ]
    (RelativeCochains.Cohomology A n × RelativeCochains.Cohomology B n) :=
  ((localSplitEquiv X U V hU hV hcover n).trans
    ((RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv.symm.prodCongr
      (RelativeExcision.excisionIso X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv.symm)).trans
      (LinearEquiv.prodComm ℚ _ _)

theorem splitEquiv_leftExtension (n : ℕ) (z : RelativeCochains.Cohomology A n) :
    splitEquiv X U V hU hV hcover n (homologyMap (leftExtension X U V) n z) = (z, 0) := by
  change (LinearEquiv.prodComm ℚ _ _)
    (((RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv.symm.prodCongr
      (RelativeExcision.excisionIso X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv.symm)
      (localSplitEquiv X U V hU hV hcover n (homologyMap (leftExtension X U V) n z))) = _
  rw [localSplitEquiv_leftExtension]
  change ((RelativeExcision.excisionIso X V U hV hU
      (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv.symm
        ((RelativeExcision.excisionIso X V U hV hU
          (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv z),
    (RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv.symm 0) = (z, 0)
  rw [LinearEquiv.symm_apply_apply, map_zero]

theorem splitEquiv_rightExtension (n : ℕ) (z : RelativeCochains.Cohomology B n) :
    splitEquiv X U V hU hV hcover n (homologyMap (rightExtension X U V) n z) = (0, z) := by
  change (LinearEquiv.prodComm ℚ _ _)
    (((RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv.symm.prodCongr
      (RelativeExcision.excisionIso X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv.symm)
      (localSplitEquiv X U V hU hV hcover n (homologyMap (rightExtension X U V) n z))) = _
  rw [localSplitEquiv_rightExtension]
  change ((RelativeExcision.excisionIso X V U hV hU
      (by simpa only [Set.union_comm] using hcover) n).toLinearEquiv.symm 0,
    (RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv.symm
      ((RelativeExcision.excisionIso X U V hU hV hcover n).toLinearEquiv z)) = (0, z)
  rw [map_zero, LinearEquiv.symm_apply_apply]

/-- The inverse splitting, with its actual original extension formula proved next. -/
def sumEquiv (n : ℕ) :
    (RelativeCochains.Cohomology A n × RelativeCochains.Cohomology B n) ≃ₗ[ℚ]
      RelativeCochains.Cohomology W n :=
  (splitEquiv X U V hU hV hcover n).symm

theorem sumEquiv_apply (n : ℕ)
    (z : RelativeCochains.Cohomology A n × RelativeCochains.Cohomology B n) :
    sumEquiv X U V hU hV hcover n z =
      homologyMap (leftExtension X U V) n z.1 + homologyMap (rightExtension X U V) n z.2 := by
  apply (splitEquiv X U V hU hV hcover n).injective
  change (splitEquiv X U V hU hV hcover n)
    ((splitEquiv X U V hU hV hcover n).symm z) = _
  rw [LinearEquiv.apply_symm_apply, map_add,
    splitEquiv_leftExtension X U V hU hV hcover,
    splitEquiv_rightExtension X U V hU hV hcover]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

omit hU hV hcover in
/-- Sum of the two ORIGINAL identity-pair extensions, independently of the equivalence. -/
def sumMap (n : ℕ) :
    (RelativeCochains.Cohomology A n × RelativeCochains.Cohomology B n) →ₗ[ℚ]
      RelativeCochains.Cohomology W n :=
  (homologyMap (leftExtension X U V) n).hom.comp (LinearMap.fst ℚ _ _) +
    (homologyMap (rightExtension X U V) n).hom.comp (LinearMap.snd ℚ _ _)

theorem sumEquiv_toLinearMap (n : ℕ) :
    (sumEquiv X U V hU hV hcover n).toLinearMap = sumMap X U V n := by
  apply LinearMap.ext
  intro z
  exact sumEquiv_apply X U V hU hV hcover n z

/-- Bijectivity of the actual original support-extension sum. -/
theorem sumMap_bijective (n : ℕ) : Function.Bijective (sumMap X U V n) := by
  rw [← sumEquiv_toLinearMap X U V hU hV hcover n]
  exact (sumEquiv X U V hU hV hcover n).bijective

end Topological

end HodgeConjecture.RelativeAdditivity

end
