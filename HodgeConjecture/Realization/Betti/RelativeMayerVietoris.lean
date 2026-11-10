module

public import HodgeConjecture.Realization.Betti.RelativeExcision

@[expose] public section

/-!
# The positive relative-boundary description of original Mayer–Vietoris

The local relative boundary, inverse actual excision and forgetting support
give the original full singular Mayer–Vietoris connecting map. Naturality
of the original short exact sequences fixes the positive sign.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeMayerVietoris

open CategoryTheory HomologicalComplex

variable {S : SSet.{0}} (A B : S.Subcomplex)

/-- The original nested intersection comparison on cohomology. -/
def intersectionCohomologyIso (n : ℕ) :
    (SubcomplexCochains.complex (A ⊓ B).toSSet).homology n ≅
      (SubcomplexCochains.complex (RelativeUnion.localBoundary A B).toSSet).homology n :=
  homologyMapIso (SingularMayerVietoris.pullbackIso (RelativeUnion.intersectionIso A B)) n

/-- The actual local relative connecting map, with the original intersection as source. -/
def localConnecting (n : ℕ) :
    (SubcomplexCochains.complex (A ⊓ B).toSSet).homology n ⟶
      RelativeCochains.Cohomology (RelativeUnion.localBoundary A B) (n + 1) :=
  (intersectionCohomologyIso A B n).hom ≫
    RelativeCochains.connecting (RelativeUnion.localBoundary A B) n

/-- Forgetting the local support after strict union excision uses actual compatible-function gluing. -/
def localToAbsolute : RelativeCochains.complex (RelativeUnion.localBoundary A B) ⟶
    SubcomplexCochains.complex (A ⊔ B).toSSet :=
  (RelativeUnion.excisionIso A B).inv ≫
    RelativeCochains.inclusion (RelativeUnion.unionBoundary A B)

theorem localToAbsolute_restrictions :
    localToAbsolute A B ≫ SubcomplexCochains.coverRestriction A B =
      RelativeCochains.inclusion (RelativeUnion.localBoundary A B) ≫ CochainPair.inl A B := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change SubcomplexCochains.coverRestrictionLinear A B n
    (RelativeUnion.extensionFunction A B n φ) = (φ.val, 0)
  exact RelativeUnion.extensionFunction_restrictions A B n φ

/-- Actual local restriction and the original first-minus-second map agree with zero on B. -/
theorem inl_difference :
    CochainPair.inl A B ≫ SubcomplexCochains.coverDifference A B =
      RelativeCochains.restriction (RelativeUnion.localBoundary A B) ≫
        SubcomplexCochains.pullback (RelativeUnion.intersectionIso A B).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change φ ⟨σ.val, σ.property.1⟩ - 0 = φ ⟨σ.val, σ.property.1⟩
  exact sub_zero _

/-- The original local relative sequence maps to the original union sequence. -/
def shortComplexMap :
    RelativeCochains.shortComplex (RelativeUnion.localBoundary A B) ⟶
      SubcomplexCochains.coverShortComplex A B where
  τ₁ := localToAbsolute A B
  τ₂ := CochainPair.inl A B
  τ₃ := SubcomplexCochains.pullback (RelativeUnion.intersectionIso A B).inv
  comm₁₂ := localToAbsolute_restrictions A B
  comm₂₃ := inl_difference A B

/-- Native connecting naturality gives the actual positive sign. -/
theorem connecting_naturality (n : ℕ) :
    RelativeCochains.connecting (RelativeUnion.localBoundary A B) n ≫
        homologyMap (localToAbsolute A B) (n + 1) =
      (intersectionCohomologyIso A B n).inv ≫ SubcomplexCochains.connecting A B n :=
  HomologySequence.δ_naturality (shortComplexMap A B)
    (RelativeCochains.shortComplex_shortExact (RelativeUnion.localBoundary A B))
    (SubcomplexCochains.coverShortComplex_shortExact A B) n (n + 1) (by simp)

/-- The original local boundary, inverse strict excision and forgetting support
are exactly the original union Mayer–Vietoris boundary. -/
@[reassoc]
theorem localConnecting_forget (n : ℕ) :
    localConnecting A B n ≫ (homologyMapIso (RelativeUnion.excisionIso A B) (n + 1)).inv ≫
        RelativeCochains.forget (RelativeUnion.unionBoundary A B) (n + 1) =
      SubcomplexCochains.connecting A B n := by
  change (intersectionCohomologyIso A B n).hom ≫
    (RelativeCochains.connecting (RelativeUnion.localBoundary A B) n ≫
      (homologyMap (RelativeUnion.excisionIso A B).inv (n + 1) ≫
        homologyMap (RelativeCochains.inclusion (RelativeUnion.unionBoundary A B)) (n + 1))) = _
  rw [← homologyMap_comp]
  change (intersectionCohomologyIso A B n).hom ≫
    (RelativeCochains.connecting (RelativeUnion.localBoundary A B) n ≫
      homologyMap (localToAbsolute A B) (n + 1)) = _
  rw [connecting_naturality, Iso.hom_inv_id_assoc]

section Topological

variable (X : TopCat.{0}) (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

local notation "A" => SingularSubcomplexes.subsetSingular X U
local notation "B" => SingularSubcomplexes.subsetSingular X V

/-- The actual local relative connecting map, with the original topological overlap source. -/
def localConnectingActual (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) n ⟶
      RelativeCochains.Cohomology (RelativeUnion.localBoundary A B) (n + 1) :=
  (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv ≫ localConnecting A B n

/-- Inverse actual relative excision and original forgetting retain absolute small restriction. -/
@[reassoc]
theorem excisionIso_inv_forget_small (n : ℕ) :
    (RelativeExcision.excisionIso X U V hU hV hcover n).inv ≫
        RelativeCochains.forget B n ≫
        (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).hom =
      (homologyMapIso (RelativeUnion.excisionIso A B) n).inv ≫
        RelativeCochains.forget (RelativeUnion.unionBoundary A B) n := by
  simp only [RelativeExcision.excisionIso, Iso.trans_inv, Category.assoc]
  rw [← RelativeExcision.smallCohomologyIso_forget]
  rw [Iso.inv_hom_id_assoc]

/-- The geometric local relative boundary maps to the original full singular cover boundary.
The equality includes the actual restriction-based excision and its positive sign. -/
@[reassoc]
theorem connecting_excision_forget (n : ℕ) :
    localConnectingActual X U V n ≫
        (RelativeExcision.excisionIso X U V hU hV hcover (n + 1)).inv ≫
        RelativeCochains.forget B (n + 1) =
      SingularMayerVietoris.connecting X U V hU hV hcover n := by
  apply (cancel_mono
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcover (n + 1)).hom).mp
  simp only [Category.assoc, excisionIso_inv_forget_small,
    localConnectingActual, localConnecting_forget, SingularMayerVietoris.connecting,
    Iso.inv_hom_id, Category.comp_id]

/-- The same positive comparison retains the actual native intersection as source. -/
@[reassoc]
theorem localConnecting_excision_forget (n : ℕ) :
    localConnecting A B n ≫
        (RelativeExcision.excisionIso X U V hU hV hcover (n + 1)).inv ≫
        RelativeCochains.forget B (n + 1) =
      (SingularMayerVietoris.intersectionCohomologyIso X U V n).hom ≫
        SingularMayerVietoris.connecting X U V hU hV hcover n := by
  apply (cancel_epi (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv).mp
  simpa only [localConnectingActual, Category.assoc, Iso.inv_hom_id_assoc] using
    connecting_excision_forget X U V hU hV hcover n

end Topological

end HodgeConjecture.RelativeMayerVietoris
