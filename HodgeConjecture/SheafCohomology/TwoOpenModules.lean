module

public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.SheafCohomology.LinearRestriction
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Topology.Sheaves.MayerVietoris

@[expose] public section

/-!
# Linear Mayer–Vietoris from the actual sections of an injective resolution

For an exact coefficient functor to fixed-ring module sheaves, the two-open-cover
square of sections is a pullback in each degree. If injective coefficients
have surjective restrictions, its associated sequence of complexes is
short exact. The connecting morphism of this sequence is the actual
Mayer–Vietoris boundary in right-derived sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology.TwoOpenModules


attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

noncomputable section

universe u v w

variable (k : Type u) [CommRing k]
variable {X : Type u} [TopologicalSpace X]
  {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) [T.Additive]

/-- The actual presheaf of modules carried by a coefficient object. -/
abbrev linearPresheaf (A : 𝒜) : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} k := (T.obj A).obj

/-- Actual sections as modules over the fixed coefficient ring. -/
def secFunctor (U : Opens X) : 𝒜 ⥤ ModuleCat.{u} k :=
  T ⋙ sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k) ⋙
    (evaluation _ _).obj (op U)

instance (U : Opens X) : (secFunctor k T U).Additive where
  map_add := by intros; simp only [secFunctor, Functor.comp_map, Functor.map_add]

instance [PreservesFiniteLimits T] (U : Opens X) : PreservesFiniteLimits (secFunctor k T U) := by
  unfold secFunctor
  infer_instance

/-- Ordinary derived sections in the actual module coefficient category. -/
abbrev Hobj [EnoughInjectives 𝒜] (U : Opens X) (n : ℕ) (A : 𝒜) : ModuleCat.{u} k :=
  ((secFunctor k T U).rightDerived n).obj A

/-- The original complex read on sections of its underlying module sheaves. -/
abbrev sectionsComplex (K : CochainComplex 𝒜 ℕ) (U : Opens X) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  ((secFunctor k T U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Actual restriction of sections in each cochain degree. -/
def restriction (K : CochainComplex 𝒜 ℕ) {U V : Opens X} (h : U ≤ V) :
    sectionsComplex k T K V ⟶ sectionsComplex k T K U where
  f n := (linearPresheaf k T (K.X n)).map (homOfLE h).op
  comm' i j _ := by
    exact (T.map (K.d i j)).hom.naturality (homOfLE h).op

@[reassoc (attr := simp)]
theorem restriction_comp (K : CochainComplex 𝒜 ℕ) {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) :
    restriction k T K hVW ≫ restriction k T K hUV = restriction k T K (hUV.trans hVW) := by
  ext n x
  change (linearPresheaf k T (K.X n)).map (homOfLE hUV).op
    ((linearPresheaf k T (K.X n)).map (homOfLE hVW).op x) = _
  rw [← Functor.map_comp_apply]
  rfl

/-- The two-open-cover square of the original complexes of sections. -/
def coverSquare (K : CochainComplex 𝒜 ℕ) (U V : Opens X) :
    Square (CochainComplex (ModuleCat.{u} k) ℕ) where
  f₁₂ := restriction k T K (show U ≤ U ⊔ V from le_sup_left)
  f₁₃ := restriction k T K (show V ≤ U ⊔ V from le_sup_right)
  f₂₄ := restriction k T K (show U ⊓ V ≤ U from inf_le_left)
  f₃₄ := restriction k T K (show U ⊓ V ≤ V from inf_le_right)
  fac := by rw [restriction_comp, restriction_comp]

/-- The sheaf condition makes the square of section complexes a pullback. -/
theorem coverSquare_isPullback (K : CochainComplex 𝒜 ℕ) (U V : Opens X) :
    (coverSquare k T K U V).IsPullback := by
  apply Square.IsPullback.mk
  apply HomologicalComplex.isLimitOfEval
  intro n
  exact (PullbackCone.isLimitMapConeEquiv (coverSquare k T K U V).pullbackCone
    (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n)).symm
    ((Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf (T.obj (K.X n)) |>.isLimit)

/-- The unaugmented sequence Γ(U∪V) → Γ(U)⊕Γ(V) → Γ(U∩V). -/
def coverShortComplex (K : CochainComplex 𝒜 ℕ) (U V : Opens X) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  (coverSquare k T K U V).commSq.shortComplex'

/-- Sheaf gluing proves exactness at the pair of chart section complexes. -/
theorem coverShortComplex_exact (K : CochainComplex 𝒜 ℕ) (U V : Opens X) :
    (coverShortComplex k T K U V).Exact :=
  (coverSquare_isPullback k T K U V).exact_shortComplex'

/-- Sheaf separatedness proves injectivity of the cover restriction map. -/
instance coverShortComplex_mono (K : CochainComplex 𝒜 ℕ) (U V : Opens X) :
    Mono (coverShortComplex k T K U V).f :=
  (coverSquare_isPullback k T K U V).mono_shortComplex'_f


/-- The local extension property used for injective coefficients. -/
def InjectiveRestrictionsSurjective : Prop :=
  ∀ A : 𝒜, Injective A → ∀ (U V : Opens X) (h : U ≤ V),
    Function.Surjective ((linearPresheaf k T A).map (homOfLE h).op)

/-- Actual fixed-ring sheaves satisfy the extension property used by this sequence. -/
theorem injectiveRestrictions_identity :
    InjectiveRestrictionsSurjective k
      (𝟭 (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k))) := by
  intro I hI U V h
  let : Injective I := hI
  exact Cohomology.LinearRestriction.injective_linear_restriction_surjective
    (X := TopCat.of X) I h

/-- Sections of an injective resolution give the actual short exact
Mayer–Vietoris sequence of complexes. -/
theorem coverShortComplex_shortExact
    (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    (coverShortComplex k T I.cocomplex U V).ShortExact := by
  have hrestr : Epi (restriction k T I.cocomplex
      (show U ⊓ V ≤ U from inf_le_left)) := by
    apply HomologicalComplex.epi_of_epi_f
    intro n
    rw [ModuleCat.epi_iff_surjective]
    exact hres _ (by infer_instance) _ _ _
  have hcomp : Epi (biprod.inl ≫ (coverShortComplex k T I.cocomplex U V).g) := by
    change Epi (biprod.inl ≫ biprod.desc _ _)
    rw [biprod.inl_desc]
    exact hrestr
  exact
    { exact := coverShortComplex_exact k T I.cocomplex U V
      mono_f := inferInstance
      epi_g := epi_of_epi biprod.inl _ }


variable [PreservesFiniteLimits T]

/-- Actual sections are degree-zero cohomology of sections of any
injective resolution, with their original augmentation. -/
def sectionsZeroIso {A : 𝒜} (I : InjectiveResolution A) (U : Opens X) :
    (linearPresheaf k T A).obj (op U) ≅ (sectionsComplex k T I.cocomplex U).homology 0 :=
  asIso (I.toRightDerivedZero' (secFunctor k T U)) ≪≫
    asIso ((sectionsComplex k T I.cocomplex U).homologyπ 0)

/-- The degree-zero normalization respects the actual restriction map. -/
@[reassoc]
theorem sectionsZeroIso_restriction {A : 𝒜} (I : InjectiveResolution A)
    {U V : Opens X} (h : U ≤ V) :
    (linearPresheaf k T A).map (homOfLE h).op ≫ (sectionsZeroIso k T I U).hom =
      (sectionsZeroIso k T I V).hom ≫ HomologicalComplex.homologyMap
        (restriction k T I.cocomplex h) 0 := by
  change _ ≫ (I.toRightDerivedZero' (secFunctor k T U) ≫
      (sectionsComplex k T I.cocomplex U).homologyπ 0) =
    (I.toRightDerivedZero' (secFunctor k T V) ≫
      (sectionsComplex k T I.cocomplex V).homologyπ 0) ≫ _
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono ((sectionsComplex k T I.cocomplex U).iCycles 0)]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  exact (T.map (I.ι.f 0)).hom.naturality (homOfLE h).op

/-- The difference of the original restrictions to the overlap. -/
def sectionDifference (A : 𝒜) (U V : Opens X) :
    (linearPresheaf k T A).obj (op U) ⊞ (linearPresheaf k T A).obj (op V) ⟶
      (linearPresheaf k T A).obj (op (U ⊓ V)) :=
  biprod.desc ((linearPresheaf k T A).map (homOfLE inf_le_left).op)
    (-((linearPresheaf k T A).map (homOfLE inf_le_right).op))

/-- Degree-zero cohomology of the chart-pair complex, with actual sections. -/
def chartPairZeroIso {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    (linearPresheaf k T A).obj (op U) ⊞ (linearPresheaf k T A).obj (op V) ≅
      (coverShortComplex k T I.cocomplex U V).X₂.homology 0 :=
  biprod.mapIso (sectionsZeroIso k T I U) (sectionsZeroIso k T I V) ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) 0).mapBiprod
      (sectionsComplex k T I.cocomplex U) (sectionsComplex k T I.cocomplex V)).symm

/-- This normalization preserves the original overlap difference. -/
@[reassoc]
theorem chartPairZeroIso_difference {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    sectionDifference k T A U V ≫ (sectionsZeroIso k T I (U ⊓ V)).hom =
      (chartPairZeroIso k T I U V).hom ≫ HomologicalComplex.homologyMap
        (coverShortComplex k T I.cocomplex U V).g 0 := by
  change sectionDifference k T A U V ≫ (sectionsZeroIso k T I (U ⊓ V)).hom =
    (biprod.mapIso (sectionsZeroIso k T I U) (sectionsZeroIso k T I V)).hom ≫
      ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) 0).mapBiprod
        (sectionsComplex k T I.cocomplex U) (sectionsComplex k T I.cocomplex V)).inv ≫
      (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) 0).map
        (biprod.desc (restriction k T I.cocomplex (show U ⊓ V ≤ U from inf_le_left))
          (-restriction k T I.cocomplex (show U ⊓ V ≤ V from inf_le_right)))
  rw [biprod.mapBiprod_inv_map_desc]
  apply biprod.hom_ext'
  · simpa [sectionDifference] using sectionsZeroIso_restriction k T I
      (show U ⊓ V ≤ U from inf_le_left)
  · simpa [sectionDifference, Functor.map_neg] using congrArg Neg.neg
      (sectionsZeroIso_restriction k T I (show U ⊓ V ≤ V from inf_le_right))


variable [EnoughInjectives 𝒜]

/-- The actual resolution connecting morphism, normalized on ordinary sections. -/
def boundary (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    (linearPresheaf k T A).obj (op (U ⊓ V)) ⟶ Hobj k T (U ⊔ V) 1 A :=
  (sectionsZeroIso k T I (U ⊓ V)).hom ≫
    (coverShortComplex_shortExact k T hres I U V).δ 0 1 rfl ≫
    (I.isoRightDerivedObj (secFunctor k T (U ⊔ V)) 1).inv

/-- A difference of two chart restrictions has zero connecting class. -/
@[reassoc]
theorem sectionDifference_boundary (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    sectionDifference k T A U V ≫ boundary k T hres I U V = 0 := by
  dsimp [boundary]
  rw [← Category.assoc, chartPairZeroIso_difference]
  simp only [Category.assoc, ShortComplex.ShortExact.comp_δ_assoc, zero_comp, comp_zero]

/-- The initial Mayer–Vietoris sequence with the original chart sections
and the independently defined first right-derived sections object. -/
def initialShortComplex (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (sectionDifference k T A U V) (boundary k T hres I U V)
    (sectionDifference_boundary k T hres I U V)

/-- The initial sequence is the actual homology sequence of the resolution. -/
def initialShortComplexIso (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    initialShortComplex k T hres I U V ≅
      ShortComplex.mk _ _ ((coverShortComplex_shortExact k T hres I U V).comp_δ 0 1 rfl) :=
  ShortComplex.isoMk (chartPairZeroIso k T I U V) (sectionsZeroIso k T I (U ⊓ V))
    (I.isoRightDerivedObj (secFunctor k T (U ⊔ V)) 1)
    (chartPairZeroIso_difference k T I U V).symm
    (by
      change (sectionsZeroIso k T I (U ⊓ V)).hom ≫ _ =
        ((sectionsZeroIso k T I (U ⊓ V)).hom ≫
          (coverShortComplex_shortExact k T hres I U V).δ 0 1 rfl ≫
          (I.isoRightDerivedObj (secFunctor k T (U ⊔ V)) 1).inv) ≫
          (I.isoRightDerivedObj (secFunctor k T (U ⊔ V)) 1).hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Exactness of the actual overlap-section-to-first-cohomology sequence. -/
theorem initialShortComplex_exact (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) :
    (initialShortComplex k T hres I U V).Exact :=
  ShortComplex.exact_of_iso (initialShortComplexIso k T hres I U V).symm
    ((coverShortComplex_shortExact k T hres I U V).homology_exact₃ 0 1 rfl)

/-- If first cohomology vanishes on the charts, every global first class
comes from an actual section on their overlap. -/
theorem boundary_epi (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X)
    (hU : IsZero (Hobj k T U 1 A)) (hV : IsZero (Hobj k T V 1 A)) :
    Epi (boundary k T hres I U V) := by
  let S := coverShortComplex k T I.cocomplex U V
  let hS := coverShortComplex_shortExact k T hres I U V
  have hzU : IsZero ((sectionsComplex k T I.cocomplex U).homology 1) :=
    hU.of_iso (I.isoRightDerivedObj (secFunctor k T U) 1).symm
  have hzV : IsZero ((sectionsComplex k T I.cocomplex V).homology 1) :=
    hV.of_iso (I.isoRightDerivedObj (secFunctor k T V) 1).symm
  have hz : IsZero (S.X₂.homology 1) :=
    ((biprod_isZero_iff _ _).2 ⟨hzU, hzV⟩).of_iso
      ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) 1).mapBiprod
        (sectionsComplex k T I.cocomplex U) (sectionsComplex k T I.cocomplex V))
  have hδ : Epi (hS.δ 0 1 rfl) :=
    (ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)).1 (hS.homology_exact₁ 0 1 rfl)
  dsimp [boundary]
  infer_instance

/-- First cohomology is the cokernel of the original overlap restrictions
when the two chart first-cohomology groups vanish. -/
def cokernelIsoFirstCohomology (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X)
    (hU : IsZero (Hobj k T U 1 A)) (hV : IsZero (Hobj k T V 1 A)) :
    cokernel (sectionDifference k T A U V) ≅ Hobj k T (U ⊔ V) 1 A := by
  have : Epi (initialShortComplex k T hres I U V).g :=
    boundary_epi k T hres I U V hU hV
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (sectionDifference k T A U V))
    (initialShortComplex_exact k T hres I U V).gIsCokernel


/-- The cokernel comparison is pinned by the actual connecting morphism. -/
@[reassoc]
theorem cokernelIsoFirstCohomology_π_hom (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X)
    (hU : IsZero (Hobj k T U 1 A)) (hV : IsZero (Hobj k T V 1 A)) :
    cokernel.π (sectionDifference k T A U V) ≫
      (cokernelIsoFirstCohomology k T hres I U V hU hV).hom = boundary k T hres I U V := by
  have : Epi (initialShortComplex k T hres I U V).g := boundary_epi k T hres I U V hU hV
  exact (cokernelIsCokernel (sectionDifference k T A U V)).comp_coconePointUniqueUpToIso_hom
    (initialShortComplex_exact k T hres I U V).gIsCokernel WalkingParallelPair.one

/-- Surjectivity of the actual chart difference proves global first-cohomology vanishing. -/
theorem isZero_firstCohomology_of_epi_difference
    (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X)
    (hU : IsZero (Hobj k T U 1 A)) (hV : IsZero (Hobj k T V 1 A))
    (hdiff : Epi (sectionDifference k T A U V)) : IsZero (Hobj k T (U ⊔ V) 1 A) := by
  have := hdiff
  exact (isZero_cokernel_of_epi (sectionDifference k T A U V)).of_iso
    (cokernelIsoFirstCohomology k T hres I U V hU hV).symm

omit [PreservesFiniteLimits T] in
/-- The same genuine homology sequence proves higher vanishing from the
chart and overlap cohomology groups; in particular it applies in degree two. -/
theorem isZero_successor_of_chartCohomology
    (hres : InjectiveRestrictionsSurjective k T)
    {A : 𝒜} (I : InjectiveResolution A) (U V : Opens X) (n : ℕ)
    (hW : IsZero (Hobj k T (U ⊓ V) n A))
    (hU : IsZero (Hobj k T U (n + 1) A)) (hV : IsZero (Hobj k T V (n + 1) A)) :
    IsZero (Hobj k T (U ⊔ V) (n + 1) A) := by
  let S := coverShortComplex k T I.cocomplex U V
  let hS := coverShortComplex_shortExact k T hres I U V
  have hzW : IsZero (S.X₃.homology n) :=
    hW.of_iso (I.isoRightDerivedObj (secFunctor k T (U ⊓ V)) n).symm
  have hzU : IsZero ((sectionsComplex k T I.cocomplex U).homology (n + 1)) :=
    hU.of_iso (I.isoRightDerivedObj (secFunctor k T U) (n + 1)).symm
  have hzV : IsZero ((sectionsComplex k T I.cocomplex V).homology (n + 1)) :=
    hV.of_iso (I.isoRightDerivedObj (secFunctor k T V) (n + 1)).symm
  have hz : IsZero (S.X₂.homology (n + 1)) :=
    ((biprod_isZero_iff _ _).2 ⟨hzU, hzV⟩).of_iso
      ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) (n + 1)).mapBiprod
        (sectionsComplex k T I.cocomplex U) (sectionsComplex k T I.cocomplex V))
  exact ((hS.homology_exact₁ n (n + 1) rfl).isZero_X₂ (hzW.eq_of_src _ _) (hz.eq_of_tgt _ _)).of_iso
    (I.isoRightDerivedObj (secFunctor k T (U ⊔ V)) (n + 1))

end

end HodgeConjecture.SheafCohomology.TwoOpenModules
