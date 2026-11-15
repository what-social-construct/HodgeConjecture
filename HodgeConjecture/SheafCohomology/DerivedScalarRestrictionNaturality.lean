module

public import HodgeConjecture.SheafCohomology.DerivedScalarRestriction

@[expose] public noncomputable section

/-!
# Naturality of derived scalar restriction

The first comparison square uses the same actual injective resolution to
compute the two right-derived functors. This file records its naturality in a
morphism of the original sheaves.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

namespace HodgeConjecture.BoundedBelowDerived

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
@[reassoc]
theorem mapExtendXIso_hom_naturality {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : Option ι) :
    F.map (HomologicalComplex.extend.mapX φ i) ≫
        (mapExtendXIso F L i).hom =
      (mapExtendXIso F K i).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) i := by
  cases i with
  | none => simp [mapExtendXIso, HomologicalComplex.extend.mapX]
  | some j => simp [mapExtendXIso, HomologicalComplex.extend.mapX]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
@[reassoc]
theorem mapExtendIso_hom_naturality {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i
  change F.map (HomologicalComplex.extend.mapX φ (e.r i)) ≫
      (mapExtendXIso F L (e.r i)).hom =
    (mapExtendXIso F K (e.r i)).hom ≫
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) (e.r i)
  exact mapExtendXIso_hom_naturality F φ (e.r i)

omit [HasDerivedCategory C] [HasDerivedCategory D] in
@[reassoc]
theorem mapExtendIso_inv_naturality {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c') :
    HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e ≫
        (mapExtendIso F L e).inv =
      (mapExtendIso F K e).inv ≫
        (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) := by
  let aK := mapExtendIso F K e
  let aL := mapExtendIso F L e
  have h := mapExtendIso_hom_naturality F φ e
  apply (cancel_epi aK.hom).mp
  change aK.hom ≫
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e ≫ aL.inv) =
    aK.hom ≫ (aK.inv ≫
      (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e))
  calc
    _ = ((F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
      aL.hom) ≫ aL.inv := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ aL.inv) h.symm
    _ = (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) := by simp
    _ = _ := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end HodgeConjecture.BoundedBelowDerived

namespace HodgeConjecture.BoundedBelowDerived

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]

/-- The explicit postcomposition comparison respects the actual derived map
of a morphism in the source abelian category. -/
@[reassoc]
theorem rightDerivedPostcomposeIso_hom_naturality {M N : C} (g : M ⟶ N) (n : ℕ) :
    T.map ((F.rightDerived n).map g) ≫
        (rightDerivedPostcomposeIso F T N n).hom =
      (rightDerivedPostcomposeIso F T M n).hom ≫
        ((F ⋙ T).rightDerived n).map g := by
  let I := injectiveResolution M
  let J := injectiveResolution N
  let φ : I.cocomplex ⟶ J.cocomplex := InjectiveResolution.desc g J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero g J I
  have hF := I.isoRightDerivedObj_hom_naturality g J φ hφ F n
  have hFT := I.isoRightDerivedObj_inv_naturality g J φ hφ (F ⋙ T) n
  let uF := (F.mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex.homologyFunctor D (.up ℕ) n).map φ
  let uFT := ((F ⋙ T).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex.homologyFunctor E (.up ℕ) n).map φ
  let qI := (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso T
  let qJ := (((F.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc n).mapHomologyIso T
  have hSC : T.map uF ≫ qJ.inv = qI.inv ≫ uFT := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor D (.up ℕ) n).map
        ((F.mapHomologicalComplex (.up ℕ)).map φ)) T
  simp only [rightDerivedPostcomposeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  change T.map ((F.rightDerived n).map g) ≫
      T.map (J.isoRightDerivedObj F n).hom ≫ qJ.inv ≫
      (J.isoRightDerivedObj (F ⋙ T) n).inv =
    T.map (I.isoRightDerivedObj F n).hom ≫ qI.inv ≫
      (I.isoRightDerivedObj (F ⋙ T) n).inv ≫
      ((F ⋙ T).rightDerived n).map g
  calc
    _ = T.map (I.isoRightDerivedObj F n).hom ≫ T.map uF ≫ qJ.inv ≫
          (J.isoRightDerivedObj (F ⋙ T) n).inv := by
            simpa only [Functor.map_comp, Category.assoc] using
              congrArg (fun h => T.map h ≫ qJ.inv ≫
                (J.isoRightDerivedObj (F ⋙ T) n).inv) hF
    _ = T.map (I.isoRightDerivedObj F n).hom ≫ qI.inv ≫ uFT ≫
          (J.isoRightDerivedObj (F ⋙ T) n).inv := by
            simpa only [Category.assoc] using
              congrArg (fun h => T.map (I.isoRightDerivedObj F n).hom ≫ h ≫
                (J.isoRightDerivedObj (F ⋙ T) n).inv) hSC
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun h => T.map (I.isoRightDerivedObj F n).hom ≫ qI.inv ≫ h) hFT.symm

end HodgeConjecture.BoundedBelowDerived

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- Naturality in the original sheaf morphism of the scalar-restriction
postcomposition comparison used by `cohomologyIso`. -/
@[reassoc]
theorem globalSections_rightDerivedPostcomposeIso_hom_naturality
    {F G : TopCat.Sheaf (ModuleCat.{u} S) X} (g : F ⟶ G) (n : ℕ) :
    (ModuleCat.restrictScalars f).map
        (((SheafHypercohomology.globalSections S X).rightDerived n).map g) ≫
      (BoundedBelowDerived.rightDerivedPostcomposeIso
        (SheafHypercohomology.globalSections S X)
        (ModuleCat.restrictScalars f) G n).hom =
    (BoundedBelowDerived.rightDerivedPostcomposeIso
        (SheafHypercohomology.globalSections S X)
        (ModuleCat.restrictScalars f) F n).hom ≫
      (((SheafHypercohomology.globalSections S X ⋙
        ModuleCat.restrictScalars f).rightDerived n).map g) := by
  exact BoundedBelowDerived.rightDerivedPostcomposeIso_hom_naturality
    (SheafHypercohomology.globalSections S X) (ModuleCat.restrictScalars f) g n

end HodgeConjecture.SheafCohomology.ScalarRestriction

namespace HodgeConjecture.SheafHypercohomology

universe u

variable (k : Type u) [CommRing k] (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

@[reassoc]
theorem nonnegativeMap_comp
    {K L M : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    nonnegativeMap k X (φ ≫ ψ) =
      nonnegativeMap k X φ ≫ nonnegativeMap k X ψ := by
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.extendMap_comp φ ψ _

@[reassoc]
theorem hypercohomologyMap_comp
    {K L M : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) :
    hypercohomologyMap k X (φ ≫ ψ) n =
      hypercohomologyMap k X φ n ≫ hypercohomologyMap k X ψ n := by
  unfold hypercohomologyMap derivedGlobalSectionsMap
  rw [nonnegativeMap_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]

/-- The chosen descent of a sheaf morphism commutes with its original
injective-resolution augmentations after extension by zero. -/
@[reassoc]
theorem injectiveResolution_nonnegativeMap_naturality
    {M N : TopCat.Sheaf (ModuleCat.{u} k) X} (g : M ⟶ N) :
    nonnegativeMap k X ((CochainComplex.single₀ _).map g) ≫
        nonnegativeMap k X (injectiveResolution N).ι =
      nonnegativeMap k X (injectiveResolution M).ι ≫
        nonnegativeMap k X
          (InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M)) := by
  rw [← nonnegativeMap_comp, ← nonnegativeMap_comp,
    InjectiveResolution.desc_commutes]

/-- The derived-category identification through the chosen injective
resolution is natural in the original sheaf morphism. -/
@[reassoc]
theorem injectiveResolutionDerivedIso_hom_naturality
    {M N : TopCat.Sheaf (ModuleCat.{u} k) X} (g : M ⟶ N) :
    (globalSections k X).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          (nonnegativeMap k X ((CochainComplex.single₀ _).map g))) ≫
      (BoundedBelowDerived.injectiveResolutionDerivedIso
        (globalSections k X) N (injectiveResolution N)).hom =
    (BoundedBelowDerived.injectiveResolutionDerivedIso
        (globalSections k X) M (injectiveResolution M)).hom ≫
      DerivedCategory.Plus.Q.map
        ((globalSections k X).mapCochainComplexPlus.map
          (nonnegativeMap k X
            (InjectiveResolution.desc g (injectiveResolution N) (injectiveResolution M)))) := by
  let Γ := globalSections k X
  let RF := Γ.rightDerivedFunctorPlus
  let P := Γ.mapCochainComplexPlus
  let Q := DerivedCategory.Plus.Q (C := ModuleCat.{u} k)
  let Qs := DerivedCategory.Plus.Q (C := TopCat.Sheaf (ModuleCat.{u} k) X)
  let I := injectiveResolution M
  let J := injectiveResolution N
  let s := nonnegativeMap k X ((CochainComplex.single₀ _).map g)
  let a := nonnegativeMap k X I.ι
  let b := nonnegativeMap k X J.ι
  let p := nonnegativeMap k X (InjectiveResolution.desc g J I)
  have hSquare : s ≫ b = a ≫ p :=
    injectiveResolution_nonnegativeMap_naturality k X g
  have (q : ℤ) : Injective ((BoundedBelowDerived.nonnegativePlus I.cocomplex).obj.X q) := by
    change Injective ((I.cocomplex.extend (ComplexShape.embeddingUpIntGE 0)).X q)
    infer_instance
  have (q : ℤ) : Injective ((BoundedBelowDerived.nonnegativePlus J.cocomplex).obj.X q) := by
    change Injective ((J.cocomplex.extend (ComplexShape.embeddingUpIntGE 0)).X q)
    infer_instance
  let ηI := Γ.rightDerivedFunctorPlusUnit.app
    (BoundedBelowDerived.nonnegativePlus I.cocomplex)
  let ηJ := Γ.rightDerivedFunctorPlusUnit.app
    (BoundedBelowDerived.nonnegativePlus J.cocomplex)
  have : IsIso ηI := BoundedBelowDerived.isIso_unit_of_injectiveTerms Γ _
  have : IsIso ηJ := BoundedBelowDerived.isIso_unit_of_injectiveTerms Γ _
  have hUnit := Γ.rightDerivedFunctorPlusUnit.naturality p
  change Q.map (P.map p) ≫ ηJ = ηI ≫ RF.map (Qs.map p) at hUnit
  have hUnitInv : RF.map (Qs.map p) ≫ inv ηJ =
      inv ηI ≫ Q.map (P.map p) := by
    apply (cancel_epi ηI).mp
    calc
      _ = (Q.map (P.map p) ≫ ηJ) ≫ inv ηJ := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ inv ηJ) hUnit.symm
      _ = Q.map (P.map p) := by simp
      _ = _ := by simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  simp only [BoundedBelowDerived.injectiveResolutionDerivedIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  change RF.map (Qs.map s) ≫ RF.map (Qs.map b) ≫ inv ηJ =
    RF.map (Qs.map a) ≫ inv ηI ≫ Q.map (P.map p)
  calc
    _ = RF.map (Qs.map a) ≫ RF.map (Qs.map p) ≫ inv ηJ := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun t => RF.map (Qs.map t) ≫ inv ηJ) hSquare
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun t => RF.map (Qs.map a) ≫ t) hUnitInv

/-- Naturality of the original nonnegative-sections homology identification. -/
@[reassoc]
theorem nonnegativeSectionsHomologyIso_hom_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((globalSections k X).mapHomologicalComplex (.up ℕ)).map φ) n ≫
      (nonnegativeSectionsHomologyIso k X L n).hom =
    (nonnegativeSectionsHomologyIso k X K n).hom ≫
      HomologicalComplex.homologyMap
        (((globalSections k X).mapCochainComplexPlus.map
          (nonnegativeMap k X φ)).hom) (n : ℤ) := by
  let Γ := globalSections k X
  let e := ComplexShape.embeddingUpIntGE 0
  let A := (Γ.mapHomologicalComplex (.up ℕ)).obj K
  let B := (Γ.mapHomologicalComplex (.up ℕ)).obj L
  let u := (Γ.mapHomologicalComplex (.up ℕ)).map φ
  let v := (Γ.mapCochainComplexPlus.map (nonnegativeMap k X φ)).hom
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) (n : ℤ)
  let aK := A.extendHomologyIso e (by simp [e] : e.f n = (n : ℤ))
  let aL := B.extendHomologyIso e (by simp [e] : e.f n = (n : ℤ))
  let bK := BoundedBelowDerived.mapExtendIso Γ K e
  let bL := BoundedBelowDerived.mapExtendIso Γ L e
  have hAhom := HomologicalComplex.extendHomologyIso_hom_naturality u e
    (show e.f n = (n : ℤ) by simp [e])
  have hA : HomologicalComplex.homologyMap u n ≫ aL.inv =
      aK.inv ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap u e) (n : ℤ) := by
    apply (cancel_epi aK.hom).mp
    calc
      _ = (HomologicalComplex.homologyMap (HomologicalComplex.extendMap u e)
          (n : ℤ) ≫ aL.hom) ≫ aL.inv := by
            simpa only [Category.assoc] using
              congrArg (fun t => t ≫ aL.inv) hAhom.symm
      _ = HomologicalComplex.homologyMap (HomologicalComplex.extendMap u e)
          (n : ℤ) := by simp
      _ = _ := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hBcomplex := BoundedBelowDerived.mapExtendIso_inv_naturality Γ φ e
  change HomologicalComplex.extendMap u e ≫ bL.inv = bK.inv ≫ v at hBcomplex
  have hB : HomologicalComplex.homologyMap (HomologicalComplex.extendMap u e)
        (n : ℤ) ≫ H.map bL.inv =
      H.map bK.inv ≫ HomologicalComplex.homologyMap v (n : ℤ) := by
    change H.map (HomologicalComplex.extendMap u e) ≫ H.map bL.inv =
      H.map bK.inv ≫ H.map v
    simpa only [Functor.map_comp] using
      congrArg (fun t => H.map t) hBcomplex
  simp only [nonnegativeSectionsHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  change HomologicalComplex.homologyMap u n ≫ aL.inv ≫ H.map bL.inv =
    aK.inv ≫ H.map bK.inv ≫ HomologicalComplex.homologyMap v (n : ℤ)
  calc
    _ = aK.inv ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap u e) (n : ℤ) ≫ H.map bL.inv := by
          simpa only [Category.assoc] using
            congrArg (fun t => t ≫ H.map bL.inv) hA
    _ = aK.inv ≫ H.map bK.inv ≫ HomologicalComplex.homologyMap v (n : ℤ) := by
      simpa only [Category.assoc] using congrArg (fun t => aK.inv ≫ t) hB

/-- The original termwise-sections-to-hypercohomology comparison is natural
in the actual map of nonnegative sheaf complexes. -/
@[reassoc]
theorem comparisonFromComplexHomology_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap
        (((globalSections k X).mapCochainComplexPlus.map
          (nonnegativeMap k X φ)).hom) n ≫
      comparisonFromComplexHomology k X L n =
    comparisonFromComplexHomology k X K n ≫
      hypercohomologyMap k X φ n := by
  let ψ := ((globalSections k X).mapCochainComplexPlus.map
    (nonnegativeMap k X φ)).hom
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n
  have hFac :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.naturality ψ
  have hUnit := congrArg (fun h => H.map h) (comparison_naturality k X φ)
  dsimp only [Functor.comp_map] at hFac
  simp only [Functor.map_comp] at hUnit
  change HomologicalComplex.homologyMap ψ n ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
        (underivedGlobalSections k X L).obj =
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
        (underivedGlobalSections k X K).obj ≫
      H.map (DerivedCategory.Plus.Q.map
        ((globalSections k X).mapCochainComplexPlus.map (nonnegativeMap k X φ))) at hFac
  dsimp only [comparisonFromComplexHomology, comparisonOnHomology, hypercohomologyMap]
  change (HomologicalComplex.homologyMap ψ n ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
        (underivedGlobalSections k X L).obj) ≫ H.map (comparison k X L) =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
      (underivedGlobalSections k X K).obj ≫ H.map (comparison k X K)) ≫
      H.map (derivedGlobalSectionsMap k X φ)
  calc
    _ = ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
        (underivedGlobalSections k X K).obj ≫
      H.map (DerivedCategory.Plus.Q.map
        ((globalSections k X).mapCochainComplexPlus.map (nonnegativeMap k X φ)))) ≫
      H.map (comparison k X L) := congrArg (fun h => h ≫ H.map (comparison k X L)) hFac
    _ = _ := by rw [Category.assoc, hUnit, ← Category.assoc]

/-- The flasque-complex isomorphism is natural in a map of original complexes;
the flasque hypotheses only guarantee invertibility. -/
@[reassoc]
theorem complexHomologyIsoHypercohomology_hom_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (hK : ∀ q, (K.X q).IsFlasque)
    (hL : ∀ q, (L.X q).IsFlasque) (n : ℤ) :
    HomologicalComplex.homologyMap
        (((globalSections k X).mapCochainComplexPlus.map
          (nonnegativeMap k X φ)).hom) n ≫
      (complexHomologyIsoHypercohomology k X L hL n).hom =
    (complexHomologyIsoHypercohomology k X K hK n).hom ≫
      hypercohomologyMap k X φ n := by
  simpa only [complexHomologyIsoHypercohomology_hom] using
    comparisonFromComplexHomology_naturality k X φ n

@[reassoc]
theorem complexHomologyIsoHypercohomology_inv_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (φ : K ⟶ L) (hK : ∀ q, (K.X q).IsFlasque)
    (hL : ∀ q, (L.X q).IsFlasque) (n : ℤ) :
    hypercohomologyMap k X φ n ≫
      (complexHomologyIsoHypercohomology k X L hL n).inv =
    (complexHomologyIsoHypercohomology k X K hK n).inv ≫
      HomologicalComplex.homologyMap
        (((globalSections k X).mapCochainComplexPlus.map
          (nonnegativeMap k X φ)).hom) n := by
  let aK := complexHomologyIsoHypercohomology k X K hK n
  let aL := complexHomologyIsoHypercohomology k X L hL n
  let ψ := ((globalSections k X).mapCochainComplexPlus.map (nonnegativeMap k X φ)).hom
  have h := complexHomologyIsoHypercohomology_hom_naturality k X φ hK hL n
  apply (cancel_epi aK.hom).mp
  change aK.hom ≫ (hypercohomologyMap k X φ n ≫ aL.inv) =
    aK.hom ≫ (aK.inv ≫ HomologicalComplex.homologyMap ψ n)
  calc
    _ = (HomologicalComplex.homologyMap ψ n ≫ aL.hom) ≫ aL.inv := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ aL.inv) h.symm
    _ = HomologicalComplex.homologyMap ψ n := by simp
    _ = _ := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end HodgeConjecture.SheafHypercohomology

namespace HodgeConjecture.SheafCohomology.ScalarRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (X : TopCat.{u})

/-- The actual restricted injective resolution map used inside `cohomologyIso`. -/
def restrictedResolutionMap (F : TopCat.Sheaf (ModuleCat.{u} S) X) :
    (CochainComplex.single₀ _).obj ((sheaves f X).obj F) ⟶
      ((sheaves f X).mapHomologicalComplex (.up ℕ)).obj
        (injectiveResolution F).cocomplex :=
  (singleMapHomologicalComplex (sheaves f X) (.up ℕ) 0).inv.app F ≫
    ((sheaves f X).mapHomologicalComplex (.up ℕ)).map (injectiveResolution F).ι

/-- The original resolution comparison commutes with the chosen descent of
a morphism of complex-coefficient sheaves. -/
@[reassoc]
theorem restrictedResolutionMap_naturality
    {F G : TopCat.Sheaf (ModuleCat.{u} S) X} (g : F ⟶ G) :
    (CochainComplex.single₀ _).map ((sheaves f X).map g) ≫
      restrictedResolutionMap f X G =
    restrictedResolutionMap f X F ≫
      ((sheaves f X).mapHomologicalComplex (.up ℕ)).map
        (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)) := by
  let T := sheaves f X
  let U := T.mapHomologicalComplex (.up ℕ)
  let E := singleMapHomologicalComplex T (.up ℕ) 0
  let I := injectiveResolution F
  let J := injectiveResolution G
  have hE := E.inv.naturality g
  change (CochainComplex.single₀ _).map (T.map g) ≫ E.inv.app G =
    E.inv.app F ≫ U.map ((CochainComplex.single₀ _).map g) at hE
  have hI := InjectiveResolution.desc_commutes g J I
  simp only [restrictedResolutionMap, Category.assoc]
  change (CochainComplex.single₀ _).map (T.map g) ≫
      E.inv.app G ≫ U.map J.ι =
    E.inv.app F ≫ U.map I.ι ≫ U.map (InjectiveResolution.desc g J I)
  calc
    _ = E.inv.app F ≫ U.map ((CochainComplex.single₀ _).map g) ≫ U.map J.ι := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ U.map J.ι) hE
    _ = E.inv.app F ≫ U.map (I.ι ≫ InjectiveResolution.desc g J I) := by
      rw [hI, Functor.map_comp]
    _ = _ := by simp only [Functor.map_comp]

attribute [local instance] HasDerivedCategory.standard

/-- The quasi-isomorphism stage of `cohomologyIso` is natural on the actual
restricted injective resolutions and their chosen descent maps. -/
@[reassoc]
theorem restrictedResolutionHypercohomology_naturality
    {F G : TopCat.Sheaf (ModuleCat.{u} S) X} (g : F ⟶ G) (n : ℤ) :
    SheafHypercohomology.hypercohomologyMap R X
        ((CochainComplex.single₀ _).map ((sheaves f X).map g)) n ≫
      SheafHypercohomology.hypercohomologyMap R X
        (restrictedResolutionMap f X G) n =
    SheafHypercohomology.hypercohomologyMap R X
        (restrictedResolutionMap f X F) n ≫
      SheafHypercohomology.hypercohomologyMap R X
        (((sheaves f X).mapHomologicalComplex (.up ℕ)).map
          (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))) n := by
  calc
    _ = SheafHypercohomology.hypercohomologyMap R X
        ((CochainComplex.single₀ _).map ((sheaves f X).map g) ≫
          restrictedResolutionMap f X G) n :=
      (SheafHypercohomology.hypercohomologyMap_comp R X _ _ n).symm
    _ = SheafHypercohomology.hypercohomologyMap R X
        (restrictedResolutionMap f X F ≫
          ((sheaves f X).mapHomologicalComplex (.up ℕ)).map
            (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))) n := by
      rw [restrictedResolutionMap_naturality]
    _ = _ := SheafHypercohomology.hypercohomologyMap_comp R X _ _ n

end HodgeConjecture.SheafCohomology.ScalarRestriction
