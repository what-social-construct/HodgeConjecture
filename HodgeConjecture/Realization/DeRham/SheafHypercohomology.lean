module

public import HodgeConjecture.Realization.DeRham.SheafComplex
public import HodgeConjecture.SheafCohomology.LinearSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Actual bounded-below hypercohomology of sheaf complexes

Global sections evaluate a sheaf of `k`-modules on the whole space. Its
bounded-below right derived functor is constructed using the actual
Grothendieck abelian category of these sheaves and its enough injectives.
Nonnegative complexes extend by zero to integer degrees before applying
derived global sections. Hypercohomology is the homology of this derived
object, with the canonical underived-to-derived comparison.

No derived target or comparison is supplied as a hypothesis. This file
does not assert that a chosen Čech complex computes hypercohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace HodgeConjecture.SheafHypercohomology

variable (k : Type u) [CommRing k] (X : TopCat.{u})

/-- Actual global sections of a sheaf of modules over the fixed base ring. -/
def globalSections : TopCat.Sheaf (ModuleCat.{u} k) X ⥤ ModuleCat.{u} k :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

instance : (globalSections k X).Additive where
  map_add := by intros; rfl

/-- Extend an actual nonnegative sheaf complex by zero in negative degrees. -/
def nonnegativeToPlus
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) :
    CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{u} k) X) :=
  ⟨K.extend (ComplexShape.embeddingUpIntGE 0), ⟨0, inferInstance⟩⟩

attribute [local instance] HasDerivedCategory.standard

/-- The actual bounded-below derived global sections of a nonnegative sheaf complex. -/
def derivedGlobalSections
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) :
    DerivedCategory.Plus (ModuleCat.{u} k) :=
  (globalSections k X).rightDerivedFunctorPlus.obj
    (DerivedCategory.Plus.Q.obj (nonnegativeToPlus k X K))

/-- Hypercohomology is homology of the constructed derived-global-sections object. -/
def hypercohomology
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℤ) :
    ModuleCat.{u} k :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj
    (derivedGlobalSections k X K)

/-- Global sections applied term by term, retained as an actual bounded-below complex. -/
def underivedGlobalSections
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) :
    CochainComplex.Plus (ModuleCat.{u} k) :=
  (globalSections k X).mapCochainComplexPlus.obj (nonnegativeToPlus k X K)

/-- The canonical comparison from termwise global sections to derived global sections. -/
def comparison
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) :
    DerivedCategory.Plus.Q.obj (underivedGlobalSections k X K) ⟶
      derivedGlobalSections k X K :=
  (globalSections k X).rightDerivedFunctorPlusUnit.app (nonnegativeToPlus k X K)

/-- The canonical underived-to-hypercohomology map in each integer degree. -/
def comparisonOnHomology
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).obj
        (DerivedCategory.Plus.Q.obj (underivedGlobalSections k X K)) ⟶
      hypercohomology k X K n :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).map (comparison k X K)

/-- The same canonical comparison, with the actual homology of the underived complex as source. -/
def comparisonFromComplexHomology
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℤ) :
    (underivedGlobalSections k X K).obj.homology n ⟶ hypercohomology k X K n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.app
      (underivedGlobalSections k X K).obj ≫ comparisonOnHomology k X K n

variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}

/-- A morphism of the original nonnegative complexes extends by zero. -/
def nonnegativeMap (φ : K ⟶ L) :
    nonnegativeToPlus k X K ⟶ nonnegativeToPlus k X L :=
  ObjectProperty.homMk (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntGE 0))

/-- Functoriality of the actual derived-global-sections construction. -/
def derivedGlobalSectionsMap (φ : K ⟶ L) :
    derivedGlobalSections k X K ⟶ derivedGlobalSections k X L :=
  (globalSections k X).rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Q.map (nonnegativeMap k X φ))

/-- Functoriality of actual hypercohomology on nonnegative sheaf complexes. -/
def hypercohomologyMap (φ : K ⟶ L) (n : ℤ) :
    hypercohomology k X K n ⟶ hypercohomology k X L n :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} k) n).map
    (derivedGlobalSectionsMap k X φ)

/-- The canonical comparison respects the original morphisms of sheaf complexes. -/
@[reassoc]
theorem comparison_naturality (φ : K ⟶ L) :
    DerivedCategory.Plus.Q.map
        ((globalSections k X).mapCochainComplexPlus.map (nonnegativeMap k X φ)) ≫
        comparison k X L =
      comparison k X K ≫ derivedGlobalSectionsMap k X φ :=
  (globalSections k X).rightDerivedFunctorPlusUnit.naturality (nonnegativeMap k X φ)

end HodgeConjecture.SheafHypercohomology

namespace HodgeConjecture.BoundedBelowDerived

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/-- The component identification for a functor applied to an extended complex. -/
def mapExtendXIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : Option ι) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => (F.map_isZero (isZero_zero C)).isoZero

/-- Mapping an extended complex commutes canonically with extension by zero. -/
def mapExtendIso {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ mapExtendXIso F K (e.r i))
    (fun i j _ ↦ by
      change (mapExtendXIso F K (e.r i)).hom ≫
          HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i) (e.r j) =
        F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫
          (mapExtendXIso F K (e.r j)).hom
      cases e.r i with
      | none => exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
      | some a =>
        cases e.r j with
        | none => exact (isZero_zero D).eq_of_tgt _ _
        | some b =>
          simp [mapExtendXIso, HomologicalComplex.extend.d, HomologicalComplex.extend.X,
            Category.id_comp, Category.comp_id])

/-- A nonnegative complex viewed as a bounded-below integer complex. -/
def nonnegativePlus (K : CochainComplex C ℕ) : CochainComplex.Plus C :=
  ⟨K.extend (ComplexShape.embeddingUpIntGE 0), ⟨0, inferInstance⟩⟩

/-- The actual derived comparison is invertible on a bounded-below complex of injectives. -/
theorem isIso_unit_of_injectiveTerms (K : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  let L : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ K.obj (fun _ ↦ inferInstance)
  obtain ⟨n, hn⟩ := K.property
  have hL : L.IsStrictlyGE n := by
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)]
  let Lplus : CochainComplex.Plus (InjectiveObject C) := ⟨L, ⟨n, hL⟩⟩
  change IsIso (F.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι C).mapCochainComplexPlus.obj Lplus))
  infer_instance

/-- An ordinary injective resolution computes the actual bounded-below derived functor
on the original object placed in degree zero. -/
def injectiveResolutionDerivedIso (M : C) (I : InjectiveResolution M) :
    F.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj (nonnegativePlus ((CochainComplex.single₀ C).obj M))) ≅
      DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj (nonnegativePlus I.cocomplex)) := by
  let i : nonnegativePlus ((CochainComplex.single₀ C).obj M) ⟶
      nonnegativePlus I.cocomplex :=
    ObjectProperty.homMk (HomologicalComplex.extendMap I.ι (ComplexShape.embeddingUpIntGE 0))
  have hi : CochainComplex.Plus.quasiIso C i := by
    change QuasiIso
      (HomologicalComplex.extendMap I.ι (ComplexShape.embeddingUpIntGE 0))
    infer_instance
  haveI : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) i hi
  haveI (n : ℤ) : Injective ((nonnegativePlus I.cocomplex).obj.X n) := by
    change Injective ((I.cocomplex.extend (ComplexShape.embeddingUpIntGE 0)).X n)
    infer_instance
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app (nonnegativePlus I.cocomplex)) :=
    isIso_unit_of_injectiveTerms F (nonnegativePlus I.cocomplex)
  exact F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map i)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (nonnegativePlus I.cocomplex))).symm

/-- For a single object the constructed derived-global-sections homology agrees with
the ordinary right derived functor, through the same actual injective resolution. -/
def singleHypercohomologyIsoRightDerived (M : C) (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        (F.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (nonnegativePlus ((CochainComplex.single₀ C).obj M)))) ≅
      (F.rightDerived n).obj M :=
  (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      (injectiveResolutionDerivedIso F M I) ≪≫
    (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
      (F.mapCochainComplexPlus.obj (nonnegativePlus I.cocomplex)).obj ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
      (mapExtendIso F I.cocomplex (ComplexShape.embeddingUpIntGE 0)) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      (ComplexShape.embeddingUpIntGE 0) (by simp) ≪≫
    (I.isoRightDerivedObj F n).symm

/-- Exact coefficient forgetting commutes with ordinary right derived functors.
Both sides are computed on the same actual injective resolution of the source object. -/
def rightDerivedPostcomposeIso {E : Type*} [Category* E] [Abelian E]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology] (M : C) (n : ℕ) :
    T.obj ((F.rightDerived n).obj M) ≅ ((F ⋙ T).rightDerived n).obj M :=
  let I := injectiveResolution M
  T.mapIso (I.isoRightDerivedObj F n) ≪≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso T).symm ≪≫
    (I.isoRightDerivedObj (F ⋙ T) n).symm

end HodgeConjecture.BoundedBelowDerived

namespace HodgeConjecture.SheafHypercohomology

variable (k : Type u) [CommRing k] (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- Hypercohomology of a single actual sheaf is ordinary derived global sections.
The comparison uses the chosen actual injective resolution, not an assumed agreement. -/
def singleIsoRightDerived (M : TopCat.Sheaf (ModuleCat.{u} k) X) (n : ℕ) :
    hypercohomology k X ((CochainComplex.single₀ _).obj M) (n : ℤ) ≅
      ((globalSections k X).rightDerived n).obj M :=
  BoundedBelowDerived.singleHypercohomologyIsoRightDerived (globalSections k X) M
    (injectiveResolution M) n

end HodgeConjecture.SheafHypercohomology

namespace HodgeConjecture.SchemeDeRham

open AlgebraicGeometry

variable (k : Type u) [CommRing k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

attribute [local instance] HasDerivedCategory.standard

/-- Derived global sections of the actual sheafified de Rham complex of the scheme. -/
def derivedGlobalSections : DerivedCategory.Plus (ModuleCat.{u} k) :=
  SheafHypercohomology.derivedGlobalSections k X (sheafComplex k X f)

/-- Actual de Rham hypercohomology of the original scheme over the fixed base ring. -/
def hypercohomology (n : ℤ) : ModuleCat.{u} k :=
  SheafHypercohomology.hypercohomology k X (sheafComplex k X f) n

/-- Canonical map from the homology of termwise sheaf global sections to actual
scheme de Rham hypercohomology. Its invertibility requires a separate comparison proof. -/
def underivedComparison (n : ℤ) :
    (SheafHypercohomology.underivedGlobalSections k X (sheafComplex k X f)).obj.homology n ⟶
      hypercohomology k X f n :=
  SheafHypercohomology.comparisonFromComplexHomology k X (sheafComplex k X f) n

end HodgeConjecture.SchemeDeRham
