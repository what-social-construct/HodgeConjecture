module

public import HodgeConjecture.SheafCohomology.Hypercohomology
public import HodgeConjecture.SheafCohomology.FlasqueDerived
public import HodgeConjecture.SheafCohomology.FlasqueComplex

@[expose] public section

/-!
# The original bounded-below comparison on flasque sheaf complexes

A native monomorphic injective replacement has an acyclic flasque
quotient. Its sections are acyclic by the shared bounded-below argument.
Naturality then proves invertibility of the original derived-functor unit.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace HodgeConjecture.SheafHypercohomology

universe u

variable (k : Type u) [CommRing k] (X : TopCat.{u})

/-- Scalar forgetting tests the original module-valued sections map. -/
theorem globalSections_quasiIso_of_mono
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℤ}
    (i : K ⟶ L) [Mono i] [QuasiIso i]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (X := X)
      ((SheafCohomology.LinearCoefficients.underlying k X).obj (K.X n)))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (X := X)
      ((SheafCohomology.LinearCoefficients.underlying k X).obj (L.X n)))
    (b : ℤ) [L.IsStrictlyGE b] :
    QuasiIso (((globalSections k X).mapHomologicalComplex (.up ℤ)).map i) := by
  let T := SheafCohomology.LinearCoefficients.underlying k X
  have h := SheafCohomology.FlasqueComplex.sections_quasiIso_of_mono X
    ((T.mapHomologicalComplex (.up ℤ)).map i) hK hL b ⊤
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((globalSections k X).mapHomologicalComplex (.up ℤ)).map i)
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).mp h

attribute [local instance] HasDerivedCategory.standard

/-- The existing derived-functor unit is invertible for a bounded-below flasque complex. -/
theorem isIso_comparison_of_flasqueTerms (K : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{u} k) X))
    (hK : ∀ n : ℤ, (K.obj.X n).IsFlasque) :
    IsIso ((globalSections k X).rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, hb⟩ := K.property
  let : K.obj.IsStrictlyGE b := hb
  obtain ⟨L, i, hi, hqi, hI, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K.obj (b - 1) b (by omega)
  let : Mono i := hi
  let : QuasiIso i := hqi
  let : L.IsStrictlyGE (b - 1) := hL
  let Lplus : CochainComplex.Plus (TopCat.Sheaf (ModuleCat.{u} k) X) := ⟨L, ⟨b - 1, hL⟩⟩
  let ip : K ⟶ Lplus := ObjectProperty.homMk i
  have hΓi : QuasiIso (((globalSections k X).mapHomologicalComplex (.up ℤ)).map i) :=
    globalSections_quasiIso_of_mono k X i
      (fun n ↦ by
        let : (K.obj.X n).IsFlasque := hK n
        exact SheafCohomology.LinearCoefficients.underlying_isFlasque_of_isFlasque k X _)
      (fun n ↦ by
        let : Injective (L.X n) := hI n
        exact SheafCohomology.LinearCoefficients.underlying_isFlasque k X _) (b - 1)
  have : IsIso (DerivedCategory.Plus.Q.map ip) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _) ip hqi
  have : IsIso (DerivedCategory.Plus.Q.map ((globalSections k X).mapCochainComplexPlus.map ip)) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _)
      ((globalSections k X).mapCochainComplexPlus.map ip) hΓi
  let (n : ℤ) : Injective (Lplus.obj.X n) := hI n
  have : IsIso ((globalSections k X).rightDerivedFunctorPlusUnit.app Lplus) :=
    BoundedBelowDerived.isIso_unit_of_injectiveTerms (globalSections k X) Lplus
  have hnat := (globalSections k X).rightDerivedFunctorPlusUnit.naturality ip
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (((globalSections k X).rightDerivedFunctorPlusUnit.app K) ≫
      (globalSections k X).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ip)) := by
    rw [← hnat]
    infer_instance
  exact (isIso_comp_right_iff ((globalSections k X).rightDerivedFunctorPlusUnit.app K)
    ((globalSections k X).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ip))).mp this

/-- Extension by zero retains the original flasque terms and has flasque zero terms. -/
theorem nonnegativeToPlus_flasqueTerms
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    ((nonnegativeToPlus k X K).obj.X n).IsFlasque := by
  change (HomologicalComplex.extend.X K ((ComplexShape.embeddingUpIntGE 0).r n)).IsFlasque
  cases (ComplexShape.embeddingUpIntGE 0).r n with
  | none =>
    exact SheafCohomology.FlasqueComplex.isFlasque_of_isZero X _ (isZero_zero _)
  | some q =>
    exact hK q

/-- The original comparison is invertible for a nonnegative flasque sheaf complex. -/
theorem comparison_isIso_of_flasqueTerms
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) : IsIso (comparison k X K) :=
  isIso_comparison_of_flasqueTerms k X (nonnegativeToPlus k X K)
    (nonnegativeToPlus_flasqueTerms k X K hK)

/-- Every integer-degree comparison uses that same derived-functor unit. -/
theorem comparisonFromComplexHomology_isIso_of_flasqueTerms
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    IsIso (comparisonFromComplexHomology k X K n) := by
  have := comparison_isIso_of_flasqueTerms k X K hK
  unfold comparisonFromComplexHomology comparisonOnHomology
  infer_instance

/-- Homology of the original termwise-sections complex computes the existing derived target. -/
def complexHomologyIsoHypercohomology
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    (underivedGlobalSections k X K).obj.homology n ≅ hypercohomology k X K n := by
  have := comparisonFromComplexHomology_isIso_of_flasqueTerms k X K hK n
  exact asIso (comparisonFromComplexHomology k X K n)

@[simp]
theorem complexHomologyIsoHypercohomology_hom
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ)
    (hK : ∀ q, (K.X q).IsFlasque) (n : ℤ) :
    (complexHomologyIsoHypercohomology k X K hK n).hom =
      comparisonFromComplexHomology k X K n := rfl

end HodgeConjecture.SheafHypercohomology
