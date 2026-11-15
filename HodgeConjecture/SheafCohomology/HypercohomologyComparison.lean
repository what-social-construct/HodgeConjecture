module

public import HodgeConjecture.SheafCohomology.Hypercohomology

@[expose] public noncomputable section

/-!
# Comparisons using the original nonnegative complexes

Native extension by zero identifies the original nonnegative homology
with its integer-degree counterpart. Quasi-isomorphisms of the original
sheaf complexes induce isomorphisms on the existing derived sections.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HodgeConjecture.SheafHypercohomology

universe u

variable (k : Type u) [CommRing k] (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- The original termwise-sections homology agrees with the existing extension by zero. -/
def nonnegativeSectionsHomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℕ) :
    (((globalSections k X).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      (underivedGlobalSections k X K).obj.homology (n : ℤ) :=
  ((((globalSections k X).mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (by simp)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) (n : ℤ)).mapIso
      (BoundedBelowDerived.mapExtendIso (globalSections k X) K
        (ComplexShape.embeddingUpIntGE 0)).symm

variable {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}

/-- The original derived-sections map inverts a quasi-isomorphism of the original complexes. -/
theorem derivedGlobalSectionsMap_isIso (φ : K ⟶ L) [QuasiIso φ] :
    IsIso (derivedGlobalSectionsMap k X φ) := by
  have hφ : CochainComplex.Plus.quasiIso _ (nonnegativeMap k X φ) := by
    change QuasiIso (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntGE 0))
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map (nonnegativeMap k X φ)) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _)
      (nonnegativeMap k X φ) hφ
  unfold derivedGlobalSectionsMap
  infer_instance

/-- This is invertibility of the existing map on hypercohomology, in every integer degree. -/
theorem hypercohomologyMap_isIso (φ : K ⟶ L) [QuasiIso φ] (n : ℤ) :
    IsIso (hypercohomologyMap k X φ n) := by
  have := derivedGlobalSectionsMap_isIso k X φ
  unfold hypercohomologyMap
  infer_instance

/-- The isomorphism is induced by the given original quasi-isomorphism. -/
def hypercohomologyIsoOfQuasiIso (φ : K ⟶ L) [QuasiIso φ] (n : ℤ) :
    hypercohomology k X K n ≅ hypercohomology k X L n := by
  have := hypercohomologyMap_isIso k X φ n
  exact asIso (hypercohomologyMap k X φ n)

@[simp]
theorem hypercohomologyIsoOfQuasiIso_hom (φ : K ⟶ L) [QuasiIso φ] (n : ℤ) :
    (hypercohomologyIsoOfQuasiIso k X φ n).hom = hypercohomologyMap k X φ n := rfl

end HodgeConjecture.SheafHypercohomology
