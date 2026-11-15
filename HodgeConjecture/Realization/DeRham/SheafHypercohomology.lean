module

public import HodgeConjecture.Realization.DeRham.SheafComplex
public import HodgeConjecture.SheafCohomology.Hypercohomology

/-!
# Derived sections of the original scheme de Rham complex

The generic bounded-below construction has its shared sheaf-cohomology
owner. These scheme wrappers retain the original objects and public names.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

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
