module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.SheafCohomology.CochainPresheaf
public import Mathlib.Topology.Category.TopCat.Opens

@[expose] public section

/-!
# The existing singular cochains on open subspaces

This is the restriction of `SingularCochains.complex` along Mathlib's
`Opens.toTopCat`. Both its cochains and differential are the existing ones.
The sheaf complex uses the already instantiated native sheafification.
No sheaf property is asserted for the raw singular-cochain presheaves.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory TopologicalSpace Opposite

/-- Continuous pullback packages the existing complexes as a functor. -/
def functor : TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℚ) ℕ where
  obj X := complex X.unop
  map f := pullback f.unop
  map_id X := pullback_id X.unop
  map_comp f g := pullback_comp g.unop f.unop

variable (X : TopCat.{0})

/-- Literal singular cochains on each native open subspace. -/
def presheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℚ) X :=
  SheafCohomology.CochainPresheaf.presheaf ℚ functor X n

/-- The original singular coboundary, natural under open restriction. -/
def presheafDifferential (n : ℕ) : presheaf X n ⟶ presheaf X (n + 1) :=
  SheafCohomology.CochainPresheaf.differential ℚ functor X n

theorem presheafDifferential_comp (n : ℕ) :
    presheafDifferential X n ≫ presheafDifferential X (n + 1) = 0 :=
  SheafCohomology.CochainPresheaf.differential_comp ℚ functor X n

/-- The all-degree presheaf complex, with no replacement cochain model. -/
def presheafComplex : CochainComplex (TopCat.Presheaf (ModuleCat.{0} ℚ) X) ℕ :=
  SheafCohomology.CochainPresheaf.complex ℚ functor X

@[simp]
theorem presheafComplex_d (n : ℕ) :
    (presheafComplex X).d n (n + 1) = presheafDifferential X n :=
  CochainComplex.of_d _ _ n

/-- Evaluation recovers the original singular complex on the same open subspace. -/
def sectionComplexIso (U : Opens X) : complex ((Opens.toTopCat X).obj U) ≅
    (((evaluation _ (ModuleCat.{0} ℚ)).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (presheafComplex X) :=
  SheafCohomology.CochainPresheaf.sectionComplexIso ℚ functor X U

/-- Native sheafification of the existing degree-`n` cochain presheaf. -/
def cochainSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  SheafCohomology.CochainPresheaf.sheaf ℚ functor X n

def sheafDifferential (n : ℕ) : cochainSheaf X n ⟶ cochainSheaf X (n + 1) :=
  (SheafCohomology.sheafification ℚ X).map (presheafDifferential X n)

theorem sheafDifferential_comp (n : ℕ) :
    sheafDifferential X n ≫ sheafDifferential X (n + 1) = 0 :=
  SheafCohomology.CochainPresheaf.sheafDifferential_comp ℚ functor X n

/-- The singular-cochain sheaf complex in the already instantiated category. -/
def sheafComplex : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ :=
  SheafCohomology.CochainPresheaf.sheafComplex ℚ functor X

@[simp]
theorem sheafComplex_d (n : ℕ) :
    (sheafComplex X).d n (n + 1) = sheafDifferential X n :=
  congrArg ((SheafCohomology.sheafification ℚ X).map) (CochainComplex.of_d _ _ n)

/-- The actual global cochains map to sections of the same sheaf complex by
the native sheafification unit. `SingularSheafGlobalSections` proves the
quasi-isomorphism under explicit paracompact Hausdorff hypotheses. -/
def globalCochainsToSheaf : complex X ⟶
    ((SheafHypercohomology.globalSections ℚ X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (sheafComplex X) :=
  SheafCohomology.CochainPresheaf.globalUnit ℚ functor X

/-- The global comparison is the literal native unit after restriction to the top open. -/
@[simp]
theorem globalCochainsToSheaf_apply (n : ℕ) (φ : Cochain X n) :
    (globalCochainsToSheaf X).f n φ =
      (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op ⊤)
        ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ) := rfl

/-- Restricting first to the top open gives the original open-subspace pullback. -/
theorem restrict_top_cochain (U : Opens X) (n : ℕ) (φ : Cochain X n) :
    (presheaf X n).map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ) =
        (pullback (Opens.inclusion' U)).f n φ := rfl

end HodgeConjecture.SingularCochains
