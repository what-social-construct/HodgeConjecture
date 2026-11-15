module

public import HodgeConjecture.Realization.DeRham.PresheafComplex
public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.Geometry.SectionAlgebra
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Forget

@[expose] public section

/-!
# The sectionwise and sheafified de Rham complexes of a scheme over a ring

The base action on each section ring comes from the actual structure
morphism `X ⟶ Spec k`. Restriction is an algebra map for that action.
Applying the functorial algebraic de Rham construction gives a complex of
presheaves of `k`-modules on the actual open subsets of `X`; its degreewise
sheafification is a complex of actual sheaves of `k`-modules.

The differential is only base-linear, so this complex is not formed in the
category of `𝒪_X`-modules. No affine-section or cohomological-acyclicity
comparison is assumed in this construction. Identifying its sheaf terms
with the usual differential sheaves and computing its derived global
sections are subsequent comparison statements.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

/-- The section algebras and their actual restriction maps. -/
def sectionFunctor : X.Opensᵒᵖ ⥤ CommAlgCat.{u} k := by
  letI (U : X.Opens) := sectionAlgebra k X f U
  exact {
    obj U := CommAlgCat.of k Γ(X, U.unop)
    map i := CommAlgCat.ofHom (sectionMap k X f i.unop)
    map_id U := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      exact congrArg (fun g ↦ g a) (X.presheaf.map_id U)
    map_comp i j := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      exact congrArg (fun g ↦ g a) (X.presheaf.map_comp i j) }

/-- The presheaf of actual degree-`n` Kähler forms on the section rings. -/
def formsPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{u} k) X :=
  sectionFunctor k X f ⋙ AlgebraDeRham.formsFunctor k n

/-- Regular functions with the fixed base action induced by the structure morphism. -/
def functionsPresheaf : TopCat.Presheaf (ModuleCat.{u} k) X :=
  sectionFunctor k X f ⋙ forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙
    forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)

theorem functionsPresheaf_isSheaf : (functionsPresheaf k X f).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget (ModuleCat.{u} k)) _).mpr
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) X.presheaf).mp
    X.sheaf.property

/-- Degree-zero forms are the actual regular-function sheaf, compatibly with restriction. -/
def zeroFormsIsoFunctions : formsPresheaf k X f 0 ≅ functionsPresheaf k X f :=
  NatIso.ofComponents (fun U ↦
    letI := sectionAlgebra k X f U.unop
    ((exteriorPower.zeroEquiv Γ(X, U.unop) Ω[Γ(X, U.unop)⁄k]).restrictScalars k).toModuleIso)
    (fun {U V} i ↦ by
      let := sectionAlgebra k X f U.unop
      let := sectionAlgebra k X f V.unop
      exact ModuleCat.hom_ext (AlgebraDeRham.formsMap_zeroEquiv k
        (sectionMap k X f i.unop)))

theorem zeroFormsPresheaf_isSheaf : (formsPresheaf k X f 0).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_iso (zeroFormsIsoFunctions k X f).symm
    (functionsPresheaf_isSheaf k X f)

/-- The sectionwise de Rham complex on all open subsets of the original scheme. -/
def presheafComplex : CochainComplex (TopCat.Presheaf (ModuleCat.{u} k) X) ℕ :=
  AlgebraDeRham.presheafComplex k (sectionFunctor k X f)

@[simp]
theorem presheafComplex_X (n : ℕ) :
    (presheafComplex k X f).X n = formsPresheaf k X f n := rfl

/-- The differential of the presheaf complex is the original sectionwise differential. -/
@[simp]
theorem presheafComplex_d (n : ℕ) :
    (presheafComplex k X f).d n (n + 1) =
      Functor.whiskerLeft (sectionFunctor k X f) (AlgebraDeRham.differential k n) := by
  apply CochainComplex.of_d

/-- Sheafification on the actual open-subset site, with fixed base-ring scalars. -/
def sheafification : TopCat.Presheaf (ModuleCat.{u} k) X ⥤
    TopCat.Sheaf (ModuleCat.{u} k) X :=
  SheafCohomology.sheafification k X

instance : (sheafification k X).Additive :=
  inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).Additive

/-- The sheafification of the actual sectionwise differential forms. -/
def formsSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{u} k) X :=
  (sheafification k X).obj (formsPresheaf k X f n)

/-- The actual sheafified de Rham complex of the structure morphism. -/
def sheafComplex : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ :=
  SheafCohomology.sheafifyComplex k X (presheafComplex k X f)

@[simp]
theorem sheafComplex_X (n : ℕ) :
    (sheafComplex k X f).X n = formsSheaf k X f n := rfl

/-- The arrow is induced by sheafifying the original sectionwise differential. -/
@[simp]
theorem sheafComplex_d (n : ℕ) :
    (sheafComplex k X f).d n (n + 1) =
      (sheafification k X).map
        (Functor.whiskerLeft (sectionFunctor k X f) (AlgebraDeRham.differential k n)) := by
  change (sheafification k X).map ((presheafComplex k X f).d n (n + 1)) = _
  rw [presheafComplex_d]

/-- The canonical map from the original sectionwise complex to the underlying
presheaves of the actual sheaf complex. -/
def toSheafComplex : presheafComplex k X f ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (sheafComplex k X f) :=
  SheafCohomology.toSheafifyComplex k X (presheafComplex k X f)

end

end HodgeConjecture.SchemeDeRham
