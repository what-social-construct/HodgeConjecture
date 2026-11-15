module

public import HodgeConjecture.CommutativeAlgebra.DeRham.Complex
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

/-!
# Functorial sectionwise algebraic de Rham complexes

The restriction maps are induced by the original universal Kähler derivation
and the universal property of exterior powers. Their compatibility with the
original de Rham differential is proved on its spanning generators.

The spanning and differential-naturality arguments adapt the local algebra
in AxiomMath/Stacks, revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeRhamSectionwise.lean`,
Apache-2.0. No upstream module is imported.
-/

set_option autoImplicit false

open CategoryTheory KaehlerDifferential

namespace HodgeConjecture.AlgebraDeRham

noncomputable section

universe u v

variable (k : Type u) [CommRing k]
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- Pullback on the actual Kähler module for a specified algebra map. -/
def kaehlerMap (f : A →ₐ[k] B) : Ω[A⁄k] →ₗ[k] Ω[B⁄k] := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  exact (KaehlerDifferential.map k k A B).restrictScalars k

@[simp]
theorem kaehlerMap_D (f : A →ₐ[k] B) (a : A) :
    kaehlerMap k f (D k A a) = D k B (f a) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  exact KaehlerDifferential.map_D k k A B a

theorem kaehlerMap_smul (f : A →ₐ[k] B) (a : A) (ω : Ω[A⁄k]) :
    kaehlerMap k f (a • ω) = f a • kaehlerMap k f ω := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  change KaehlerDifferential.map k k A B (a • ω) = _
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul B a _

/-- Read the target wedge as an alternating map over the source algebra. -/
def restrictedWedge [Algebra A B] (n : ℕ) :
    Ω[B⁄k] [⋀^Fin n]→ₗ[A] ⋀[B]^n Ω[B⁄k] where
  toMultilinearMap := (exteriorPower.ιMulti B n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _i _j h hij := (exteriorPower.ιMulti B n).map_eq_zero_of_eq v h hij

/-- Pullback on every actual exterior power of Kähler differentials. -/
def formsMap (f : A →ₐ[k] B) (n : ℕ) : ⋀[A]^n Ω[A⁄k] →ₗ[k] ⋀[B]^n Ω[B⁄k] := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  exact (exteriorPower.alternatingMapLinearEquiv
    ((restrictedWedge (A := A) k n).compLinearMap
      (KaehlerDifferential.map k k A B))).restrictScalars k

theorem formsMap_smul (f : A →ₐ[k] B) (n : ℕ) (a : A) (ω : ⋀[A]^n Ω[A⁄k]) :
    formsMap k f n (a • ω) = f a • formsMap k f n ω := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  change (exteriorPower.alternatingMapLinearEquiv
    ((restrictedWedge (A := A) k n).compLinearMap (KaehlerDifferential.map k k A B)))
    (a • ω) = _
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul B a _

@[simp]
theorem formsMap_ιMulti (f : A →ₐ[k] B) (n : ℕ) (v : Fin n → Ω[A⁄k]) :
    formsMap k f n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i ↦ kaehlerMap k f (v i)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    ((restrictedWedge (A := A) k n).compLinearMap (KaehlerDifferential.map k k A B)) v

@[simp]
theorem formsMap_ιMulti_D (f : A →ₐ[k] B) (n : ℕ) (v : Fin n → A) :
    formsMap k f n (exteriorPower.ιMulti A n (fun i ↦ D k A (v i))) =
      exteriorPower.ιMulti B n (fun i ↦ D k B (f (v i))) := by
  simp only [formsMap_ιMulti, kaehlerMap_D]

/-- The exact wedges span differential forms over the section algebra. -/
theorem span_exactWedges (n : ℕ) :
    Submodule.span A (Set.range fun v : Fin n → A ↦
      exteriorPower.ιMulti A n fun i ↦ D k A (v i)) = ⊤ :=
  KaehlerDifferential.span_range_ιMulti_D_eq_top (A := k) (B := A) n

/-- Scalar multiples of exact wedges span forms already over the fixed base ring. -/
theorem span_smul_exactWedges (n : ℕ) :
    Submodule.span k (Set.range fun v : Fin (n + 1) → A ↦
      v 0 • exteriorPower.ιMulti A n fun i ↦ D k A (v i.succ)) = ⊤ :=
  KaehlerDifferential.span_range_smul_ιMulti_D_eq_top (A := k) (B := A) n

/-- Test equality of base-linear maps on the actual de Rham generators. -/
theorem forms_linearMap_ext {M : Type u} [AddCommGroup M] [Module k M] (n : ℕ)
    {f g : ⋀[A]^n Ω[A⁄k] →ₗ[k] M}
    (h : ∀ v : Fin (n + 1) → A,
      f (v 0 • exteriorPower.ιMulti A n fun i ↦ D k A (v i.succ)) =
        g (v 0 • exteriorPower.ιMulti A n fun i ↦ D k A (v i.succ))) : f = g :=
  LinearMap.ext_on (span_smul_exactWedges k n) (by rintro _ ⟨v, rfl⟩; exact h v)

@[simp]
theorem formsMap_id (n : ℕ) : formsMap k (AlgHom.id k A) n = LinearMap.id := by
  apply forms_linearMap_ext k n
  intro v
  simp [formsMap_smul]

@[simp]
theorem formsMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C) (n : ℕ) :
    formsMap k (g.comp f) n = (formsMap k g n).comp (formsMap k f n) := by
  apply forms_linearMap_ext k n
  intro v
  simp [formsMap_smul]

/-- Degree-zero form pullback is the original algebra map. -/
theorem formsMap_zeroEquiv (f : A →ₐ[k] B) :
    ((exteriorPower.zeroEquiv B Ω[B⁄k]).restrictScalars k).toLinearMap.comp
        (formsMap k f 0) =
      f.toLinearMap.comp ((exteriorPower.zeroEquiv A Ω[A⁄k]).restrictScalars k).toLinearMap := by
  apply forms_linearMap_ext k 0
  intro v
  simp [formsMap_smul]

/-- Degree-one form pullback is the original universal Kähler map. -/
theorem formsMap_oneEquiv (f : A →ₐ[k] B) :
    ((exteriorPower.oneEquiv B Ω[B⁄k]).restrictScalars k).toLinearMap.comp
        (formsMap k f 1) =
      (kaehlerMap k f).comp
        ((exteriorPower.oneEquiv A Ω[A⁄k]).restrictScalars k).toLinearMap := by
  apply forms_linearMap_ext k 1
  intro v
  simp [formsMap_smul, kaehlerMap_smul]

/-- An actual algebra equivalence induces an equivalence on the original forms. -/
def formsEquiv (e : A ≃ₐ[k] B) (n : ℕ) : ⋀[A]^n Ω[A⁄k] ≃ₗ[k] ⋀[B]^n Ω[B⁄k] where
  __ := formsMap k e.toAlgHom n
  invFun := formsMap k e.symm.toAlgHom n
  left_inv ω := by
    change ((formsMap k e.symm.toAlgHom n).comp (formsMap k e.toAlgHom n)) ω = ω
    rw [← formsMap_comp]
    have he : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k A := by
      ext a
      exact e.symm_apply_apply a
    rw [he, formsMap_id]
    rfl
  right_inv ω := by
    change ((formsMap k e.toAlgHom n).comp (formsMap k e.symm.toAlgHom n)) ω = ω
    rw [← formsMap_comp]
    have he : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id k B := by
      ext b
      exact e.apply_symm_apply b
    rw [he, formsMap_id]
    rfl

/-- Pullback commutes with the original de Rham differential in every degree. -/
theorem formsMap_deRhamDifferential (f : A →ₐ[k] B) (n : ℕ) :
    (formsMap k f (n + 1)).comp (deRhamDifferential (A := k) n) =
      (deRhamDifferential (A := k) n).comp (formsMap k f n) := by
  apply forms_linearMap_ext k n
  intro v
  simp only [LinearMap.comp_apply, formsMap_smul, formsMap_ιMulti_D,
    deRhamDifferential_smul_ιMulti_D]
  exact (deRhamDifferential_smul_ιMulti_D (A := k) n (fun i ↦ f (v i))).symm

/-- The actual de Rham complex map induced by an algebra map. -/
def deRhamComplexMap (f : A →ₐ[k] B) : deRhamComplex k A ⟶ deRhamComplex k B where
  f n := ModuleCat.ofHom (formsMap k f n)
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    simp only [deRhamComplex_d]
    exact ModuleCat.hom_ext (formsMap_deRhamDifferential k f i).symm

/-- Coordinate algebra equivalences preserve the original de Rham differential. -/
def deRhamComplexIso (e : A ≃ₐ[k] B) : deRhamComplex k A ≅ deRhamComplex k B :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (formsEquiv k e n).toModuleIso)
    (fun i j hij ↦ (deRhamComplexMap k e.toAlgHom).comm' i j hij)

/-- Forms of a fixed degree, as a functor on commutative base algebras. -/
def formsFunctor (n : ℕ) : CommAlgCat.{u} k ⥤ ModuleCat.{u} k where
  obj A := ModuleCat.of k (⋀[A]^n Ω[A⁄k])
  map f := ModuleCat.ofHom (formsMap k f.hom n)
  map_id _A := ModuleCat.hom_ext (formsMap_id k n)
  map_comp f g := ModuleCat.hom_ext (formsMap_comp k f.hom g.hom n)

/-- The actual de Rham differential as a natural transformation. -/
def differential (n : ℕ) : formsFunctor k n ⟶ formsFunctor k (n + 1) where
  app _A := ModuleCat.ofHom (deRhamDifferential (A := k) n)
  naturality {_ _} f := ModuleCat.hom_ext (formsMap_deRhamDifferential k f.hom n).symm

/-- Sectionwise forms and differentials for any presheaf of base algebras. -/
def presheafComplex {D : Type v} [Category D] (R : D ⥤ CommAlgCat.{u} k) :
    CochainComplex (D ⥤ ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n ↦ R ⋙ formsFunctor k n)
    (fun n ↦ Functor.whiskerLeft R (differential k n)) (fun n ↦ by
      ext U : 2
      apply ModuleCat.hom_ext
      change (deRhamDifferential (A := k) (B := R.obj U) (n + 1)).comp
        (deRhamDifferential n) = 0
      exact deRhamDifferential_comp_deRhamDifferential n)

end

end HodgeConjecture.AlgebraDeRham
