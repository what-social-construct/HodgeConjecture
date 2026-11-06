module

public import HodgeConjecture.Realization.DeRham.SheafComplex
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Differential forms under actual open immersions

An open immersion identifies sections on each image open with sections on
the original open subscheme. These are algebra identifications for the
original structure morphism. Applying the functor of actual Kähler forms
identifies their presheaves and their sheafifications, retaining the
canonical sheafification unit on every open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace HodgeConjecture.SchemeDeRham

variable (k : Type u) [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (i : Y ⟶ X) [IsOpenImmersion i]

/-- The section-ring identification of an open immersion preserves the actual base map. -/
theorem openImmersion_sectionBaseMap (U : Y.Opens) (a : k) :
    (i.appIso U).hom (sectionBaseMap k X f (i ''ᵁ U) a) =
      sectionBaseMap k Y (i ≫ f) U a := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (i ''ᵁ U) (by simp) ≫
    (i.appIso U).hom) a = _
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Sections on the actual image open are canonically equivalent as base algebras. -/
def openImmersionSectionEquiv (U : Y.Opens) :
    letI := sectionAlgebra k X f (i ''ᵁ U)
    letI := sectionAlgebra k Y (i ≫ f) U
    Γ(X, i ''ᵁ U) ≃ₐ[k] Γ(Y, U) := by
  letI := sectionAlgebra k X f (i ''ᵁ U)
  letI := sectionAlgebra k Y (i ≫ f) U
  exact { (i.appIso U).commRingCatIsoToRingEquiv with
    commutes' := openImmersion_sectionBaseMap k f i U }

/-- All section-algebra identifications commute with the original restriction maps. -/
def openImmersionSectionFunctorIso :
    i.opensFunctor.op ⋙ sectionFunctor k X f ≅ sectionFunctor k Y (i ≫ f) :=
  NatIso.ofComponents
    (fun U ↦ CommAlgCat.isoMk (openImmersionSectionEquiv k f i U.unop))
    (fun {U V} j ↦ by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      exact congrArg (fun g ↦ g a) (i.appIso_hom_naturality j))

/-- The actual differential-form presheaves restrict along the original open immersion. -/
def openImmersionFormsPresheafIso (n : ℕ) :
    i.opensFunctor.op ⋙ formsPresheaf k X f n ≅ formsPresheaf k Y (i ≫ f) n :=
  Functor.isoWhiskerRight (openImmersionSectionFunctorIso k f i)
    (AlgebraDeRham.formsFunctor k n)

/-- Restriction along the original open immersion commutes with actual sheafification. -/
def openImmersionFormsSheafIso (n : ℕ) :
    (i.opensFunctor.sheafPushforwardContinuous (ModuleCat.{u} k)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        (formsSheaf k X f n) ≅ formsSheaf k Y (i ≫ f) n :=
  (i.opensFunctor.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} k)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).symm.app
        (formsPresheaf k X f n) ≪≫
    (sheafification k Y).mapIso (openImmersionFormsPresheafIso k f i n)

/-- The open-immersion identification retains the canonical sheafification unit. -/
@[reassoc]
theorem openImmersionFormsSheafIso_unit (n : ℕ) :
    Functor.whiskerLeft i.opensFunctor.op
        (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f n)) ≫
        (openImmersionFormsSheafIso k f i n).hom.hom =
      (openImmersionFormsPresheafIso k f i n).hom ≫
        toSheafify (Opens.grothendieckTopology Y) (formsPresheaf k Y (i ≫ f) n) := by
  let c := i.opensFunctor.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} k)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let e := (sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} k)).mapIso
    (c.app (formsPresheaf k X f n))
  have hc : toSheafify (Opens.grothendieckTopology Y)
      (i.opensFunctor.op ⋙ formsPresheaf k X f n) ≫ e.hom =
      Functor.whiskerLeft i.opensFunctor.op
        (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f n)) :=
    i.opensFunctor.toSheafify_pullbackSheafificationCompatibility (ModuleCat.{u} k)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) (formsPresheaf k X f n)
  change Functor.whiskerLeft i.opensFunctor.op
      (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f n)) ≫
      e.inv ≫
      sheafifyMap (Opens.grothendieckTopology Y)
        (openImmersionFormsPresheafIso k f i n).hom = _
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (toSheafify_naturality (Opens.grothendieckTopology Y)
    (openImmersionFormsPresheafIso k f i n).hom).symm

/-- A proved local sheafification identification gives the canonical unit isomorphism
on every actual image open of the original scheme. -/
theorem openImmersionFormsSheafUnit_app_isIso (n : ℕ) (U : Y.Opens)
    (h : IsIso (toSheafify (Opens.grothendieckTopology Y)
      (formsPresheaf k Y (i ≫ f) n))) :
    IsIso ((toSheafify (Opens.grothendieckTopology X)
      (formsPresheaf k X f n)).app (op (i ''ᵁ U))) := by
  have : IsIso (toSheafify (Opens.grothendieckTopology Y)
      (formsPresheaf k Y (i ≫ f) n)) := h
  have : IsIso (openImmersionFormsPresheafIso k f i n).hom := inferInstance
  have : IsIso (openImmersionFormsSheafIso k f i n).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} k)).map
      (openImmersionFormsSheafIso k f i n).hom))
  let α := Functor.whiskerLeft i.opensFunctor.op
    (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f n))
  have : IsIso (α ≫ (openImmersionFormsSheafIso k f i n).hom.hom) := by
    change IsIso (Functor.whiskerLeft i.opensFunctor.op
      (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f n)) ≫ _)
    rw [openImmersionFormsSheafIso_unit]
    infer_instance
  have : IsIso α := IsIso.of_isIso_comp_right _
    (openImmersionFormsSheafIso k f i n).hom.hom
  exact inferInstanceAs (IsIso (α.app (op U)))

/-- The same canonical identification on the actual open range of the immersion. -/
theorem openImmersionFormsSheafUnit_range_isIso (n : ℕ)
    (h : IsIso (toSheafify (Opens.grothendieckTopology Y)
      (formsPresheaf k Y (i ≫ f) n))) :
    IsIso ((toSheafify (Opens.grothendieckTopology X)
      (formsPresheaf k X f n)).app (op i.opensRange)) := by
  rw [← i.image_top_eq_opensRange]
  exact openImmersionFormsSheafUnit_app_isIso k f i n ⊤ h

end HodgeConjecture.SchemeDeRham
