module

public import HodgeConjecture.Realization.DeRham.OpenImmersionForms

/-!
# Natural local trivializations of actual form sheaves

A proved trivialization of the differential forms on an open chart gives
a trivialization of the actual ambient form sheaf on every open contained
in that chart. The construction uses the canonical sheafification unit
and the actual section-ring identification of the original open immersion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace HodgeConjecture.SchemeDeRham

variable (k : Type u) [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (i : Y ⟶ X) [IsOpenImmersion i]

/-- The actual regular functions also retain the original open-immersion section maps. -/
def openImmersionFunctionsPresheafIso :
    i.opensFunctor.op ⋙ functionsPresheaf k X f ≅ functionsPresheaf k Y (i ≫ f) :=
  Functor.isoWhiskerRight (openImmersionSectionFunctorIso k f i)
    (forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙
      forget₂ (AlgCat.{u} k) (ModuleCat.{u} k))

/-- Local coordinates on sectionwise one-forms induce natural coordinates on the
actual ambient sheaf over all image opens of the original chart. -/
def openImmersionOneFormsTrivialization
    (e : formsPresheaf k Y (i ≫ f) 1 ≅ functionsPresheaf k Y (i ≫ f)) :
    i.opensFunctor.op ⋙ (formsSheaf k X f 1).obj ≅
      i.opensFunctor.op ⋙ functionsPresheaf k X f := by
  have hs : (formsPresheaf k Y (i ≫ f) 1).IsSheaf :=
    TopCat.Presheaf.isSheaf_of_iso e.symm (functionsPresheaf_isSheaf k Y (i ≫ f))
  let η := (toSheafComplex k Y (i ≫ f)).f 1
  have : IsIso η := isIso_toSheafify (Opens.grothendieckTopology Y) hs
  exact (sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} k)).mapIso
      (openImmersionFormsSheafIso k f i 1) ≪≫
    (asIso η).symm ≪≫ e ≪≫ (openImmersionFunctionsPresheafIso k f i).symm

/-- The category of actual ambient opens contained in the chart image. -/
abbrev OpensInRange := ObjectProperty.FullSubcategory (fun V : X.Opens ↦ V ≤ i.opensRange)

/-- The original ambient inclusion of opens under the chart. -/
abbrev opensInRangeInclusion : OpensInRange i ⥤ X.Opens :=
  ObjectProperty.ι _

/-- Take the actual inverse image open in the original chart. -/
def opensInRangePreimage : OpensInRange i ⥤ Y.Opens :=
  opensInRangeInclusion i ⋙ Opens.map i.base

/-- The actual image of the inverse-image open is the original ambient open. -/
theorem image_preimage_of_mem_range (V : OpensInRange i) :
    i ''ᵁ i ⁻¹ᵁ V.obj = V.obj := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr V.property

/-- Any ambient presheaf has its original sections on these image-preimage opens. -/
def opensInRangePresheafIso (P : TopCat.Presheaf (ModuleCat.{u} k) X) :
    (opensInRangeInclusion i).op ⋙ P ≅
      (opensInRangePreimage i).op ⋙ i.opensFunctor.op ⋙ P :=
  NatIso.ofComponents
    (fun V ↦ P.mapIso (eqToIso (image_preimage_of_mem_range i V.unop)).op)
    (fun {_ _} _ ↦ by
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      rw [← P.map_comp, ← P.map_comp]
      exact congrArg (fun g ↦ P.map g) (Subsingleton.elim _ _))

/-- Natural coordinates on the actual form sheaf for every ambient open under the chart. -/
def underRangeOneFormsTrivialization
    (e : formsPresheaf k Y (i ≫ f) 1 ≅ functionsPresheaf k Y (i ≫ f)) :
    (opensInRangeInclusion i).op ⋙ (formsSheaf k X f 1).obj ≅
      (opensInRangeInclusion i).op ⋙ functionsPresheaf k X f :=
  opensInRangePresheafIso k i (formsSheaf k X f 1).obj ≪≫
    Functor.isoWhiskerLeft (opensInRangePreimage i).op
      (openImmersionOneFormsTrivialization k f i e) ≪≫
    (opensInRangePresheafIso k i (functionsPresheaf k X f)).symm

/-- The resulting additive equivalence with the actual ambient regular-function sections. -/
def underRangeOneFormsAddEquiv
    (e : formsPresheaf k Y (i ≫ f) 1 ≅ functionsPresheaf k Y (i ≫ f))
    (V : X.Opens) (hV : V ≤ i.opensRange) :
    (formsSheaf k X f 1).obj.obj (op V) ≃+ Γ(X, V) :=
  ((underRangeOneFormsTrivialization k f i e).app (op ⟨V, hV⟩)).toLinearEquiv.toAddEquiv

/-- Local trivializations commute with the original ambient restriction maps. -/
theorem underRangeOneFormsAddEquiv_naturality
    (e : formsPresheaf k Y (i ≫ f) 1 ≅ functionsPresheaf k Y (i ≫ f))
    {V W : X.Opens} (hV : V ≤ i.opensRange) (hW : W ≤ i.opensRange) (j : V ⟶ W)
    (s : (formsSheaf k X f 1).obj.obj (op W)) :
    underRangeOneFormsAddEquiv k f i e V hV ((formsSheaf k X f 1).obj.map j.op s) =
      X.presheaf.map j.op (underRangeOneFormsAddEquiv k f i e W hW s) := by
  exact congrArg (fun g ↦ g s) ((underRangeOneFormsTrivialization k f i e).hom.naturality
    (show op (⟨W, hW⟩ : OpensInRange i) ⟶ op (⟨V, hV⟩ : OpensInRange i) from
      (ObjectProperty.homMk j).op))

end HodgeConjecture.SchemeDeRham
