module

public import HodgeConjecture.SheafCohomology.Basis
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Injective sheaves of modules over a fixed ring

Sections of an injective sheaf of `k`-modules extend along every inclusion
of opens. The proof uses the actual subsheaf of sections locally zero
outside an open subset and injectivity, without a flatness hypothesis on
`k`. This supplies the coefficient category needed by scheme de Rham
complexes, whose differential is base-linear.

The supported-section proof adapts AxiomMath/Stacks at revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/Topology/Sheaves/Cohomology/CechAcyclicity/InjectiveSheavesRestrictOnto.lean`,
Apache-2.0. See `third_party/axiom-stacks/LICENSE`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace HodgeConjecture.SheafCohomology.Cohomology.LinearRestriction

variable {k : Type u} [CommRing k]

namespace Linear

variable {X : TopCat.{u}}

/-- Restricting twice in `(Opens X)ᵒᵖ` agrees with restricting along any single map with
the same source and target, because the hom-sets are subsingletons. -/
private lemma linearMap_comp_eq (M : TopCat.Presheaf (ModuleCat.{u} k) X)
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (h : V ⟶ Z) (s : M.obj V) :
    M.map g (M.map f s) = M.map h s :=
  (Functor.map_comp_apply M f g s).symm.trans
    (congrArg (fun k => M.map k s) (Subsingleton.elim _ _))

/-- Restricting twice along inclusions of opens is restricting along the composite. -/
private lemma restrict_comp (M : TopCat.Sheaf (ModuleCat.{u} k) X)
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (s : M.obj.obj (op C)) :
    M.obj.map (homOfLE hAB).op (M.obj.map (homOfLE hBC).op s) =
      M.obj.map (homOfLE (hAB.trans hBC)).op s :=
  linearMap_comp_eq M.obj _ _ _ s

/-- Sections over `V` locally zero outside `U` form a submodule. -/
public def supportedSubmodule (M : TopCat.Sheaf (ModuleCat.{u} k) X)
    (U V : Opens X) : Submodule k (M.obj.obj (op V)) where
  carrier := {s | ∀ x ∈ V, x ∉ U → ∃ (W : Opens X) (hWV : W ≤ V),
    x ∈ W ∧ M.obj.map (homOfLE hWV).op s = 0}
  zero_mem' := by
    intro x hx _
    exact ⟨V, le_rfl, hx, map_zero _⟩
  add_mem' := by
    intro s t hs ht x hx hxU
    obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
    obtain ⟨Z, hZ, hxZ, htZ⟩ := ht x hx hxU
    refine ⟨W ⊓ Z, inf_le_left.trans hW, ⟨hxW, hxZ⟩, ?_⟩
    rw [map_add, ← restrict_comp M inf_le_left hW,
      ← restrict_comp M inf_le_right hZ, hsW, htZ, map_zero, map_zero, add_zero]
  smul_mem' := by
    intro a s hs x hx hxU
    obtain ⟨W, hW, hxW, hsW⟩ := hs x hx hxU
    exact ⟨W, hW, hxW, by rw [map_smul, hsW, smul_zero]⟩

/-- Restriction carries sections locally zero outside `U` to sections locally zero
outside `U`. -/
public lemma supportedSubmodule_map (M : TopCat.Sheaf (ModuleCat.{u} k) X)
    (U : Opens X) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    {s : M.obj.obj V} (hs : s ∈ supportedSubmodule M U V.unop) :
    M.obj.map f s ∈ supportedSubmodule M U W.unop := by
  intro x hx hxU
  obtain ⟨Z, hZ, hxZ, hsZ⟩ := hs x (leOfHom f.unop hx) hxU
  refine ⟨Z ⊓ W.unop, inf_le_right, ⟨hxZ, hx⟩, ?_⟩
  rw [← Functor.map_comp_apply]
  have he : f ≫ (homOfLE (show Z ⊓ W.unop ≤ W.unop from inf_le_right)).op =
      (homOfLE hZ).op ≫ (homOfLE (show Z ⊓ W.unop ≤ Z from inf_le_left)).op :=
    Subsingleton.elim _ _
  rw [he, Functor.map_comp_apply, hsZ, map_zero]

/-- The subfunctor of sections locally zero outside `U`. -/
public def supportedSubfunctor (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    Subfunctor (M.obj ⋙ forget (ModuleCat k)) where
  obj V := {s | s ∈ supportedSubmodule M U V.unop}
  map f _ hs := supportedSubmodule_map M U f hs

/-- The presheaf of sections locally zero outside `U`. -/
public def supportedPresheaf (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    TopCat.Presheaf (ModuleCat.{u} k) X where
  obj V := ModuleCat.of k (supportedSubmodule M U V.unop)
  map f := ModuleCat.ofHom
    { toFun := fun s => ⟨M.obj.map f s.val, supportedSubmodule_map M U f s.property⟩
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  map_id V := by ext; simp
  map_comp f g := by ext; simp

/-- The sheaf of sections locally zero outside `U`. -/
public def supportedSheaf (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{u} k) X where
  obj := supportedPresheaf M U
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat k))
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf _ (supportedSubfunctor M U).toFunctor
    rw [(supportedSubfunctor M U).isSheaf_iff
      ((isSheaf_iff_isSheaf_of_type _ _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ M.property))]
    intro V s hs x hx hxU
    obtain ⟨W, f, hf, hxW⟩ := hs x hx
    obtain ⟨Z, hZ, hxZ, hsZ⟩ := hf x hxW hxU
    refine ⟨Z, hZ.trans (leOfHom f), hxZ, ?_⟩
    change M.obj.map (homOfLE hZ).op (M.obj.map f.op s) = 0 at hsZ
    exact (linearMap_comp_eq M.obj f.op (homOfLE hZ).op _ s).symm.trans hsZ

/-- The inclusion of the sheaf of sections locally zero outside `U` into `M`. -/
public def supportedSheafι (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    supportedSheaf M U ⟶ M :=
  ⟨{ app V := ModuleCat.ofHom (supportedSubmodule M U V.unop).subtype }⟩

/-- Separatedness tests equality on an open neighbourhood of each point. -/
private theorem eq_of_locally_eq {F : (Opens X)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (Opens.grothendieckTopology X) F) {V : Opens X} (s t : F.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V),
      x ∈ W ∧ F.map (homOfLE hWV).op s = F.map (homOfLE hWV).op t) : s = t := by
  choose W hW hxW heq using fun x : V => h x.1 x.2
  apply (hF.isSheafFor (.ofArrows W fun x => homOfLE (hW x)) ?_).isSeparatedFor.ext
  · rintro _ _ ⟨x⟩
    exact heq x
  · intro x hx
    exact ⟨W ⟨x, hx⟩, homOfLE (hW _), Sieve.ofArrows_mk _ _ _, hxW _⟩

/-- A section of an abelian sheaf that vanishes locally everywhere is zero. -/
private lemma eq_zero_of_locally_zero (M : TopCat.Sheaf (ModuleCat.{u} k) X)
    {V : Opens X} (s : M.obj.obj (op V))
    (hs : ∀ x ∈ V, ∃ (W : Opens X) (hWV : W ≤ V),
      x ∈ W ∧ M.obj.map (homOfLE hWV).op s = 0) : s = 0 :=
  eq_of_locally_eq (F := M.obj ⋙ forget (ModuleCat k))
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ M.property)) s 0 fun x hx => by
    obtain ⟨W, hWV, hxW, h⟩ := hs x hx
    exact ⟨W, hWV, hxW, h.trans (map_zero (M.obj.map (homOfLE hWV).op).hom).symm⟩

/-- The direct image along the inclusion of an open subset of the restriction of `M`. -/
public noncomputable abbrev directImageRestriction
    (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{u} k) X :=
  ((Over.star U).sheafPushforwardContinuous (ModuleCat k)
    (Opens.grothendieckTopology X) ((Opens.grothendieckTopology X).over U)).obj (M.over U)

/-- The canonical map from `M` to the direct image of its restriction to `U`. -/
public noncomputable def toDirectImageRestriction
    (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    M ⟶ directImageRestriction M U :=
  ⟨{ app V := M.obj.map prod.snd.op
     naturality V W f := by
       ext s
       exact (linearMap_comp_eq M.obj f (prod.snd : U ⨯ W.unop ⟶ W.unop).op
           (f ≫ (prod.snd : U ⨯ W.unop ⟶ W.unop).op) s).trans
         (linearMap_comp_eq M.obj (prod.snd : U ⨯ V.unop ⟶ V.unop).op
           (((Over.star U).map f.unop).left).op
           (f ≫ (prod.snd : U ⨯ W.unop ⟶ W.unop).op) s).symm }⟩

/-- The sheaf of sections locally zero outside `U` includes monomorphically into the direct
image of the restriction to `U`. -/
private lemma supportedSheaf_toDirectImageRestriction_mono
    (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : Opens X) :
    Mono (supportedSheafι M U ≫ toDirectImageRestriction M U) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ ?_
  intro V
  apply ConcreteCategory.mono_of_injective
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  apply Subtype.ext
  apply eq_zero_of_locally_zero M s.val
  intro x hx
  by_cases hxU : x ∈ U
  · let f : U ⊓ V.unop ⟶ U ⨯ V.unop :=
      prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right)
    refine ⟨U ⊓ V.unop, inf_le_right, ⟨hxU, hx⟩, ?_⟩
    change M.obj.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s.val = 0 at hs
    exact (linearMap_comp_eq M.obj (prod.snd : U ⨯ V.unop ⟶ V.unop).op f.op _ s.val).symm.trans
      (by rw [hs, map_zero])
  · exact s.property x hx hxU

end Linear

/-- An injective sheaf of modules over a fixed ring has surjective restriction maps. -/
public theorem injective_linear_restriction_surjective
    {X : TopCat.{u}} (I : TopCat.Sheaf (ModuleCat.{u} k) X) [Injective I]
    {U' U : Opens X} (h : U' ≤ U) :
    Function.Surjective (I.presheaf.map (homOfLE h).op) := by
  intro y
  let j := Linear.supportedSheafι I U' ≫ Linear.toDirectImageRestriction I U'
  have : Mono j := Linear.supportedSheaf_toDirectImageRestriction_mono I U'
  let k := Injective.factorThru (Linear.supportedSheafι I U') j
  let t : (Linear.directImageRestriction I U').obj.obj (op U) :=
    I.obj.map (prod.fst : U' ⨯ U ⟶ U').op y
  let y₀ : (Linear.supportedSheaf I U').obj.obj (op U') :=
    ⟨y, fun _ hx hxU => (hxU hx).elim⟩
  have ht : (Linear.directImageRestriction I U').obj.map (homOfLE h).op t =
      j.hom.app (op U') y₀ := by
    show I.obj.map (prod.map (𝟙 U') (homOfLE h)).op
      (I.obj.map (prod.fst : U' ⨯ U ⟶ U').op y) =
        I.obj.map (prod.snd : U' ⨯ U' ⟶ U').op y
    rw [← Functor.map_comp_apply]
    congr 2
  have hy := congrArg (fun f => f.hom.app (op U') y₀)
    (Injective.comp_factorThru (Linear.supportedSheafι I U') j)
  change k.hom.app (op U') (j.hom.app (op U') y₀) = y at hy
  refine ⟨k.hom.app (op U) t, ?_⟩
  show I.obj.map (homOfLE h).op (k.hom.app (op U) t) = y
  rw [← ConcreteCategory.comp_apply, ← k.hom.naturality, ConcreteCategory.comp_apply, ht]
  exact hy

end HodgeConjecture.SheafCohomology.Cohomology.LinearRestriction

end
