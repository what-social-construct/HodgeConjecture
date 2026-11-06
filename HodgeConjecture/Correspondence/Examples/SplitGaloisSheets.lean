module

public import HodgeConjecture.Boundary.Sheets.GaloisSheets
public import HodgeConjecture.Correspondence.Examples.SplitProductGeometry
public import HodgeConjecture.Correspondence.GaloisCollision
public import Mathlib.Data.Complex.Basic

@[expose] public section

/-!
# Actual split torsors and homogeneous sheets

The regular split scheme `Spec (G → ℂ)` has its genuine left-translation
deck action over `Spec ℂ`. Its self-fiber-product is the actual coproduct
of the graphs of that action. The map to `Spec ((G ⧸ D) → ℂ)` is induced
by the left-coset quotient and is equivariant for the left action of `G`.
No normality of `D` is required.

This is a finite split torsor over the complex point. It is disconnected
for nontrivial `G`; no field normal closure is constructed.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SplitPointGeometry

noncomputable section

namespace SplitGaloisSheets

variable (G : Type) [Group G]

def translationEquiv (S : Type) [MulAction G S] (a : G) : S ≃ S where
  toFun s := a • s
  invFun s := a⁻¹ • s
  left_inv s := by simp [smul_smul]
  right_inv s := by simp [smul_smul]

/-- Any action on split components gives actual scheme automorphisms over the field. -/
def deckAction (S : Type) [MulAction G S] :
    SchemeCorrespondence.FiniteDeckAction (toBase ℂ S) G where
  toFun a := CategoryTheory.Aut.of <| Over.isoMk (isoOfEquiv ℂ (translationEquiv G S a)) (by
    exact mapOfFunction_toBase ℂ _)
  map_one' := by
    apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    change mapOfFunction ℂ (fun s : S ↦ (1 : G) • s) = 𝟙 _
    have he : (fun s : S ↦ (1 : G) • s) = id := by
      funext s
      exact one_smul G s
    rw [he]
    exact mapOfFunction_id ℂ (I := S)
  map_mul' := by
    intro a b
    apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    change mapOfFunction ℂ (fun s : S ↦ (a * b) • s) =
      mapOfFunction ℂ (fun s : S ↦ b • s) ≫
        mapOfFunction ℂ (fun s : S ↦ a • s)
    simp [Function.comp_def, mul_smul]

@[simp]
theorem deckAction_toSchemeHom (S : Type) [MulAction G S] (a : G) :
    (deckAction G S a).toSchemeHom = mapOfFunction ℂ (fun s : S ↦ a • s) :=
  rfl

/-- Left translations of the regular split cover. -/
abbrev regularAction := deckAction G G

/-- The induced left action on the actual homogeneous split scheme. -/
abbrev sheetAction (D : Subgroup G) := deckAction G (G ⧸ D)

/-- The genuine finite split scheme morphism induced by the coset quotient. -/
def quotientMap (D : Subgroup G) : scheme ℂ G ⟶ scheme ℂ (G ⧸ D) :=
  mapOfFunction ℂ (fun g : G ↦ (g : G ⧸ D))

@[simp, reassoc]
theorem quotientMap_toBase (D : Subgroup G) :
    quotientMap G D ≫ toBase ℂ (G ⧸ D) = toBase ℂ G := by
  simp [quotientMap]

@[simp, reassoc]
theorem pointInclusion_quotientMap (D : Subgroup G) (g : G) :
    pointInclusion ℂ G g ≫ quotientMap G D =
      pointInclusion ℂ (G ⧸ D) (g : G ⧸ D) := by
  simp [quotientMap]

/-- The quotient is equivariant for left translation; this is not a claim
that all left translations are deck transformations over the quotient. -/
@[reassoc]
theorem quotientMap_equivariant (D : Subgroup G) (a : G) :
    (regularAction G a).toSchemeHom ≫ quotientMap G D =
      quotientMap G D ≫ (sheetAction G D a).toSchemeHom := by
  simp only [regularAction, sheetAction, deckAction_toSchemeHom,
    quotientMap, mapOfFunction_comp]
  rfl

variable [Finite G]

instance quotientMap_isFinite (D : Subgroup G) : IsFinite (quotientMap G D) := by
  unfold quotientMap
  infer_instance

instance quotientMap_isEtale (D : Subgroup G) : Etale (quotientMap G D) := by
  unfold quotientMap
  infer_instance

instance quotientMap_isProper (D : Subgroup G) : IsProper (quotientMap G D) :=
  inferInstance

/-- Every homogeneous component is attained by an actual point of the cover. -/
instance quotientMap_surjective (D : Subgroup G) : Surjective (quotientMap G D) := by
  constructor
  intro y
  obtain ⟨s, rfl⟩ := (labelEquivScheme ℂ (G ⧸ D)).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  exact ⟨labelEquivScheme ℂ G g, mapOfFunction_label ℂ _ g⟩

/-- The regular split cover is surjective, with the identity component as a section. -/
instance regularToBase_surjective : Surjective (toBase ℂ G) := by
  have : Surjective (pointInclusion ℂ G 1 ≫ toBase ℂ G) := by
    rw [pointInclusion_toBase]
    infer_instance
  exact Surjective.of_comp (pointInclusion ℂ G 1) (toBase ℂ G)

/-- The regular action is free and transitive on the actual scheme points. -/
theorem regularAction_existsUnique (x y : scheme ℂ G) :
    ∃! a : G, (regularAction G a).toSchemeHom.base x = y := by
  obtain ⟨g, rfl⟩ := (labelEquivScheme ℂ G).surjective x
  obtain ⟨h, rfl⟩ := (labelEquivScheme ℂ G).surjective y
  refine ⟨h * g⁻¹, ?_, ?_⟩
  · change (mapOfFunction ℂ (fun x : G ↦ (h * g⁻¹) * x)).base
      (labelEquivScheme ℂ G g) = labelEquivScheme ℂ G h
    rw [mapOfFunction_label]
    simp
  · intro a ha
    change labelEquivScheme ℂ G (a * g) = labelEquivScheme ℂ G h at ha
    exact eq_mul_inv_iff_mul_eq.mpr ((labelEquivScheme ℂ G).injective ha)

def curryRingEquiv : ((G × G) → ℂ) ≃+* (G → G → ℂ) where
  toFun f a x := f (a, x)
  invFun f p := f p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The actual indexed coproduct of regular split schemes, with pair labels. -/
def indexedSchemeIso :
    (∐ fun _ : G ↦ scheme ℂ G) ≅ scheme ℂ (G × G) :=
  asIso (sigmaSpec (fun _ : G ↦ CommRingCat.of (G → ℂ))) ≪≫
    Scheme.Spec.mapIso (curryRingEquiv G).toCommRingCatIso.op

omit [Group G] in
@[simp, reassoc]
theorem indexedSchemeIso_ι (a : G) :
    Sigma.ι (fun _ : G ↦ scheme ℂ G) a ≫ (indexedSchemeIso G).hom =
      mapOfFunction ℂ (fun x : G ↦ (a, x)) := by
  change Sigma.ι _ a ≫ sigmaSpec (fun _ : G ↦ CommRingCat.of (G → ℂ)) ≫
    Spec.map (CommRingCat.ofHom (curryRingEquiv G).toRingHom) = _
  rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
  rfl

/-- The regular-action torsor coordinates `(a,x) ↦ (x,a*x)`. -/
def regularPairEquiv : G × G ≃ G × G where
  toFun p := (p.2, p.1 * p.2)
  invFun p := (p.2 * p.1⁻¹, p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The split regular action gives an isomorphism onto the actual self-product. -/
def regularTorsorIso :
    scheme ℂ (G × G) ≅ pullback (toBase ℂ G) (toBase ℂ G) :=
  isoOfEquiv ℂ (regularPairEquiv G) ≪≫ productIso ℂ G G

@[simp, reassoc]
theorem regularTorsorIso_hom_fst :
    (regularTorsorIso G).hom ≫ pullback.fst _ _ =
      mapOfFunction ℂ (Prod.snd : G × G → G) := by
  simp [regularTorsorIso, isoOfEquiv, regularPairEquiv, Function.comp_def]

@[simp, reassoc]
theorem regularTorsorIso_hom_snd :
    (regularTorsorIso G).hom ≫ pullback.snd _ _ =
      mapOfFunction ℂ (fun p : G × G ↦ p.1 * p.2) := by
  simp [regularTorsorIso, isoOfEquiv, regularPairEquiv, Function.comp_def]

/-- Actual graph-sheet decomposition of the finite split regular torsor. -/
def regularCollisionDecomposition :
    GaloisCollisionDecomposition G (toBase ℂ G) where
  action := regularAction G
  collisionIso := indexedSchemeIso G ≪≫ regularTorsorIso G
  collisionIso_hom_fst a := by
    change Sigma.ι _ a ≫ (indexedSchemeIso G).hom ≫
      (regularTorsorIso G).hom ≫ pullback.fst _ _ = 𝟙 _
    simp only [regularTorsorIso_hom_fst, indexedSchemeIso_ι_assoc,
      mapOfFunction_comp]
    exact mapOfFunction_id ℂ
  collisionIso_hom_snd a := by
    change Sigma.ι _ a ≫ (indexedSchemeIso G).hom ≫
      (regularTorsorIso G).hom ≫ pullback.snd _ _ = _
    simp only [regularTorsorIso_hom_snd, indexedSchemeIso_ι_assoc,
      mapOfFunction_comp, regularAction, deckAction_toSchemeHom]
    rfl

end SplitGaloisSheets

end

end HodgeConjecture
