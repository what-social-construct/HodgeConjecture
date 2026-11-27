module

public import HodgeConjecture.Realization.Betti.RelativeExcision
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

@[expose] public section

/-!
# Relative cochains on a union split by their original restrictions

A cochain on `A ∪ B` vanishing on `A ∩ B` restricts to relative cochains
on each piece. Its inverse is the original compatible-function gluing.
The two zero-overlap extensions and all product maps are literal cochain
maps, in every degree, before passing to native cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeUnionSplit

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial

variable {S : SSet.{0}} (A B : S.Subcomplex)

abbrev unionBoundary := (A ⊓ B).preimage (A ⊔ B).ι
abbrev leftBoundary := RelativeUnion.localBoundary A B
abbrev rightBoundary := RelativeUnion.localBoundary B A

def rightInclusion : B.toSSet ⟶ (A ⊔ B).toSSet :=
  SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)

theorem leftCondition :
    leftBoundary A B ≤ (unionBoundary A B).preimage (RelativeUnion.leftInclusion A B) := by
  intro n σ hσ
  exact ⟨σ.property, hσ⟩

theorem rightCondition :
    rightBoundary A B ≤ (unionBoundary A B).preimage (rightInclusion A B) := by
  intro n σ hσ
  exact ⟨hσ, σ.property⟩

/-- Original restriction to the first piece. -/
def restrictionLeft : RelativeCochains.complex (unionBoundary A B) ⟶
    RelativeCochains.complex (leftBoundary A B) :=
  RelativeCochains.pullback (RelativeUnion.leftInclusion A B) (leftCondition A B)

/-- Original restriction to the second piece. -/
def restrictionRight : RelativeCochains.complex (unionBoundary A B) ⟶
    RelativeCochains.complex (rightBoundary A B) :=
  RelativeCochains.pullback (rightInclusion A B) (rightCondition A B)

def restrictionPair (n : ℕ) : RelativeCochains.Cochain (unionBoundary A B) n →ₗ[ℚ]
    (RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :=
  ((restrictionLeft A B).f n).hom.prod ((restrictionRight A B).f n).hom

theorem pairDifference_zero (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :
    SubcomplexCochains.coverDifferenceLinear A B n (φ.1.val, φ.2.val) = 0 := by
  funext σ
  change φ.1.val ⟨σ.val, σ.property.1⟩ - φ.2.val ⟨σ.val, σ.property.2⟩ = 0
  rw [RelativeCochains.cochain_vanish (leftBoundary A B) n φ.1
      ⟨⟨σ.val, σ.property.1⟩, σ.property.2⟩,
    RelativeCochains.cochain_vanish (rightBoundary A B) n φ.2
      ⟨⟨σ.val, σ.property.2⟩, σ.property.1⟩, sub_self]

/-- The same original compatible-function gluing, on the same simplex representatives. -/
def glueFunction (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :
    SubcomplexCochains.Cochain (A ⊔ B).toSSet n :=
  SubcomplexCochains.glueFunction A B n (φ.1.val, φ.2.val)

theorem glueFunction_restrictions (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :
    SubcomplexCochains.coverRestrictionLinear A B n (glueFunction A B n φ) =
      (φ.1.val, φ.2.val) :=
  SubcomplexCochains.coverRestrictionLinear_glueFunction A B n _ (pairDifference_zero A B n φ)

def glueLinear (n : ℕ) :
    (RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) →ₗ[ℚ]
      RelativeCochains.Cochain (unionBoundary A B) n where
  toFun φ := ⟨glueFunction A B n φ, by
    funext σ
    have h := congrFun (congrArg Prod.fst (glueFunction_restrictions A B n φ))
      ⟨σ.val.val, σ.property.1⟩
    exact h.trans (RelativeCochains.cochain_vanish (leftBoundary A B) n φ.1
      ⟨⟨σ.val.val, σ.property.1⟩, σ.property.2⟩)⟩
  map_add' φ ψ := by
    apply Subtype.ext
    apply SubcomplexCochains.coverRestrictionLinear_injective A B n
    change SubcomplexCochains.coverRestrictionLinear A B n (glueFunction A B n (φ + ψ)) =
      SubcomplexCochains.coverRestrictionLinear A B n
        (glueFunction A B n φ + glueFunction A B n ψ)
    rw [glueFunction_restrictions, map_add, glueFunction_restrictions, glueFunction_restrictions]
    exact Prod.ext (Submodule.coe_add φ.1 ψ.1) (Submodule.coe_add φ.2 ψ.2)
  map_smul' q φ := by
    apply Subtype.ext
    apply SubcomplexCochains.coverRestrictionLinear_injective A B n
    change SubcomplexCochains.coverRestrictionLinear A B n (glueFunction A B n (q • φ)) =
      SubcomplexCochains.coverRestrictionLinear A B n (q • glueFunction A B n φ)
    rw [glueFunction_restrictions, map_smul, glueFunction_restrictions]
    exact Prod.ext (Submodule.coe_smul q φ.1) (Submodule.coe_smul q φ.2)

theorem glue_restriction (n : ℕ) (φ : RelativeCochains.Cochain (unionBoundary A B) n) :
    glueLinear A B n (restrictionPair A B n φ) = φ := by
  apply Subtype.ext
  apply SubcomplexCochains.coverRestrictionLinear_injective A B n
  change SubcomplexCochains.coverRestrictionLinear A B n
      (glueFunction A B n (restrictionPair A B n φ)) =
    SubcomplexCochains.coverRestrictionLinear A B n φ.val
  rw [glueFunction_restrictions]
  rfl

theorem restriction_glue (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :
    restrictionPair A B n (glueLinear A B n φ) = φ := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (glueFunction_restrictions A B n φ)
  · apply Subtype.ext
    exact congrArg Prod.snd (glueFunction_restrictions A B n φ)

/-- The representative-preserving relative cochain splitting. -/
def cochainEquiv (n : ℕ) : RelativeCochains.Cochain (unionBoundary A B) n ≃ₗ[ℚ]
    (RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) where
  toLinearMap := restrictionPair A B n
  invFun := glueLinear A B n
  left_inv := glue_restriction A B n
  right_inv := restriction_glue A B n

@[simp]
theorem cochainEquiv_symm_val (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n ×
      RelativeCochains.Cochain (rightBoundary A B) n) :
    ((cochainEquiv A B n).symm φ).val =
      SubcomplexCochains.glueFunction A B n (φ.1.val, φ.2.val) := rfl

theorem cochainEquiv_differential (n : ℕ)
    (φ : RelativeCochains.Cochain (unionBoundary A B) n) :
    cochainEquiv A B (n + 1) (RelativeCochains.differential (unionBoundary A B) n φ) =
      (RelativeCochains.differential (leftBoundary A B) n (cochainEquiv A B n φ).1,
        RelativeCochains.differential (rightBoundary A B) n (cochainEquiv A B n φ).2) := by
  have hleft := congrArg (fun f ↦ f.hom φ) ((restrictionLeft A B).comm n (n + 1))
  have hright := congrArg (fun f ↦ f.hom φ) ((restrictionRight A B).comm n (n + 1))
  simp only [RelativeCochains.complex_d, ModuleCat.hom_comp, LinearMap.comp_apply] at hleft hright
  exact Prod.ext hleft.symm hright.symm

def extensionLeftLinear (n : ℕ) : RelativeCochains.Cochain (leftBoundary A B) n →ₗ[ℚ]
    RelativeCochains.Cochain (unionBoundary A B) n :=
  (cochainEquiv A B n).symm.toLinearMap.comp (LinearMap.inl ℚ _ _)

def extensionRightLinear (n : ℕ) : RelativeCochains.Cochain (rightBoundary A B) n →ₗ[ℚ]
    RelativeCochains.Cochain (unionBoundary A B) n :=
  (cochainEquiv A B n).symm.toLinearMap.comp (LinearMap.inr ℚ _ _)

@[simp]
theorem cochainEquiv_extensionLeft (n : ℕ)
    (φ : RelativeCochains.Cochain (leftBoundary A B) n) :
    cochainEquiv A B n (extensionLeftLinear A B n φ) = (φ, 0) :=
  (cochainEquiv A B n).apply_symm_apply (φ, 0)

@[simp]
theorem cochainEquiv_extensionRight (n : ℕ)
    (φ : RelativeCochains.Cochain (rightBoundary A B) n) :
    cochainEquiv A B n (extensionRightLinear A B n φ) = (0, φ) :=
  (cochainEquiv A B n).apply_symm_apply (0, φ)

/-- Original gluing with zero on the second piece, as an actual cochain map. -/
def extensionLeft : RelativeCochains.complex (leftBoundary A B) ⟶
    RelativeCochains.complex (unionBoundary A B) where
  f n := ModuleCat.ofHom (extensionLeftLinear A B n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [RelativeCochains.complex_d, RelativeCochains.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (cochainEquiv A B (i + 1)).injective
    change cochainEquiv A B (i + 1)
        (RelativeCochains.differential (unionBoundary A B) i (extensionLeftLinear A B i φ)) =
      cochainEquiv A B (i + 1)
        (extensionLeftLinear A B (i + 1) (RelativeCochains.differential (leftBoundary A B) i φ))
    rw [cochainEquiv_differential, cochainEquiv_extensionLeft, cochainEquiv_extensionLeft]
    simp only [map_zero]

/-- Original gluing with zero on the first piece, as an actual cochain map. -/
def extensionRight : RelativeCochains.complex (rightBoundary A B) ⟶
    RelativeCochains.complex (unionBoundary A B) where
  f n := ModuleCat.ofHom (extensionRightLinear A B n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [RelativeCochains.complex_d, RelativeCochains.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply (cochainEquiv A B (i + 1)).injective
    change cochainEquiv A B (i + 1)
        (RelativeCochains.differential (unionBoundary A B) i (extensionRightLinear A B i φ)) =
      cochainEquiv A B (i + 1)
        (extensionRightLinear A B (i + 1) (RelativeCochains.differential (rightBoundary A B) i φ))
    rw [cochainEquiv_differential, cochainEquiv_extensionRight, cochainEquiv_extensionRight]
    simp only [map_zero]

@[simp]
theorem extensionLeft_restrictionLeft : extensionLeft A B ≫ restrictionLeft A B = 𝟙 _ := by
  ext n φ
  exact congrArg Prod.fst (cochainEquiv_extensionLeft A B n φ)

@[simp]
theorem extensionLeft_restrictionRight : extensionLeft A B ≫ restrictionRight A B = 0 := by
  ext n φ
  exact congrArg Prod.snd (cochainEquiv_extensionLeft A B n φ)

@[simp]
theorem extensionRight_restrictionLeft : extensionRight A B ≫ restrictionLeft A B = 0 := by
  ext n φ
  exact congrArg Prod.fst (cochainEquiv_extensionRight A B n φ)

@[simp]
theorem extensionRight_restrictionRight : extensionRight A B ≫ restrictionRight A B = 𝟙 _ := by
  ext n φ
  exact congrArg Prod.snd (cochainEquiv_extensionRight A B n φ)

theorem total : restrictionLeft A B ≫ extensionLeft A B +
    restrictionRight A B ≫ extensionRight A B = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (cochainEquiv A B n).injective
  change cochainEquiv A B n (extensionLeftLinear A B n ((restrictionLeft A B).f n φ) +
    extensionRightLinear A B n ((restrictionRight A B).f n φ)) = cochainEquiv A B n φ
  rw [map_add, cochainEquiv_extensionLeft, cochainEquiv_extensionRight]
  exact Prod.ext (add_zero _) (zero_add _)

/-- The actual relative cochain complex is the categorical biproduct of its two local kernels. -/
def complexIso : RelativeCochains.complex (unionBoundary A B) ≅
    RelativeCochains.complex (leftBoundary A B) ⊞
      RelativeCochains.complex (rightBoundary A B) where
  hom := biprod.lift (restrictionLeft A B) (restrictionRight A B)
  inv := biprod.desc (extensionLeft A B) (extensionRight A B)
  hom_inv_id := by rw [biprod.lift_desc, total]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
        biprod.inl_desc_assoc, biprod.inr_desc_assoc, extensionLeft_restrictionLeft,
        extensionLeft_restrictionRight, extensionRight_restrictionLeft,
        extensionRight_restrictionRight, biprod.inl_fst, biprod.inl_snd,
        biprod.inr_fst, biprod.inr_snd, Category.id_comp]

/-- Native cohomology splits by the original restrictions, in every degree. -/
def cohomologyEquiv (n : ℕ) : RelativeCochains.Cohomology (unionBoundary A B) n ≃ₗ[ℚ]
    (RelativeCochains.Cohomology (leftBoundary A B) n ×
      RelativeCochains.Cohomology (rightBoundary A B) n) where
  toFun z := (homologyMap (restrictionLeft A B) n z, homologyMap (restrictionRight A B) n z)
  invFun z := homologyMap (extensionLeft A B) n z.1 + homologyMap (extensionRight A B) n z.2
  left_inv z := by
    have h : homologyMap (restrictionLeft A B) n ≫ homologyMap (extensionLeft A B) n +
        homologyMap (restrictionRight A B) n ≫ homologyMap (extensionRight A B) n = 𝟙 _ := by
      rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add, total, homologyMap_id]
    exact congrArg (fun f : RelativeCochains.Cohomology (unionBoundary A B) n ⟶ _ ↦ f z) h
  right_inv z := by
    have h₁ := congrArg (fun f : RelativeCochains.Cohomology (leftBoundary A B) n ⟶ _ ↦ f z.1)
      (homologyMap_comp (extensionLeft A B) (restrictionLeft A B) n)
    have h₂ := congrArg (fun f : RelativeCochains.Cohomology (rightBoundary A B) n ⟶ _ ↦ f z.2)
      (homologyMap_comp (extensionRight A B) (restrictionLeft A B) n)
    have h₃ := congrArg (fun f : RelativeCochains.Cohomology (leftBoundary A B) n ⟶ _ ↦ f z.1)
      (homologyMap_comp (extensionLeft A B) (restrictionRight A B) n)
    have h₄ := congrArg (fun f : RelativeCochains.Cohomology (rightBoundary A B) n ⟶ _ ↦ f z.2)
      (homologyMap_comp (extensionRight A B) (restrictionRight A B) n)
    simp only [extensionLeft_restrictionLeft, extensionRight_restrictionLeft,
      extensionLeft_restrictionRight, extensionRight_restrictionRight,
      homologyMap_id, homologyMap_zero, ModuleCat.id_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply, ModuleCat.comp_apply] at h₁ h₂ h₃ h₄
    apply Prod.ext
    · simp only [map_add]
      rw [← h₁, ← h₂, add_zero]
    · simp only [map_add]
      rw [← h₃, ← h₄, zero_add]
  map_add' x y := by simp
  map_smul' q z := by simp

/-- Original relative restriction from the ambient simplicial set to its small union. -/
def toUnion : RelativeCochains.complex (A ⊓ B) ⟶
    RelativeCochains.complex (unionBoundary A B) :=
  RelativeCochains.pullback (A ⊔ B).ι le_rfl

/-- The nested small-union boundary has the same actual intersection simplices. -/
def boundaryIso : (unionBoundary A B).toSSet ≅ (A ⊓ B).toSSet where
  hom :=
    { app n := ↾fun σ ↦ ⟨σ.val.val, σ.property⟩
      naturality _ _ _ := by ext σ; rfl }
  inv :=
    { app n := ↾fun σ ↦ ⟨⟨σ.val, Or.inl σ.property.1⟩, σ.property⟩
      naturality _ _ _ := by ext σ; rfl }
  hom_inv_id := by ext n σ; rfl
  inv_hom_id := by ext n σ; rfl

theorem quotient_quasiIso :
    QuasiIso (SubcomplexCochains.pullback
      (RelativeCochains.subcomplexMap (A := unionBoundary A B) (B := A ⊓ B)
        (A ⊔ B).ι le_rfl)) := by
  change QuasiIso (SubcomplexCochains.pullback (boundaryIso A B).hom)
  have : IsIso (SubcomplexCochains.pullback (boundaryIso A B).hom) :=
    inferInstanceAs (IsIso (SingularMayerVietoris.pullbackIso (boundaryIso A B)).hom)
  infer_instance

theorem toUnion_quasiIso
    (h : QuasiIso (SubcomplexCochains.pullback (A ⊔ B).ι)) : QuasiIso (toUnion A B) :=
  ShortExactQuasiIso.left
    (RelativeCochains.shortComplexMap (A := unionBoundary A B) (B := A ⊓ B)
      (A ⊔ B).ι le_rfl)
    (RelativeCochains.shortComplex_shortExact (A ⊓ B))
    (RelativeCochains.shortComplex_shortExact (unionBoundary A B)) h (quotient_quasiIso A B)

end HodgeConjecture.RelativeUnionSplit

end
