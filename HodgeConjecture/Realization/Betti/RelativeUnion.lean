module

public import HodgeConjecture.Realization.Betti.RelativeCochains
public import HodgeConjecture.Realization.Betti.SingularMayerVietoris

@[expose] public section

/-!
# Exact relative cochain excision inside a simplicial union

Restricting original cochains from A ∪ B to A identifies cochains
vanishing on B with cochains on A vanishing on A ∩ B. The inverse is
the actual compatible gluing of the first cochain with zero on B.
No topological excision or cohomology computation is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeUnion

open CategoryTheory HomologicalComplex Opposite Simplicial

variable {S : SSet.{0}} (A B : S.Subcomplex)

/-- The original B-simplices regarded as a subcomplex of the actual union. -/
abbrev unionBoundary := B.preimage (A ⊔ B).ι

/-- The original intersection regarded as a subcomplex of A. -/
abbrev localBoundary := B.preimage A.ι

/-- Original inclusion of A in the actual union. -/
def leftInclusion : A.toSSet ⟶ (A ⊔ B).toSSet :=
  SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)

theorem leftInclusion_maps_boundary :
    localBoundary A B ≤ (unionBoundary A B).preimage (leftInclusion A B) := by
  intro n σ hσ
  exact hσ

/-- The actual relative restriction from the union to its first piece. -/
def restriction : RelativeCochains.complex (unionBoundary A B) ⟶
    RelativeCochains.complex (localBoundary A B) :=
  RelativeCochains.pullback (leftInclusion A B) (leftInclusion_maps_boundary A B)

/-- A local relative cochain and zero on B have exactly zero original overlap difference. -/
theorem difference_pair_zero (n : ℕ) (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    SubcomplexCochains.coverDifferenceLinear A B n (φ.val, 0) = 0 := by
  funext σ
  change φ.val ⟨σ.val, σ.property.1⟩ - 0 = 0
  simpa only [sub_zero] using RelativeCochains.cochain_vanish (localBoundary A B) n φ
    ⟨⟨σ.val, σ.property.1⟩, σ.property.2⟩

/-- The original compatible-function gluing with zero on B. -/
def extensionFunction (n : ℕ) (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    SubcomplexCochains.Cochain (A ⊔ B).toSSet n :=
  SubcomplexCochains.glueFunction A B n (φ.val, 0)

theorem extensionFunction_restrictions (n : ℕ)
    (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    SubcomplexCochains.coverRestrictionLinear A B n (extensionFunction A B n φ) = (φ.val, 0) :=
  SubcomplexCochains.coverRestrictionLinear_glueFunction A B n _
    (difference_pair_zero A B n φ)

/-- Gluing with zero genuinely vanishes on the original B-subcomplex. -/
def extensionLinear (n : ℕ) : RelativeCochains.Cochain (localBoundary A B) n →ₗ[ℚ]
    RelativeCochains.Cochain (unionBoundary A B) n where
  toFun φ := ⟨extensionFunction A B n φ, by
    funext σ
    exact congrFun (congrArg Prod.snd (extensionFunction_restrictions A B n φ))
      ⟨σ.val.val, σ.property⟩⟩
  map_add' φ ψ := by
    apply Subtype.ext
    change extensionFunction A B n (φ + ψ) =
      extensionFunction A B n φ + extensionFunction A B n ψ
    apply SubcomplexCochains.coverRestrictionLinear_injective A B n
    rw [extensionFunction_restrictions, map_add, extensionFunction_restrictions,
      extensionFunction_restrictions]
    apply Prod.ext
    · exact Submodule.coe_add φ ψ
    · exact (add_zero (0 : SubcomplexCochains.Cochain B.toSSet n)).symm
  map_smul' q φ := by
    apply Subtype.ext
    change extensionFunction A B n (q • φ) = q • extensionFunction A B n φ
    apply SubcomplexCochains.coverRestrictionLinear_injective A B n
    rw [extensionFunction_restrictions, map_smul, extensionFunction_restrictions]
    apply Prod.ext
    · exact Submodule.coe_smul q φ
    · exact (smul_zero q : q • (0 : SubcomplexCochains.Cochain B.toSSet n) = 0).symm

@[simp]
theorem extensionLinear_val (n : ℕ) (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    (extensionLinear A B n φ).val = extensionFunction A B n φ := rfl

theorem extension_restriction (n : ℕ)
    (φ : RelativeCochains.Cochain (unionBoundary A B) n) :
    extensionLinear A B n ((restriction A B).f n φ) = φ := by
  apply Subtype.ext
  change extensionFunction A B n
    (RelativeCochains.pullbackLinear (RelativeUnion.leftInclusion A B)
      (leftInclusion_maps_boundary A B) n φ) = φ.val
  apply SubcomplexCochains.coverRestrictionLinear_injective A B n
  rw [extensionFunction_restrictions]
  apply Prod.ext
  · rfl
  · funext σ
    exact (RelativeCochains.cochain_vanish (unionBoundary A B) n φ
      ⟨⟨σ.val, Or.inr σ.property⟩, σ.property⟩).symm

theorem restriction_extension (n : ℕ)
    (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    (restriction A B).f n (extensionLinear A B n φ) = φ := by
  apply Subtype.ext
  change (fun σ ↦ extensionFunction A B n φ ⟨σ.val, Or.inl σ.property⟩) = φ.val
  exact congrArg Prod.fst (extensionFunction_restrictions A B n φ)

/-- Actual relative restriction is a degreewise linear equivalence. -/
def cochainEquiv (n : ℕ) : RelativeCochains.Cochain (unionBoundary A B) n ≃ₗ[ℚ]
    RelativeCochains.Cochain (localBoundary A B) n where
  toLinearMap := ((restriction A B).f n).hom
  invFun := extensionLinear A B n
  left_inv := extension_restriction A B n
  right_inv := restriction_extension A B n

/-- The exact relative union comparison, fixed by the original restriction cochain map. -/
def excisionIso : RelativeCochains.complex (unionBoundary A B) ≅
    RelativeCochains.complex (localBoundary A B) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (cochainEquiv A B n).toModuleIso)
    (fun i j _ ↦ (restriction A B).comm i j)

@[simp]
theorem excisionIso_hom : (excisionIso A B).hom = restriction A B := rfl

@[simp]
theorem excisionIso_inv_apply (n : ℕ) (φ : RelativeCochains.Cochain (localBoundary A B) n) :
    (excisionIso A B).inv.f n φ = extensionLinear A B n φ := rfl

/-- The nested intersection subtype retains exactly the original intersection simplices. -/
def intersectionIso : (localBoundary A B).toSSet ≅ (A ⊓ B).toSSet where
  hom :=
    { app n := ↾fun σ ↦ ⟨σ.val.val, ⟨σ.val.property, σ.property⟩⟩
      naturality _ _ _ := by ext σ; rfl }
  inv :=
    { app n := ↾fun σ ↦ ⟨⟨σ.val, σ.property.1⟩, σ.property.2⟩
      naturality _ _ _ := by ext σ; rfl }
  hom_inv_id := by ext n σ; rfl
  inv_hom_id := by ext n σ; rfl

/-- The nested B-subtype in the union retains exactly the original B-simplices. -/
def boundaryIso : (unionBoundary A B).toSSet ≅ B.toSSet where
  hom :=
    { app n := ↾fun σ ↦ ⟨σ.val.val, σ.property⟩
      naturality _ _ _ := by ext σ; rfl }
  inv :=
    { app n := ↾fun σ ↦ ⟨⟨σ.val, Or.inr σ.property⟩, σ.property⟩
      naturality _ _ _ := by ext σ; rfl }
  hom_inv_id := by ext n σ; rfl
  inv_hom_id := by ext n σ; rfl

end HodgeConjecture.RelativeUnion
