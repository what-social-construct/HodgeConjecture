module

public import HodgeConjecture.Realization.Betti.SubcomplexCochains

@[expose] public section

/-!
# Cohomology of the actual pair cochain complex

The componentwise cochain complex of two simplicial subcomplexes has
cohomology equal to the product of their actual cohomology modules.
The comparison is fixed by the original two projections and inclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CochainPair

open CategoryTheory HomologicalComplex SubcomplexCochains

variable {S : SSet.{0}} (A B : S.Subcomplex)

/-- Projection to cochains on the first piece. -/
def fst : pairComplex A B ⟶ complex (A : SSet) where
  f n := ModuleCat.ofHom (LinearMap.fst ℚ _ _)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    rw [pairComplex_d, complex_d]
    rfl

/-- Projection to cochains on the second piece. -/
def snd : pairComplex A B ⟶ complex (B : SSet) where
  f n := ModuleCat.ofHom (LinearMap.snd ℚ _ _)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    rw [pairComplex_d, complex_d]
    rfl

/-- Include first-piece cochains, with zero on the second piece. -/
def inl : complex (A : SSet) ⟶ pairComplex A B where
  f n := ModuleCat.ofHom (LinearMap.inl ℚ _ _)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    rw [pairComplex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (differential (A : SSet) i φ, differential (B : SSet) i 0) =
      (differential (A : SSet) i φ, 0)
    rw [map_zero]

/-- Include second-piece cochains, with zero on the first piece. -/
def inr : complex (B : SSet) ⟶ pairComplex A B where
  f n := ModuleCat.ofHom (LinearMap.inr ℚ _ _)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    rw [pairComplex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change (differential (A : SSet) i 0, differential (B : SSet) i φ) =
      (0, differential (B : SSet) i φ)
    rw [map_zero]

@[simp]
theorem inl_fst : inl A B ≫ fst A B = 𝟙 _ := by ext n φ; rfl

@[simp]
theorem inl_snd : inl A B ≫ snd A B = 0 := by ext n φ; rfl

@[simp]
theorem inr_fst : inr A B ≫ fst A B = 0 := by ext n φ; rfl

@[simp]
theorem inr_snd : inr A B ≫ snd A B = 𝟙 _ := by ext n φ; rfl

theorem total : fst A B ≫ inl A B + snd A B ≫ inr A B = 𝟙 _ := by
  ext n φ
  apply Prod.ext
  · change φ.1 + 0 = φ.1
    exact add_zero _
  · change 0 + φ.2 = φ.2
    exact zero_add _

/-- The actual projection-defined product equivalence in every cohomological degree. -/
def cohomologyEquiv (n : ℕ) :
    (pairComplex A B).homology n ≃ₗ[ℚ]
      ((complex (A : SSet)).homology n × (complex (B : SSet)).homology n) where
  toFun z := (homologyMap (fst A B) n z, homologyMap (snd A B) n z)
  invFun z := homologyMap (inl A B) n z.1 + homologyMap (inr A B) n z.2
  left_inv z := by
    have h : homologyMap (fst A B) n ≫ homologyMap (inl A B) n +
        homologyMap (snd A B) n ≫ homologyMap (inr A B) n = 𝟙 _ := by
      rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add, total, homologyMap_id]
    exact congrArg (fun f : (pairComplex A B).homology n ⟶ (pairComplex A B).homology n ↦ f z) h
  right_inv z := by
    have h₁ := congrArg (fun f : (complex (A : SSet)).homology n ⟶ _ ↦ f z.1)
      (homologyMap_comp (inl A B) (fst A B) n)
    have h₂ := congrArg (fun f : (complex (B : SSet)).homology n ⟶ _ ↦ f z.2)
      (homologyMap_comp (inr A B) (fst A B) n)
    have h₃ := congrArg (fun f : (complex (A : SSet)).homology n ⟶ _ ↦ f z.1)
      (homologyMap_comp (inl A B) (snd A B) n)
    have h₄ := congrArg (fun f : (complex (B : SSet)).homology n ⟶ _ ↦ f z.2)
      (homologyMap_comp (inr A B) (snd A B) n)
    simp only [inl_fst, inr_fst, inl_snd, inr_snd, homologyMap_id, homologyMap_zero,
      ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      ModuleCat.comp_apply] at h₁ h₂ h₃ h₄
    apply Prod.ext
    · simp only [map_add]
      rw [← h₁, ← h₂, add_zero]
    · simp only [map_add]
      rw [← h₃, ← h₄, zero_add]
  map_add' x y := by simp
  map_smul' a z := by simp

/-- Categorical form of the proved cohomology product comparison. -/
def cohomologyIso (n : ℕ) :
    (pairComplex A B).homology n ≅
      ModuleCat.of ℚ ((complex (A : SSet)).homology n × (complex (B : SSet)).homology n) :=
  (cohomologyEquiv A B n).toModuleIso

end HodgeConjecture.CochainPair
