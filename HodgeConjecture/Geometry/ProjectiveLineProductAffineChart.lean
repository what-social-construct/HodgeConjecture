module

public import HodgeConjecture.Geometry.ProjectiveLineProduct
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

/-!
# An affine product chart of P¹ × P¹

The product of the two first affine charts is an open subscheme of the
scheme-theoretic product of projective lines. Mathlib's affine-pullback
isomorphism identifies that chart with the spectrum of the tensor product
`k[X] ⊗[k] k[X]`, retaining both coordinate projection equations.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The product of the two first affine charts over `Spec k`. -/
abbrev projectiveLineAffineProduct : Scheme.{u} :=
  pullback (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)

/-- Its natural map into the product of projective lines. -/
def projectiveLineAffineProductMap :
    projectiveLineAffineProduct k ⟶ projectiveLineProduct k :=
  pullback.map
    (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLineXChart k) (projectiveLineXChart k)
    (𝟙 (Spec (.of k))) (by simp) (by simp)

/-- The product of open affine charts is open in the product scheme. -/
instance projectiveLineAffineProductMap_isOpenImmersion :
    IsOpenImmersion (projectiveLineAffineProductMap k) := by
  unfold projectiveLineAffineProductMap
  infer_instance

@[simp] theorem projectiveLineAffineProductMap_fst :
    projectiveLineAffineProductMap k ≫ projectiveLineProductFst k =
      pullback.fst _ _ ≫ projectiveLineXChart k := by
  simp [projectiveLineAffineProductMap, projectiveLineProductFst]

@[simp] theorem projectiveLineAffineProductMap_snd :
    projectiveLineAffineProductMap k ≫ projectiveLineProductSnd k =
      pullback.snd _ _ ≫ projectiveLineXChart k := by
  simp [projectiveLineAffineProductMap, projectiveLineProductSnd]

/-- Affine fiber-product coordinates on the same open chart. -/
def projectiveLineAffineProductIso :
    projectiveLineAffineProduct k ≅
      Spec (.of (Polynomial k ⊗[k] Polynomial k)) :=
  pullbackSpecIso k (Polynomial k) (Polynomial k)

/-- The two-coordinate affine chart as a map from its tensor-product spectrum. -/
def projectiveLineProductAffineChart :
    Spec (.of (Polynomial k ⊗[k] Polynomial k)) ⟶ projectiveLineProduct k :=
  (projectiveLineAffineProductIso k).inv ≫ projectiveLineAffineProductMap k

/-- The tensor-product spectrum is an actual open chart of P¹ × P¹. -/
instance projectiveLineProductAffineChart_isOpenImmersion :
    IsOpenImmersion (projectiveLineProductAffineChart k) := by
  unfold projectiveLineProductAffineChart
  infer_instance

@[simp] theorem projectiveLineProductAffineChart_fst :
    projectiveLineProductAffineChart k ≫ projectiveLineProductFst k =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := Polynomial k)
          (B := Polynomial k))) ≫ projectiveLineXChart k := by
  rw [projectiveLineProductAffineChart, Category.assoc,
    projectiveLineAffineProductMap_fst, ← Category.assoc]
  exact congrArg (fun f : _ ⟶ Spec (.of (Polynomial k)) ↦
    f ≫ projectiveLineXChart k)
    (pullbackSpecIso_inv_fst k (Polynomial k) (Polynomial k))

@[simp] theorem projectiveLineProductAffineChart_snd :
    projectiveLineProductAffineChart k ≫ projectiveLineProductSnd k =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k).toRingHom) ≫
        projectiveLineXChart k := by
  rw [projectiveLineProductAffineChart, Category.assoc,
    projectiveLineAffineProductMap_snd, ← Category.assoc]
  exact congrArg (fun f : _ ⟶ Spec (.of (Polynomial k)) ↦
    f ≫ projectiveLineXChart k)
    (pullbackSpecIso_inv_snd k (Polynomial k) (Polynomial k))

end AlgebraicGeometry

end
