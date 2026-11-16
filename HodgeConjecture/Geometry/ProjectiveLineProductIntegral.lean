module

public import HodgeConjecture.Cycles.ProjectiveLineProductAffineChowLocalization
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Integrality of the actual projective-line product

The product has a dense integral affine chart. Reducedness holds on the
four affine product charts obtained from the two original affine charts
of each projective-line factor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open HodgeConjecture.ProjectiveLineProductAffineChowLocalization

universe u

variable (k : Type u) [Field k]

private instance affineProduct_isReduced : IsReduced (projectiveLineAffineProduct k) := by
  haveI : _root_.IsDomain (Polynomial k ⊗[k] Polynomial k) :=
    HodgeConjecture.ProjectiveLineProductFiberCodimension.affineProduct_isDomain k
  exact isReduced_of_isOpenImmersion (projectiveLineAffineProductIso k).hom

/-- The four actual affine product charts prove reducedness of the product. -/
theorem projectiveLineProduct_isReduced : IsReduced (projectiveLineProduct k) := by
  let 𝒰 := Scheme.Pullback.openCoverOfLeftRight
    (projectiveLineOpenCover k) (projectiveLineOpenCover k)
    (projectiveLine k ↘ Spec (.of k)) (projectiveLine k ↘ Spec (.of k))
  have hchart : ∀ ij : 𝒰.I₀, IsReduced (𝒰.X ij) := by
    rintro ⟨i, j⟩
    change IsReduced (pullback
      ((projectiveLineOpenCover k).f i ≫ (projectiveLine k ↘ Spec (.of k)))
      ((projectiveLineOpenCover k).f j ≫ (projectiveLine k ↘ Spec (.of k))))
    have hi : (projectiveLineOpenCover k).f i ≫
        (projectiveLine k ↘ Spec (.of k)) =
          projectiveLineAffineStructureMorphism k :=
      (projectiveLineStructureMorphism k).2 i
    have hj : (projectiveLineOpenCover k).f j ≫
        (projectiveLine k ↘ Spec (.of k)) =
          projectiveLineAffineStructureMorphism k :=
      (projectiveLineStructureMorphism k).2 j
    rw [hi, hj]
    exact affineProduct_isReduced k
  letI : ∀ ij : 𝒰.I₀, IsReduced (𝒰.X ij) := hchart
  exact IsReduced.of_openCover (projectiveLineProduct k) 𝒰

/-- The first affine product chart is dense in the actual scheme product. -/
theorem denseRange_projectiveLineProductAffineChart :
    Dense (Set.range (projectiveLineProductAffineChart k).base) := by
  have hfst : Dense ((projectiveLineProductFst k).base ⁻¹'
      Set.range (projectiveLineXChart k).base) :=
    (denseRange_projectiveLineXChart k).preimage
      (projectiveLineProductFst k).isOpenMap
  have hsnd : Dense ((projectiveLineProductSnd k).base ⁻¹'
      Set.range (projectiveLineXChart k).base) :=
    (denseRange_projectiveLineXChart k).preimage
      (projectiveLineProductSnd k).isOpenMap
  rw [range_chart k]
  exact hfst.inter_of_isOpen_left hsnd
    ((projectiveLineProductFst k).continuous.isOpen_preimage
      (Set.range (projectiveLineXChart k).base)
      (projectiveLineXChart k).isOpenEmbedding.isOpen_range)

/-- The actual product scheme is integral over every field. -/
instance projectiveLineProduct_isIntegral : IsIntegral (projectiveLineProduct k) := by
  have hpre : IsPreirreducible
      (Set.range (projectiveLineProductAffineChart k).base) := by
    rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ
      (X := Spec (.of (Polynomial k ⊗[k] Polynomial k)))).image _ (by fun_prop)
  haveI : PreirreducibleSpace (projectiveLineProduct k) := by
    refine ⟨?_⟩
    rw [← (denseRange_projectiveLineProductAffineChart k).closure_eq]
    exact hpre.closure
  haveI : IrreducibleSpace (projectiveLineProduct k) := by
    let x : Spec (.of (Polynomial k ⊗[k] Polynomial k)) :=
      Classical.choice inferInstance
    exact { toNonempty := ⟨(projectiveLineProductAffineChart k).base x⟩ }
  haveI : IsReduced (projectiveLineProduct k) := projectiveLineProduct_isReduced k
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry

end
