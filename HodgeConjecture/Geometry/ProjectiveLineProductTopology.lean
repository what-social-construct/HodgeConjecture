module

public import HodgeConjecture.Geometry.ProjectiveLineProductAffineChart
public import HodgeConjecture.Geometry.ProjectiveLineProductComplexPoints
public import HodgeConjecture.Geometry.AffineComplexPointsProduct
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints

/-!
# Four affine charts of the complex projective-line product

Each choice of the `x` or `y` chart on each projective-line factor gives
an open affine chart of the scheme product. The source is the spectrum of
the tensor product of the two polynomial algebras. These maps are the
geometric charts used to compare the analytic topology on the product's
complex points with the product topology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

namespace HodgeConjecture.ProjectiveLineProductComplexPoints

attribute [local instance] AffineComplexPoints.evaluationTopology

/-- Choose one of the two actual affine charts of the projective line. -/
def lineChart (i : Bool) : Spec (.of (Polynomial ℂ)) ⟶ projectiveLine ℂ :=
  if i then projectiveLineYChart ℂ else projectiveLineXChart ℂ

instance lineChart_isOpenImmersion (i : Bool) : IsOpenImmersion (lineChart i) := by
  cases i <;> dsimp [lineChart] <;> infer_instance

@[simp] theorem lineChart_comp_structureMorphism (i : Bool) :
    lineChart i ≫ lineBase = projectiveLineAffineStructureMorphism ℂ := by
  cases i <;> simp [lineChart]

/-- The chosen projective-line chart on algebra-valued affine points. -/
def linePointChart (i : Bool) :
    AffineComplexPoints.algebraPointSpace (Polynomial ℂ) →
      Scheme.ComplexPoints lineBase :=
  Scheme.ComplexPoints.map (lineChart i)
    (lineChart_comp_structureMorphism i) ∘
      (AffineComplexPoints.homeomorph (Polynomial ℂ)).symm

theorem continuous_linePointChart (i : Bool) : Continuous (linePointChart i) :=
  (Scheme.ComplexPoints.continuous_map (lineChart i)
    (lineChart_comp_structureMorphism i)).comp
      (AffineComplexPoints.homeomorph (Polynomial ℂ)).symm.continuous

@[simp] theorem linePointChart_false (a : AffineLineComplexPoints.Point) :
    linePointChart false a = ProjectiveLineComplexPoints.canonicalXChart a := rfl

@[simp] theorem linePointChart_true (a : AffineLineComplexPoints.Point) :
    linePointChart true a = ProjectiveLineComplexPoints.canonicalYChart a := rfl

/-- The product of the chosen affine charts, before affine fiber-product coordinates. -/
def productAffineMap (i j : Bool) :
    projectiveLineAffineProduct ℂ ⟶ projectiveLineProduct ℂ :=
  pullback.map
    (projectiveLineAffineStructureMorphism ℂ)
    (projectiveLineAffineStructureMorphism ℂ)
    lineBase lineBase
    (lineChart i) (lineChart j)
    (𝟙 (Spec (.of ℂ)))
    (by simp)
    (by simp)

instance productAffineMap_isOpenImmersion (i j : Bool) :
    IsOpenImmersion (productAffineMap i j) := by
  unfold productAffineMap
  infer_instance

@[simp] theorem productAffineMap_fst (i j : Bool) :
    productAffineMap i j ≫ projectiveLineProductFst ℂ =
      pullback.fst _ _ ≫ lineChart i := by
  simp [productAffineMap, projectiveLineProductFst]

@[simp] theorem productAffineMap_snd (i j : Bool) :
    productAffineMap i j ≫ projectiveLineProductSnd ℂ =
      pullback.snd _ _ ≫ lineChart j := by
  simp [productAffineMap, projectiveLineProductSnd]

@[simp] theorem productAffineMap_comp_structureMorphism (i j : Bool) :
    productAffineMap i j ≫ productBase =
      pullback.fst _ _ ≫ projectiveLineAffineStructureMorphism ℂ := by
  change productAffineMap i j ≫ (projectiveLineProductFst ℂ ≫ lineBase) = _
  rw [← Category.assoc, productAffineMap_fst, Category.assoc,
    lineChart_comp_structureMorphism]

/-- The chosen open product chart in tensor-product affine coordinates. -/
def productTensorChart (i j : Bool) :
    Spec (.of (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)) ⟶ projectiveLineProduct ℂ :=
  (projectiveLineAffineProductIso ℂ).inv ≫ productAffineMap i j

instance productTensorChart_isOpenImmersion (i j : Bool) :
    IsOpenImmersion (productTensorChart i j) := by
  unfold productTensorChart
  infer_instance

@[simp] theorem productTensorChart_fst (i j : Bool) :
    productTensorChart i j ≫ projectiveLineProductFst ℂ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := Polynomial ℂ)
          (B := Polynomial ℂ))) ≫ lineChart i := by
  rw [productTensorChart, Category.assoc, productAffineMap_fst, ← Category.assoc]
  exact congrArg (fun f : _ ⟶ Spec (.of (Polynomial ℂ)) ↦ f ≫ lineChart i)
    (pullbackSpecIso_inv_fst ℂ (Polynomial ℂ) (Polynomial ℂ))

@[simp] theorem productTensorChart_snd (i j : Bool) :
    productTensorChart i j ≫ projectiveLineProductSnd ℂ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          Polynomial ℂ →ₐ[ℂ] Polynomial ℂ ⊗[ℂ] Polynomial ℂ).toRingHom) ≫
        lineChart j := by
  rw [productTensorChart, Category.assoc, productAffineMap_snd, ← Category.assoc]
  exact congrArg (fun f : _ ⟶ Spec (.of (Polynomial ℂ)) ↦ f ≫ lineChart j)
    (pullbackSpecIso_inv_snd ℂ (Polynomial ℂ) (Polynomial ℂ))

@[simp] theorem productTensorChart_comp_structureMorphism (i j : Bool) :
    productTensorChart i j ≫ productBase =
      AffineComplexPoints.structureMorphism
        (Polynomial ℂ ⊗[ℂ] Polynomial ℂ) := by
  change productTensorChart i j ≫ (projectiveLineProductFst ℂ ≫ lineBase) = _
  rw [← Category.assoc, productTensorChart_fst, Category.assoc,
    lineChart_comp_structureMorphism]
  change Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := Polynomial ℂ)
      (B := Polynomial ℂ))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) =
    Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)))
  rw [← Spec.map_comp]
  rfl

/-- A pair of affine algebra-valued points enters the chosen open chart of
the actual scheme product. -/
def tensorPointChart (i j : Bool) :
    (AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ)) →
        Scheme.ComplexPoints productBase :=
  Scheme.ComplexPoints.map (productTensorChart i j)
    (productTensorChart_comp_structureMorphism i j) ∘
      (AffineComplexPoints.homeomorph
        (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)).symm ∘
      (AffineComplexPointsProduct.homeomorph (Polynomial ℂ) (Polynomial ℂ)).symm

/-- The four tensor-coordinate charts are continuous for the original analytic
topology on complex scheme points. -/
theorem continuous_tensorPointChart (i j : Bool) : Continuous (tensorPointChart i j) :=
  (Scheme.ComplexPoints.continuous_map (productTensorChart i j)
    (productTensorChart_comp_structureMorphism i j)).comp
      ((AffineComplexPoints.homeomorph
        (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)).symm.continuous.comp
        (AffineComplexPointsProduct.homeomorph
          (Polynomial ℂ) (Polynomial ℂ)).symm.continuous)

private theorem tensorAffinePoint_fst
    (pq : AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ)) :
    (AffineComplexPoints.ofAlgHom
      (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := Polynomial ℂ)
            (B := Polynomial ℂ))) =
      (AffineComplexPoints.ofAlgHom (Polynomial ℂ) pq.1).hom := by
  have h :
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq).comp
        (Algebra.TensorProduct.includeLeft : Polynomial ℂ →ₐ[ℂ]
          Polynomial ℂ ⊗[ℂ] Polynomial ℂ) = pq.1 := by
    exact congrArg Prod.fst
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).apply_symm_apply pq)
  have hr := congrArg (fun f : Polynomial ℂ →ₐ[ℂ] ℂ => f.toRingHom) h
  have hspec := congrArg (fun f : Polynomial ℂ →+* ℂ =>
    Spec.map (CommRingCat.ofHom f)) hr
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp]
  exact hspec

private theorem tensorAffinePoint_snd
    (pq : AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ)) :
    (AffineComplexPoints.ofAlgHom
      (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Polynomial ℂ →ₐ[ℂ]
            Polynomial ℂ ⊗[ℂ] Polynomial ℂ).toRingHom) =
      (AffineComplexPoints.ofAlgHom (Polynomial ℂ) pq.2).hom := by
  have h :
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq).comp
        (Algebra.TensorProduct.includeRight : Polynomial ℂ →ₐ[ℂ]
          Polynomial ℂ ⊗[ℂ] Polynomial ℂ) = pq.2 := by
    exact congrArg Prod.snd
      ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).apply_symm_apply pq)
  have hr := congrArg (fun f : Polynomial ℂ →ₐ[ℂ] ℂ => f.toRingHom) h
  have hspec := congrArg (fun f : Polynomial ℂ →+* ℂ =>
    Spec.map (CommRingCat.ofHom f)) hr
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp]
  exact hspec

/-- The tensor-coordinate chart agrees pointwise with the two original
projective-line charts under the categorical product equivalence. -/
theorem pointsEquiv_tensorPointChart (i j : Bool)
    (pq : AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ)) :
    pointsEquiv (tensorPointChart i j pq) =
      (linePointChart i pq.1, linePointChart j pq.2) := by
  apply Prod.ext
  · apply Scheme.ComplexPoints.ext
    change ((AffineComplexPoints.ofAlgHom
        (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)
        ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq)).hom ≫
        productTensorChart i j) ≫ projectiveLineProductFst ℂ =
      (AffineComplexPoints.ofAlgHom (Polynomial ℂ) pq.1).hom ≫ lineChart i
    rw [Category.assoc, productTensorChart_fst, ← Category.assoc]
    exact congrArg (fun f : Spec (.of ℂ) ⟶ Spec (.of (Polynomial ℂ)) =>
      f ≫ lineChart i) (tensorAffinePoint_fst pq)
  · apply Scheme.ComplexPoints.ext
    change ((AffineComplexPoints.ofAlgHom
        (Polynomial ℂ ⊗[ℂ] Polynomial ℂ)
        ((AffineComplexPointsProduct.pointEquiv (Polynomial ℂ) (Polynomial ℂ)).symm pq)).hom ≫
        productTensorChart i j) ≫ projectiveLineProductSnd ℂ =
      (AffineComplexPoints.ofAlgHom (Polynomial ℂ) pq.2).hom ≫ lineChart j
    rw [Category.assoc, productTensorChart_snd, ← Category.assoc]
    exact congrArg (fun f : Spec (.of ℂ) ⟶ Spec (.of (Polynomial ℂ)) =>
      f ≫ lineChart j) (tensorAffinePoint_snd pq)

theorem tensorPointChart_eq_pointsEquiv_symm (i j : Bool)
    (pq : AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ)) :
    tensorPointChart i j pq =
      pointsEquiv.symm (linePointChart i pq.1, linePointChart j pq.2) := by
  calc
    tensorPointChart i j pq = pointsEquiv.symm (pointsEquiv (tensorPointChart i j pq)) :=
      (pointsEquiv.symm_apply_apply _).symm
    _ = _ := congrArg pointsEquiv.symm (pointsEquiv_tensorPointChart i j pq)

/-- Inverse continuity on each of the four affine product charts. -/
theorem continuous_pointsEquiv_symm_chart (i j : Bool) :
    Continuous (fun pq : AffineComplexPoints.algebraPointSpace (Polynomial ℂ) ×
      AffineComplexPoints.algebraPointSpace (Polynomial ℂ) =>
        pointsEquiv.symm (linePointChart i pq.1, linePointChart j pq.2)) := by
  convert continuous_tensorPointChart i j using 1
  funext pq
  exact (tensorPointChart_eq_pointsEquiv_symm i j pq).symm

private abbrev AffinePoint := AffineLineComplexPoints.Point

private def chartDomainDistrib :
    (AffinePoint ⊕ AffinePoint) × (AffinePoint ⊕ AffinePoint) ≃ₜ
      ((AffinePoint × AffinePoint ⊕ AffinePoint × AffinePoint) ⊕
        (AffinePoint × AffinePoint ⊕ AffinePoint × AffinePoint)) :=
  Homeomorph.sumProdDistrib.trans
    (Homeomorph.sumCongr Homeomorph.prodSumDistrib Homeomorph.prodSumDistrib)

/-- The categorical equivalence from product scheme points to pairs of
projective-line points is also continuous in the inverse direction. -/
theorem continuous_pointsEquiv_symm : Continuous pointsEquiv.symm := by
  let q : AffinePoint ⊕ AffinePoint → Scheme.ComplexPoints lineBase :=
    Sum.elim ProjectiveLineComplexPoints.canonicalXChart
      ProjectiveLineComplexPoints.canonicalYChart
  have hq : IsOpenQuotientMap (Prod.map q q) :=
    ProjectiveLineComplexPoints.canonicalCharts_isOpenQuotientMap.prodMap
      ProjectiveLineComplexPoints.canonicalCharts_isOpenQuotientMap
  apply hq.continuous_comp_iff.mp
  let f00 : AffinePoint × AffinePoint → Scheme.ComplexPoints productBase :=
    fun pq => pointsEquiv.symm
      (ProjectiveLineComplexPoints.canonicalXChart pq.1,
        ProjectiveLineComplexPoints.canonicalXChart pq.2)
  let f01 : AffinePoint × AffinePoint → Scheme.ComplexPoints productBase :=
    fun pq => pointsEquiv.symm
      (ProjectiveLineComplexPoints.canonicalXChart pq.1,
        ProjectiveLineComplexPoints.canonicalYChart pq.2)
  let f10 : AffinePoint × AffinePoint → Scheme.ComplexPoints productBase :=
    fun pq => pointsEquiv.symm
      (ProjectiveLineComplexPoints.canonicalYChart pq.1,
        ProjectiveLineComplexPoints.canonicalXChart pq.2)
  let f11 : AffinePoint × AffinePoint → Scheme.ComplexPoints productBase :=
    fun pq => pointsEquiv.symm
      (ProjectiveLineComplexPoints.canonicalYChart pq.1,
        ProjectiveLineComplexPoints.canonicalYChart pq.2)
  have h00 : Continuous f00 := by
    convert continuous_pointsEquiv_symm_chart false false using 1
    funext pq
    rfl
  have h01 : Continuous f01 := by
    convert continuous_pointsEquiv_symm_chart false true using 1
    funext pq
    rfl
  have h10 : Continuous f10 := by
    convert continuous_pointsEquiv_symm_chart true false using 1
    funext pq
    rfl
  have h11 : Continuous f11 := by
    convert continuous_pointsEquiv_symm_chart true true using 1
    funext pq
    rfl
  let e := chartDomainDistrib
  have heq :
      (pointsEquiv.symm ∘ Prod.map q q) ∘ e.symm =
        Sum.elim (Sum.elim f00 f01) (Sum.elim f10 f11) := by
    funext x
    rcases x with ((⟨a, b⟩ | ⟨a, b⟩) | (⟨a, b⟩ | ⟨a, b⟩)) <;> rfl
  have hc : Continuous ((pointsEquiv.symm ∘ Prod.map q q) ∘ e.symm) := by
    rw [heq]
    exact (h00.sumElim h01).sumElim (h10.sumElim h11)
  convert hc.comp e.continuous using 1
  funext x
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]

/-- Complex points of the actual product scheme have the analytic product
topology. -/
def pointsHomeomorph : Scheme.ComplexPoints productBase ≃ₜ
    Scheme.ComplexPoints lineBase × Scheme.ComplexPoints lineBase where
  toEquiv := pointsEquiv
  continuous_toFun := continuous_pointsEquiv
  continuous_invFun := continuous_pointsEquiv_symm

end HodgeConjecture.ProjectiveLineProductComplexPoints

end
