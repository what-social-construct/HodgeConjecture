module

public import HodgeConjecture.Realization.HodgeFiltration
public import HodgeConjecture.LinearAlgebra.BlockGraphProjector
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.Hom.BoundedLattice

@[expose] public section

/-!
# Tate lines, products and the Hodge type of a graph projector

The Tate line `ℚ(-p)` has type `(p,p)` and weight `2p`. Its filtration
is constructed on its genuine tensor complexification. Products use the
native tensor/product equivalence, retaining the original rational product
carrier and canonical conjugation. Rational Hodge morphisms preserve the
complex filtration; they also preserve every recovered Hodge piece.

No cycle map, Chow correspondence, period comparison or geometric purity
theorem is imported by this module.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HodgeConjecture

namespace RationalComplexification

universe u v

variable (H : Type u) (K : Type v)
variable [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K]

/-- The native scalar-extension equivalence for the original rational product. -/
abbrev prodEquiv : Space (H × K) ≃ₗ[ℂ] Space H × Space K :=
  TensorProduct.prodRight ℚ ℂ ℂ H K

@[simp]
theorem prodEquiv_embedding (x : H × K) :
    prodEquiv H K (embedding (H × K) x) = (embedding H x.1, embedding K x.2) := rfl

/-- The native product coordinates intertwine the canonical rational real structures. -/
theorem prodEquiv_conjugation (z : Space (H × K)) :
    prodEquiv H K (conjugation (H × K) z) =
      (conjugation H (prodEquiv H K z).1, conjugation K (prodEquiv H K z).2) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add, Prod.snd_add] at hx hy ⊢
    rw [hx, hy]
    rfl

variable {H K}

/-- Product subspaces transported to the original tensor complexification. -/
def productSubmodule (U : Submodule ℂ (Space H)) (V : Submodule ℂ (Space K)) :
    Submodule ℂ (Space (H × K)) :=
  (U.prod V).comap (prodEquiv H K).toLinearMap

@[simp]
theorem mem_productSubmodule (U : Submodule ℂ (Space H)) (V : Submodule ℂ (Space K))
    (z : Space (H × K)) :
    z ∈ productSubmodule U V ↔ (prodEquiv H K z).1 ∈ U ∧ (prodEquiv H K z).2 ∈ V := Iff.rfl

@[simp]
theorem productSubmodule_top :
    productSubmodule (⊤ : Submodule ℂ (Space H)) (⊤ : Submodule ℂ (Space K)) = ⊤ := by
  simp [productSubmodule]

@[simp]
theorem productSubmodule_bot :
    productSubmodule (⊥ : Submodule ℂ (Space H)) (⊥ : Submodule ℂ (Space K)) = ⊥ := by
  simp [productSubmodule]

theorem productSubmodule_mono {U U' : Submodule ℂ (Space H)}
    {V V' : Submodule ℂ (Space K)} (hU : U ≤ U') (hV : V ≤ V') :
    productSubmodule U V ≤ productSubmodule U' V' :=
  Submodule.comap_mono (Submodule.prod_mono hU hV)

/-- Conjugation of a product is the product of the canonical conjugates. -/
theorem conjugate_productSubmodule (U : Submodule ℂ (Space H))
    (V : Submodule ℂ (Space K)) :
    conjugateSubmodule (H × K) (productSubmodule U V) =
      productSubmodule (conjugateSubmodule H U) (conjugateSubmodule K V) := by
  ext z
  simp only [mem_conjugateSubmodule, mem_productSubmodule, prodEquiv_conjugation]

/-- Complementary factors give complementary subspaces in the actual product tensor. -/
theorem isCompl_productSubmodule {U U' : Submodule ℂ (Space H)}
    {V V' : Submodule ℂ (Space K)} (hU : IsCompl U U') (hV : IsCompl V V') :
    IsCompl (productSubmodule U V) (productSubmodule U' V') := by
  have h : IsCompl (U.prod V) (U'.prod V') := IsCompl.of_eq
    (by rw [Submodule.prod_inf_prod, hU.inf_eq_bot, hV.inf_eq_bot, Submodule.prod_bot])
    (by rw [Submodule.prod_sup_prod, hU.sup_eq_top, hV.sup_eq_top, Submodule.prod_top])
  simpa only [productSubmodule, Submodule.comap_equiv_eq_map_symm] using
    Submodule.isCompl_map (prodEquiv H K).symm h

end RationalComplexification

namespace HodgeFiltration

variable {H K : Type*} [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K]

/-- The decreasing product filtration on the original rational product. -/
def product (F : ℤ → Submodule ℂ (RationalComplexification.Space H))
    (G : ℤ → Submodule ℂ (RationalComplexification.Space K)) (k : ℤ) :
    Submodule ℂ (RationalComplexification.Space (H × K)) :=
  RationalComplexification.productSubmodule (F k) (G k)

theorem product_antitone {F : ℤ → Submodule ℂ (RationalComplexification.Space H)}
    {G : ℤ → Submodule ℂ (RationalComplexification.Space K)}
    (hF : Antitone F) (hG : Antitone G) : Antitone (product F G) :=
  fun _ _ h ↦ RationalComplexification.productSubmodule_mono (hF h) (hG h)

/-- The cohomological Tate convention: `ℚ(-p)` has filtration cutoff `p`. -/
def tate (p k : ℤ) : Submodule ℂ (RationalComplexification.Space ℚ) :=
  if k ≤ p then ⊤ else ⊥

theorem tate_antitone (p : ℤ) : Antitone (tate p) := by
  intro k l hkl
  by_cases hl : l ≤ p
  · simp [tate, hl, hkl.trans hl]
  · simp [tate, hl]

end HodgeFiltration

namespace PureRationalHodgeStructure

variable {H K : Type*} [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K]
variable {weight : ℤ}

/-- A rational Hodge morphism is filtered after the original scalar extension. -/
def IsHodgeMorphism (S : PureRationalHodgeStructure H weight)
    (T : PureRationalHodgeStructure K weight) (f : H →ₗ[ℚ] K) : Prop :=
  HodgeFiltration.IsFilteredMap S.filtration T.filtration f

/-- Filtered rational maps preserve every type, using canonical conjugation. -/
theorem map_mem_piece {S : PureRationalHodgeStructure H weight}
    {T : PureRationalHodgeStructure K weight} {f : H →ₗ[ℚ] K}
    (hf : IsHodgeMorphism S T f) (p q : ℤ)
    {z : RationalComplexification.Space H} (hz : z ∈ S.piece p q) :
    RationalComplexification.map f z ∈ T.piece p q := by
  by_cases h : p + q = weight
  · simp only [piece, h, ite_true, Submodule.mem_inf,
      RationalComplexification.mem_conjugateSubmodule] at hz ⊢
    refine ⟨hf p hz.1, ?_⟩
    rw [RationalComplexification.conjugation_map]
    exact hf q hz.2
  · have hz0 : z = 0 := by simpa [piece, h] using hz
    simp [hz0, piece, h]

/-- The product of pure structures of the same weight, on the original rational product. -/
def product (S : PureRationalHodgeStructure H weight)
    (T : PureRationalHodgeStructure K weight) : PureRationalHodgeStructure (H × K) weight where
  finiteDimensional := by
    let := S.finiteDimensional
    let := T.finiteDimensional
    infer_instance
  filtration := HodgeFiltration.product S.filtration T.filtration
  antitone := HodgeFiltration.product_antitone S.antitone T.antitone
  exhaustive := by
    obtain ⟨i, hi⟩ := S.exhaustive
    obtain ⟨j, hj⟩ := T.exhaustive
    have hS := S.antitone (min_le_left i j)
    have hT := T.antitone (min_le_right i j)
    rw [hi] at hS
    rw [hj] at hT
    exact ⟨min i j, by simp [HodgeFiltration.product, top_unique hS, top_unique hT]⟩
  separated := by
    obtain ⟨i, hi⟩ := S.separated
    obtain ⟨j, hj⟩ := T.separated
    have hS := S.antitone (le_max_left i j)
    have hT := T.antitone (le_max_right i j)
    rw [hi] at hS
    rw [hj] at hT
    exact ⟨max i j, by simp [HodgeFiltration.product, bot_unique hS, bot_unique hT]⟩
  opposed := by
    intro k
    rw [HodgeFiltration.product, HodgeFiltration.product,
      RationalComplexification.conjugate_productSubmodule]
    exact RationalComplexification.isCompl_productSubmodule (S.opposed k) (T.opposed k)

/-- The rational Tate line of type `(p,p)` and weight `2p`. -/
def tate (p : ℤ) : PureRationalHodgeStructure ℚ (2 * p) where
  finiteDimensional := inferInstance
  filtration := HodgeFiltration.tate p
  antitone := HodgeFiltration.tate_antitone p
  exhaustive := ⟨p, by simp [HodgeFiltration.tate]⟩
  separated := ⟨p + 1, by simp [HodgeFiltration.tate]⟩
  opposed := by
    intro k
    by_cases hk : k ≤ p
    · have hk' : ¬ (2 * p + 1 - k ≤ p) := by omega
      simp only [HodgeFiltration.tate, ite_eq_left hk, ite_eq_right hk',
        RationalComplexification.conjugateSubmodule_bot]
      exact isCompl_top_bot
    · have hk' : 2 * p + 1 - k ≤ p := by omega
      simp only [HodgeFiltration.tate, ite_eq_right hk, ite_eq_left hk',
        RationalComplexification.conjugateSubmodule_top]
      exact isCompl_bot_top

/-- The genuine pure Tate-plus-cohomology object on the existing `ℚ × H` carrier. -/
abbrev tateBlock (p : ℤ) (S : PureRationalHodgeStructure H (2 * p)) :=
  (tate p).product S

end PureRationalHodgeStructure

namespace HodgeFiltration

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- Tensor extension of the original graph operator in native product coordinates. -/
theorem prodEquiv_graph_operator (α : H) (z : RationalComplexification.Space (ℚ × H)) :
    RationalComplexification.prodEquiv ℚ H
      (RationalComplexification.map (BlockGraphProjector.operator α) z) =
      ((RationalComplexification.prodEquiv ℚ H z).1,
        RationalComplexification.map (BlockGraphProjector.lineMap α)
          (RationalComplexification.prodEquiv ℚ H z).1) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add] at hx hy ⊢
    rw [hx, hy]
    rfl

/-- A map from the Tate line is filtered exactly at the independently defined Hodge target. -/
theorem lineMap_isFiltered_iff
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (hF : Antitone F)
    (p : ℤ) (α : H) :
    IsFilteredMap (tate p) F (BlockGraphProjector.lineMap α) ↔
      α ∈ rationalHodgeClasses F p := by
  rw [mem_rationalHodgeClasses_iff]
  constructor
  · intro hf
    have h := hf p (show RationalComplexification.embedding ℚ 1 ∈ tate p p by simp [tate])
    simpa [RationalComplexification.map_embedding, BlockGraphProjector.lineMap] using h
  · intro hα k z hz
    change RationalComplexification.map (BlockGraphProjector.lineMap α) z ∈ F k
    by_cases hk : k ≤ p
    · clear hz
      have hαk : RationalComplexification.embedding H α ∈ F k := hF hk hα
      induction z using TensorProduct.inductionOn with
      | tmul c t =>
        have ht : RationalComplexification.embedding H (t • α) ∈ F k := by
          rw [map_smul]
          exact ((F k).restrictScalars ℚ).smul_mem t hαk
        change c ⊗ₜ[ℚ] (t • α) ∈ F k
        simpa [RationalComplexification.embedding, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_comm] using
          (F k).smul_mem c ht
      | add x y hx hy =>
        simpa only [map_add] using (F k).add_mem hx hy
    · have hz0 : z = 0 := by simpa [tate, hk] using hz
      simp [hz0]

/-- Graph filtration preservation is exactly filtration preservation of its lower-left map. -/
theorem graph_isFiltered_iff_lineMap
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ) (α : H) :
    IsFilteredMap (product (tate p) F) (product (tate p) F)
      (BlockGraphProjector.operator α) ↔
        IsFilteredMap (tate p) F (BlockGraphProjector.lineMap α) := by
  constructor
  · intro hf k z hz
    have hmem : (RationalComplexification.prodEquiv ℚ H).symm (z, 0) ∈
        product (tate p) F k := by
      simpa [product] using And.intro hz (F k).zero_mem
    have h := hf k hmem
    change RationalComplexification.map (BlockGraphProjector.operator α)
      ((RationalComplexification.prodEquiv ℚ H).symm (z, 0)) ∈ product (tate p) F k at h
    rw [product, RationalComplexification.mem_productSubmodule, prodEquiv_graph_operator] at h
    simpa using h.2
  · intro hf k z hz
    change RationalComplexification.map (BlockGraphProjector.operator α) z ∈
      product (tate p) F k
    change (RationalComplexification.prodEquiv ℚ H z).1 ∈ tate p k ∧
      (RationalComplexification.prodEquiv ℚ H z).2 ∈ F k at hz
    rw [product, RationalComplexification.mem_productSubmodule, prodEquiv_graph_operator]
    exact ⟨hz.1, hf k hz.1⟩

/-- The graph criterion needs only the decreasing filtration, not cycle generation. -/
theorem graph_isFiltered_iff
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (hF : Antitone F)
    (p : ℤ) (α : H) :
    IsFilteredMap (product (tate p) F) (product (tate p) F)
      (BlockGraphProjector.operator α) ↔ α ∈ rationalHodgeClasses F p :=
  (graph_isFiltered_iff_lineMap F p α).trans (lineMap_isFiltered_iff F hF p α)

end HodgeFiltration

namespace PureRationalHodgeStructure

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- A rational class is type `(p,p)` exactly when its Tate-line map is a Hodge morphism. -/
theorem lineMap_isHodge_iff (p : ℤ) (S : PureRationalHodgeStructure H (2 * p)) (α : H) :
    IsHodgeMorphism (tate p) S (BlockGraphProjector.lineMap α) ↔
      α ∈ S.rationalHodgeClasses p :=
  HodgeFiltration.lineMap_isFiltered_iff S.filtration S.antitone p α

/-- The original rational graph operator is Hodge exactly for rational type `(p,p)` classes. -/
theorem graph_isHodge_iff (p : ℤ) (S : PureRationalHodgeStructure H (2 * p)) (α : H) :
    IsHodgeMorphism (tateBlock p S) (tateBlock p S) (BlockGraphProjector.operator α) ↔
      α ∈ S.rationalHodgeClasses p :=
  HodgeFiltration.graph_isFiltered_iff S.filtration S.antitone p α

end PureRationalHodgeStructure

end HodgeConjecture
