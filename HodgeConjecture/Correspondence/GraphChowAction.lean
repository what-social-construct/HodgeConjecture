module

public import HodgeConjecture.Correspondence.GraphChow
public import HodgeConjecture.Correspondence.GraphCycleComposition
public import HodgeConjecture.Cycles.RationalChowOpenRestriction

@[expose] public section

/-!
# Geometric graph actions on the actual graded Chow quotient

Changing the first coordinate by a deck transformation gives right graph
composition. Changing the second coordinate by its inverse gives left
graph composition. Both operations are actual open pullbacks through
scheme isomorphisms. Their descent uses preservation of the existing
principal relations, rather than an assumed ambient intersection product.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u

variable (k : Type u) [Field k] {X S : Scheme.{u}}
variable (p : X ⟶ S) (b : S ⟶ Spec (CommRingCat.of k))

private theorem dimensionFunction_ext {Y : Scheme.{u}}
    (δ ε : DimensionFunction Y) (h : ∀ x, δ x = ε x) : δ = ε := by
  cases δ
  cases ε
  congr 1
  exact funext h

private theorem rationalPrincipalRelations_transport {Y : Scheme.{u}}
    [IsNoetherian Y] {δ ε : DimensionFunction Y} {n : ℤ}
    (hδε : δ = ε) (c : cyclesOfDegree ℚ δ n) (d : cyclesOfDegree ℚ ε n)
    (hcd : c.val = d.val) (hc : c ∈ rationalPrincipalRelations δ n) :
    d ∈ rationalPrincipalRelations ε n := by
  subst ε
  have h : c = d := Subtype.ext hcd
  exact h ▸ hc

/-- The canonical grading is invariant under an actual open self-map over
the given field structure. -/
theorem graphPairDimensionFunction_comap
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) :
    (graphPairDimensionFunction k p b).comapOpenImmersion f =
      graphPairDimensionFunction k p b := by
  apply dimensionFunction_ext
  intro x
  change graphPairDimensionFunction k p b (f.base x) =
    graphPairDimensionFunction k p b x
  have h := DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion
    k (graphPairStructure k p b) f x
  simpa only [graphPairDimensionFunction, hf] using h.symm

/-- The original open restriction, on the existing homogeneous submodule. -/
def gradedGraphPairPullback
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ) :
    Module.End ℚ (cyclesOfDegree ℚ (graphPairDimensionFunction k p b) n) where
  toFun c := ⟨openRestriction ℚ f c.val, by
    simpa only [graphPairDimensionFunction_comap k p b f hf] using
      openRestriction_mem_cyclesOfDegree ℚ (graphPairDimensionFunction k p b)
        f n c.val c.property⟩
  map_add' c d := Subtype.ext ((openRestriction ℚ f).map_add c.val d.val)
  map_smul' q c := Subtype.ext ((openRestriction ℚ f).map_smul q c.val)

@[simp]
theorem gradedGraphPairPullback_val
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ)
    (c : cyclesOfDegree ℚ (graphPairDimensionFunction k p b) n) :
    (gradedGraphPairPullback k p b f hf n c).val = openRestriction ℚ f c.val := rfl

/-- Actual principal relations are preserved by this same geometric map. -/
theorem rationalPrincipalRelations_le_comap_graphPairPullback
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ) :
    rationalPrincipalRelations (graphPairDimensionFunction k p b) n ≤
      (rationalPrincipalRelations (graphPairDimensionFunction k p b) n).comap
        (gradedGraphPairPullback k p b f hf n) := by
  intro c hc
  have h := rationalPrincipalRelations_le_comap_openRestriction
    (graphPairDimensionFunction k p b) f n hc
  change gradedOpenRestriction ℚ (graphPairDimensionFunction k p b) f n c ∈
    rationalPrincipalRelations
      ((graphPairDimensionFunction k p b).comapOpenImmersion f) n at h
  exact rationalPrincipalRelations_transport
    (graphPairDimensionFunction_comap k p b f hf) _ _ rfl h

/-- Descent on the original rational homogeneous-cycle quotient. -/
def graphPairChowPullback
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ) :
    Module.End ℚ (RationalChowGroup (graphPairDimensionFunction k p b) n) :=
  (rationalPrincipalRelations (graphPairDimensionFunction k p b) n).mapQ
    (rationalPrincipalRelations (graphPairDimensionFunction k p b) n)
    (gradedGraphPairPullback k p b f hf n)
    (rationalPrincipalRelations_le_comap_graphPairPullback k p b f hf n)

@[simp]
theorem graphPairChowPullback_classMap
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f : pullback p p ⟶ pullback p p) [IsOpenImmersion f]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ)
    (c : cyclesOfDegree ℚ (graphPairDimensionFunction k p b) n) :
    graphPairChowPullback k p b f hf n
        (rationalClassMap (graphPairDimensionFunction k p b) n c) =
      rationalClassMap (graphPairDimensionFunction k p b) n
        (gradedGraphPairPullback k p b f hf n c) := rfl

theorem graphPairChowPullback_comp
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f g : pullback p p ⟶ pullback p p) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b)
    (hg : g ≫ graphPairStructure k p b = graphPairStructure k p b) (n : ℤ) :
    (graphPairChowPullback k p b f hf n).comp
        (graphPairChowPullback k p b g hg n) =
      graphPairChowPullback k p b (f ≫ g)
        (by rw [Category.assoc, hg, hf]) n := by
  apply (rationalPrincipalRelations (graphPairDimensionFunction k p b) n).quot_hom_ext
  intro c
  change rationalClassMap _ n
    (gradedGraphPairPullback k p b f hf n
      (gradedGraphPairPullback k p b g hg n c)) =
    rationalClassMap _ n (gradedGraphPairPullback k p b (f ≫ g) _ n c)
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (openRestriction_comp g ℚ f) c.val

theorem graphPairChowPullback_congr
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (f g : pullback p p ⟶ pullback p p) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : f ≫ graphPairStructure k p b = graphPairStructure k p b)
    (hg : g ≫ graphPairStructure k p b = graphPairStructure k p b)
    (n : ℤ) (hfg : f = g) :
    graphPairChowPullback k p b f hf n = graphPairChowPullback k p b g hg n := by
  subst g
  rfl

@[reassoc (attr := simp)]
theorem graphSlicePairMap_structure (τ : DeckTransformation p) :
    graphSlicePairMap p τ ≫ graphPairStructure k p b = graphPairStructure k p b := by
  simp [graphPairStructure]

@[simp]
theorem graphSlicePairMap_one : graphSlicePairMap p 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [graphSlicePairMap_fst, Category.id_comp]
    have h : (1 : DeckTransformation p).toSchemeHom = 𝟙 X := by
      change (1 : DeckTransformation p).hom.left = _
      simp only [show (1 : DeckTransformation p).hom = 𝟙 (Over.mk p) from rfl,
        Over.id_left]
      rfl
    rw [h, Category.comp_id]
  · simp

theorem graphSlicePairMap_mul (σ τ : DeckTransformation p) :
    graphSlicePairMap p (σ * τ) = graphSlicePairMap p τ ≫ graphSlicePairMap p σ := by
  apply pullback.hom_ext <;> simp [Category.assoc]
  rfl

/-- Actual right graph composition on every degree of the canonical Chow group. -/
def graphChowRightAction
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (τ : DeckTransformation p) :
    Module.End ℚ (RationalChowGroup (graphPairDimensionFunction k p b) n) :=
  graphPairChowPullback k p b (graphSlicePairMap p τ)
    (graphSlicePairMap_structure k p b τ) n

@[simp]
theorem graphChowRightAction_one
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    graphChowRightAction k p b n 1 = LinearMap.id := by
  apply (rationalPrincipalRelations (graphPairDimensionFunction k p b) n).quot_hom_ext
  intro c
  change rationalClassMap _ n (gradedGraphPairPullback k p b _ _ n c) =
    rationalClassMap _ n c
  congr 1
  apply Subtype.ext
  simp [graphSlicePairMap_one]

/-- Right composition reverses the endomorphism multiplication order. -/
theorem graphChowRightAction_mul
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (σ τ : DeckTransformation p) :
    graphChowRightAction k p b n (σ * τ) =
      (graphChowRightAction k p b n τ).comp (graphChowRightAction k p b n σ) := by
  unfold graphChowRightAction
  rw [graphPairChowPullback_comp]
  apply graphPairChowPullback_congr
  exact graphSlicePairMap_mul p σ τ

/-- Change the output coordinate by the inverse deck transformation. -/
def graphLeftPairMap (τ : DeckTransformation p) : pullback p p ⟶ pullback p p :=
  pullback.map p p p p (𝟙 X) τ⁻¹.toSchemeHom (𝟙 S) (by simp) (by simp)

instance graphLeftPairMap_isIso (τ : DeckTransformation p) :
    IsIso (graphLeftPairMap p τ) := by
  unfold graphLeftPairMap
  infer_instance

@[reassoc (attr := simp)]
theorem graphLeftPairMap_fst (τ : DeckTransformation p) :
    graphLeftPairMap p τ ≫ pullback.fst p p = pullback.fst p p := by
  simp [graphLeftPairMap]

@[reassoc (attr := simp)]
theorem graphLeftPairMap_snd (τ : DeckTransformation p) :
    graphLeftPairMap p τ ≫ pullback.snd p p =
      pullback.snd p p ≫ τ⁻¹.toSchemeHom := by
  simp [graphLeftPairMap]

@[reassoc (attr := simp)]
theorem graphLeftPairMap_structure (τ : DeckTransformation p) :
    graphLeftPairMap p τ ≫ graphPairStructure k p b = graphPairStructure k p b := by
  simp [graphPairStructure]

@[simp]
theorem graphLeftPairMap_one : graphLeftPairMap p 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [graphLeftPairMap_snd, inv_one, Category.id_comp]
    have h : (1 : DeckTransformation p).toSchemeHom = 𝟙 X := by
      change (1 : DeckTransformation p).hom.left = _
      simp only [show (1 : DeckTransformation p).hom = 𝟙 (Over.mk p) from rfl,
        Over.id_left]
      rfl
    rw [h, Category.comp_id]

theorem graphLeftPairMap_mul (σ τ : DeckTransformation p) :
    graphLeftPairMap p (σ * τ) = graphLeftPairMap p σ ≫ graphLeftPairMap p τ := by
  apply pullback.hom_ext
  · simp
  · simp only [graphLeftPairMap_snd, Category.assoc, graphLeftPairMap_snd_assoc,
      mul_inv_rev]
    rfl

@[reassoc (attr := simp)]
theorem graphMorphism_graphLeftPairMap (σ τ : DeckTransformation p) :
    graphMorphism p (τ * σ) ≫ graphLeftPairMap p τ = graphMorphism p σ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, graphLeftPairMap_snd, graphMorphism_snd_assoc,
      graphMorphism_snd]
    change (σ.toSchemeHom ≫ τ.toSchemeHom) ≫ τ⁻¹.toSchemeHom = σ.toSchemeHom
    have h : τ.toSchemeHom ≫ τ⁻¹.toSchemeHom = 𝟙 X := by
      simpa only [DeckTransformation.toSchemeHom, Aut.hom_inv,
        Over.comp_left, Over.id_left, Over.mk_left] using
        congrArg (fun f : Over.mk p ⟶ Over.mk p ↦ f.left) τ.hom_inv_id
    rw [Category.assoc, h, Category.comp_id]

theorem graphIdeal_comap_graphLeftPairMap [IsSeparated p]
    (σ τ : DeckTransformation p) :
    (graphIdeal p σ).comap (graphLeftPairMap p τ) = graphIdeal p (τ * σ) := by
  have h : IsPullback (graphMorphism p (τ * σ)) (𝟙 X)
      (graphLeftPairMap p τ) (graphMorphism p σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  change _ = (graphMorphism p (τ * σ)).ker
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

/-- Left graph composition is also actual isomorphism pullback. -/
def graphChowLeftAction
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (τ : DeckTransformation p) :
    Module.End ℚ (RationalChowGroup (graphPairDimensionFunction k p b) n) :=
  graphPairChowPullback k p b (graphLeftPairMap p τ)
    (graphLeftPairMap_structure k p b τ) n

@[simp]
theorem graphChowLeftAction_one
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    graphChowLeftAction k p b n 1 = LinearMap.id := by
  apply (rationalPrincipalRelations (graphPairDimensionFunction k p b) n).quot_hom_ext
  intro c
  change rationalClassMap _ n (gradedGraphPairPullback k p b _ _ n c) =
    rationalClassMap _ n c
  congr 1
  apply Subtype.ext
  simp [graphLeftPairMap_one]

theorem graphChowLeftAction_mul
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (σ τ : DeckTransformation p) :
    graphChowLeftAction k p b n (σ * τ) =
      (graphChowLeftAction k p b n σ).comp (graphChowLeftAction k p b n τ) := by
  unfold graphChowLeftAction
  rw [graphPairChowPullback_comp]
  apply graphPairChowPullback_congr
  exact graphLeftPairMap_mul p σ τ

/-- Finite rational combinations of actual right graph pullbacks. -/
def graphChowRightLinearAction
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    MonoidAlgebra ℚ (DeckTransformation p) →ₗ[ℚ]
      Module.End ℚ (RationalChowGroup (graphPairDimensionFunction k p b) n) :=
  (Finsupp.linearCombination ℚ (graphChowRightAction k p b n)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp]
theorem graphChowRightLinearAction_single
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (τ : DeckTransformation p) (q : ℚ) :
    graphChowRightLinearAction k p b n (MonoidAlgebra.single τ q) =
      q • graphChowRightAction k p b n τ := by
  simp [graphChowRightLinearAction]

@[simp]
theorem graphChowRightLinearAction_one
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    graphChowRightLinearAction k p b n 1 = LinearMap.id := by
  change graphChowRightLinearAction k p b n (MonoidAlgebra.single 1 1) = _
  simp

/-- Finite rational combinations of actual left graph pullbacks. -/
def graphChowLeftLinearAction
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    MonoidAlgebra ℚ (DeckTransformation p) →ₗ[ℚ]
      Module.End ℚ (RationalChowGroup (graphPairDimensionFunction k p b) n) :=
  (Finsupp.linearCombination ℚ (graphChowLeftAction k p b n)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp]
theorem graphChowLeftLinearAction_single
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (τ : DeckTransformation p) (q : ℚ) :
    graphChowLeftLinearAction k p b n (MonoidAlgebra.single τ q) =
      q • graphChowLeftAction k p b n τ := by
  simp [graphChowLeftLinearAction]

@[simp]
theorem graphChowLeftLinearAction_one
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)] (n : ℤ) :
    graphChowLeftLinearAction k p b n 1 = LinearMap.id := by
  change graphChowLeftLinearAction k p b n (MonoidAlgebra.single 1 1) = _
  simp

/-- The linearized geometric right action is an anti-representation. -/
theorem graphChowRightLinearAction_mul
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowRightLinearAction k p b n (a * c) =
      (graphChowRightLinearAction k p b n c).comp
        (graphChowRightLinearAction k p b n a) := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂, LinearMap.comp_add]
  · intro σ q
    refine MonoidAlgebra.induction_linear c ?_ ?_ ?_
    · simp
    · intro c₁ c₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂, LinearMap.add_comp]
    · intro τ r
      simp only [MonoidAlgebra.single_mul_single, graphChowRightLinearAction_single,
        graphChowRightAction_mul, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]

theorem graphChowLeftLinearAction_mul
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowLeftLinearAction k p b n (a * c) =
      (graphChowLeftLinearAction k p b n a).comp
        (graphChowLeftLinearAction k p b n c) := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂, LinearMap.add_comp]
  · intro σ q
    refine MonoidAlgebra.induction_linear c ?_ ?_ ?_
    · simp
    · intro c₁ c₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂, LinearMap.comp_add]
    · intro τ r
      simp only [MonoidAlgebra.single_mul_single, graphChowLeftLinearAction_single,
        graphChowLeftAction_mul, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      rw [mul_comm q r]

/-- A group-algebra idempotent gives an actual projector on every Chow degree. -/
theorem graphChowRightLinearAction_isIdempotent
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (q : MonoidAlgebra ℚ (DeckTransformation p)) (hq : IsIdempotentElem q) :
    IsIdempotentElem (graphChowRightLinearAction k p b n q) := by
  change (graphChowRightLinearAction k p b n q).comp
    (graphChowRightLinearAction k p b n q) = _
  rw [← graphChowRightLinearAction_mul, hq.eq]

theorem graphChowLeftLinearAction_isIdempotent
    [IsNoetherian (pullback p p)]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    (n : ℤ) (q : MonoidAlgebra ℚ (DeckTransformation p)) (hq : IsIdempotentElem q) :
    IsIdempotentElem (graphChowLeftLinearAction k p b n q) := by
  change (graphChowLeftLinearAction k p b n q).comp
    (graphChowLeftLinearAction k p b n q) = _
  rw [← graphChowLeftLinearAction_mul, hq.eq]

section GraphClasses

variable [IsSeparated p] [IsIntegral X]
variable [IsNoetherian (pullback p p)]
variable [LocallyOfFiniteType (p ≫ b)]
variable [LocallyOfFiniteType (graphPairStructure k p b)]

@[simp]
theorem graphChowRightAction_graphChowClass (σ τ : DeckTransformation p) :
    graphChowRightAction k p b (graphChowDimension k p b) τ
        (graphChowClass k p b σ) = graphChowClass k p b (σ * τ) := by
  change rationalClassMap _ _
    (gradedGraphPairPullback k p b _ _ _ (gradedGraphCycle k p b σ)) = _
  change _ = rationalClassMap _ _ (gradedGraphCycle k p b (σ * τ))
  congr 1
  apply Subtype.ext
  exact graphRightPullback_graphCycle p ℚ σ τ

@[simp]
theorem graphChowLeftAction_graphChowClass (σ τ : DeckTransformation p) :
    graphChowLeftAction k p b (graphChowDimension k p b) τ
        (graphChowClass k p b σ) = graphChowClass k p b (τ * σ) := by
  change rationalClassMap _ _
    (gradedGraphPairPullback k p b _ _ _ (gradedGraphCycle k p b σ)) = _
  change _ = rationalClassMap _ _ (gradedGraphCycle k p b (τ * σ))
  congr 1
  apply Subtype.ext
  exact openRestriction_fundamentalCycle_of_comap_eq (graphLeftPairMap p τ) ℚ
    (graphIntegralSubscheme p σ) (graphIntegralSubscheme p (τ * σ))
    (graphIdeal_comap_graphLeftPairMap p σ τ)

/-- Multiplication on graph representatives agrees with actual right pullbacks. -/
theorem graphChowRightLinearAction_graphChowLinearMap
    (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowRightLinearAction k p b (graphChowDimension k p b) c
        (graphChowLinearMap k p b a) = graphChowLinearMap k p b (a * c) := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ h₁ h₂
    simp only [map_add, add_mul, h₁, h₂]
  · intro σ q
    refine MonoidAlgebra.induction_linear c ?_ ?_ ?_
    · simp
    · intro c₁ c₂ h₁ h₂
      simp only [map_add, LinearMap.add_apply, mul_add, h₁, h₂]
    · intro τ r
      simp only [MonoidAlgebra.single_mul_single, graphChowRightLinearAction_single,
        graphChowLinearMap_single, LinearMap.smul_apply, map_smul,
        graphChowRightAction_graphChowClass, smul_smul]

/-- Multiplication on graph representatives agrees with actual left pullbacks. -/
theorem graphChowLeftLinearAction_graphChowLinearMap
    (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowLeftLinearAction k p b (graphChowDimension k p b) a
        (graphChowLinearMap k p b c) = graphChowLinearMap k p b (a * c) := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ h₁ h₂
    simp only [map_add, LinearMap.add_apply, add_mul, h₁, h₂]
  · intro σ q
    refine MonoidAlgebra.induction_linear c ?_ ?_ ?_
    · simp
    · intro c₁ c₂ h₁ h₂
      simp only [map_add, mul_add, h₁, h₂]
    · intro τ r
      simp only [MonoidAlgebra.single_mul_single, graphChowLeftLinearAction_single,
        graphChowLinearMap_single, LinearMap.smul_apply, map_smul,
        graphChowLeftAction_graphChowClass, smul_smul]
      rw [mul_comm r q]

end GraphClasses

end

end HodgeConjecture.SchemeCorrespondence
