module

public import HodgeConjecture.Realization.DeRham.TwoTermDegreeFiltration
public import Mathlib.Algebra.Module.Submodule.Range

@[expose] public section

/-!
# Actual hypercohomology maps and their image filtration

The original extension by zero defines a functor on nonnegative complexes.
Applying the original bounded-below derived functor and homology gives
actual hypercohomology maps. Their linear ranges form the image subspaces
used by a genuine degree filtration. Range monotonicity follows from the
original transition/inclusion factorization; it is not an assigned list
of desired subspaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.HypercohomologyFiltration

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable (C : Type*) [Category* C] [Abelian C]

/-- Original extension by zero, retained functorially in the bounded-below category. -/
def nonnegativeFunctor : CochainComplex C ℕ ⥤ CochainComplex.Plus C where
  obj K := BoundedBelowDerived.nonnegativePlus K
  map f := ObjectProperty.homMk
    (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0))
  map_id K := by
    apply ObjectProperty.hom_ext
    exact HomologicalComplex.extendMap_id K _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact HomologicalComplex.extendMap_comp f g _

instance nonnegativeFunctor_additive : (nonnegativeFunctor C).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change ((ComplexShape.embeddingUpIntGE 0).extendFunctor C).map (f + g) =
      ((ComplexShape.embeddingUpIntGE 0).extendFunctor C).map f +
        ((ComplexShape.embeddingUpIntGE 0).extendFunctor C).map g
    exact Functor.map_add _

variable {C}
variable {D : Type*} [Category* D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/-- The original bounded-below derived functor and homology on actual nonnegative complexes. -/
def functor (n : ℤ) : CochainComplex C ℕ ⥤ D :=
  nonnegativeFunctor C ⋙ DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n

instance functor_additive (n : ℤ) : (functor F n).Additive := by
  unfold functor
  infer_instance

@[simp]
theorem functor_map (n : ℤ) {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (functor F n).map f =
      (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk
            (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0))))) := rfl

section Module

universe w

variable {R : Type w} [Ring R]
variable (G : C ⥤ ModuleCat.{w} R) [G.Additive] [HasDerivedCategory (ModuleCat.{w} R)]

/-- The image is the actual linear range of the actual hypercohomology map. -/
def image {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℤ) :
    Submodule R ((functor G n).obj L) :=
  LinearMap.range ((functor G n).map f).hom

/-- An actual transition followed by an inclusion has image contained in that inclusion. -/
theorem image_comp_le {K L M : CochainComplex C ℕ} (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    image G (f ≫ g) n ≤ image G g n := by
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  refine ⟨(functor G n).map f x, ?_⟩
  change ((functor G n).map f ≫ (functor G n).map g) x =
    (functor G n).map (f ≫ g) x
  rw [Functor.map_comp]

/-- Range containment follows from a proved factorization of the original inclusion maps. -/
theorem image_le_of_factorization {K L M : CochainComplex C ℕ}
    (i : K ⟶ M) (j : L ⟶ M) (t : K ⟶ L) (h : t ≫ j = i) (n : ℤ) :
    image G i n ≤ image G j n := by
  rw [← h]
  exact image_comp_le G t j n

/-- A proved epimorphism on actual hypercohomology gives the whole target image. -/
theorem image_eq_top_of_epi {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℤ)
    [Epi ((functor G n).map f)] : image G f n = ⊤ :=
  LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- In particular the image of a proved actual hypercohomology isomorphism is the whole target. -/
theorem image_eq_top_of_isIso {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℤ)
    [IsIso ((functor G n).map f)] : image G f n = ⊤ :=
  image_eq_top_of_epi G f n

/-- The image of an original zero complex map is zero. -/
@[simp]
theorem image_zero {K L : CochainComplex C ℕ} (n : ℤ) :
    image G (0 : K ⟶ L) n = ⊥ := by
  simp [image]

/-- An actually zero source filtration complex has zero hypercohomological image. -/
theorem image_eq_bot_of_isZero {K L : CochainComplex C ℕ}
    (f : K ⟶ L) (hK : IsZero K) (n : ℤ) : image G f n = ⊥ := by
  rw [hK.eq_of_src f 0]
  exact image_zero G n

/-- The decreasing image filtration of the actual brutal degree subcomplexes. -/
def filtration (K : CochainComplex C ℕ) (n : ℤ) (p : ℕ) :
    Submodule R ((functor G n).obj K) :=
  image G (DegreeFiltration.inclusion K p) n

/-- Actual transition maps make the hypercohomology image filtration decreasing. -/
theorem filtration_antitone (K : CochainComplex C ℕ) (n : ℤ) :
    Antitone (filtration G K n) := by
  intro p q hpq
  exact image_le_of_factorization G
    (DegreeFiltration.inclusion K q) (DegreeFiltration.inclusion K p)
    (DegreeFiltration.transition K p q hpq)
    (DegreeFiltration.transition_inclusion K p q hpq) n

/-- Level zero is the original complex and therefore its image is the whole cohomology group. -/
@[simp]
theorem filtration_zero (K : CochainComplex C ℕ) (n : ℤ) :
    filtration G K n 0 = ⊤ := by
  exact image_eq_top_of_isIso G (DegreeFiltration.inclusion K 0) n

/-- A genuinely zero high-degree filtered complex has zero hypercohomological image. -/
theorem filtration_eq_bot_of_twoTerm (K : CochainComplex C ℕ)
    (hK : ∀ i : ℕ, 2 ≤ i → IsZero (K.X i)) (n : ℤ) (p : ℕ) (hp : 2 ≤ p) :
    filtration G K n p = ⊥ :=
  image_eq_bot_of_isZero G (DegreeFiltration.inclusion K p)
    (DegreeFiltration.complex_isZero_of_twoTerm K hK p hp) n

/-- The original degree-one inclusion is invertible on actual degree-two hypercohomology
under the adjacent right-derived vanishings of the original degree-zero term. -/
theorem degreeOne_inclusion_map_isIso (K : CochainComplex C ℕ)
    (hK : ∀ i : ℕ, 2 ≤ i → IsZero (K.X i))
    (h₁ : IsZero ((G.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((G.rightDerived 2).obj (K.X 0))) :
    IsIso ((functor G 2).map (TwoTermComplex.inclusion K hK)) :=
  BoundedBelowDerived.twoTermInclusion_isIso G K hK h₁ h₂

/-- The actual filtration-one map retains the original two-term derived inclusion. -/
theorem filtration_one_map_isIso (K : CochainComplex C ℕ)
    (hK : ∀ i : ℕ, 2 ≤ i → IsZero (K.X i))
    (h₁ : IsZero ((G.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((G.rightDerived 2).obj (K.X 0))) :
    IsIso ((functor G 2).map (DegreeFiltration.inclusion K 1)) := by
  have := degreeOne_inclusion_map_isIso G K hK h₁ h₂
  rw [← DegreeFiltration.degreeOneIso_hom_inclusion K hK, Functor.map_comp]
  infer_instance

/-- For a genuine two-term complex with the proved adjacent vanishings,
the actual filtration-one image is the whole degree-two hypercohomology. -/
theorem filtration_one_of_twoTerm (K : CochainComplex C ℕ)
    (hK : ∀ i : ℕ, 2 ≤ i → IsZero (K.X i))
    (h₁ : IsZero ((G.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((G.rightDerived 2).obj (K.X 0))) :
    filtration G K 2 1 = ⊤ := by
  have := filtration_one_map_isIso G K hK h₁ h₂
  exact image_eq_top_of_isIso G (DegreeFiltration.inclusion K 1) 2

end Module

section Sheaf

universe u

variable (k : Type u) [CommRing k] (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- The generic functor retains exactly the existing actual sheaf hypercohomology object. -/
theorem sheaf_functor_obj (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ) (n : ℤ) :
    (functor (SheafHypercohomology.globalSections k X) n).obj K =
      SheafHypercohomology.hypercohomology k X K n := rfl

/-- The image construction uses the original sheaf hypercohomology map without replacing it. -/
theorem sheaf_functor_map {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ}
    (f : K ⟶ L) (n : ℤ) :
    (functor (SheafHypercohomology.globalSections k X) n).map f =
      SheafHypercohomology.hypercohomologyMap k X f n := rfl

end Sheaf

end HodgeConjecture.HypercohomologyFiltration
