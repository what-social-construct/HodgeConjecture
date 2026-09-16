import HodgeConjecture.Cycles.DimensionFunctionRestriction
import HodgeConjecture.Cycles.CycleDegree
import HodgeConjecture.Cycles.OpenSupport

/-!
# Actual open restriction of dimension functions and homogeneous cycles

An open immersion embeds specialization orders with order-convex image.
Thus a supplied dimension function restricts by the actual point map.
The reduced-closure coefficient formula proves that existing finite-cycle
restriction preserves the corresponding homogeneous submodules over any
semiring. The resulting linear map retains the actual representatives
and inherits identity and composition from ungraded restriction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

private def openImmersionPointOrderEmbedding {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] : X ↪o Y where
  toFun := j.base
  inj' := j.isOpenEmbedding.injective
  map_rel_iff' := by
    intro x y
    change j.base y ⤳ j.base x ↔ y ⤳ x
    exact j.isOpenEmbedding.isInducing.specializes_iff

private theorem openImmersionPointRange_ordConnected {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    (Set.range (openImmersionPointOrderEmbedding j)).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact (Scheme.le_iff_specializes.mp hz.1).mem_open
    j.isOpenEmbedding.isOpen_range hx

/-- Actual open immersions preserve immediate specialization. -/
theorem openImmersion_covBy {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {x y : X} (h : x ⋖ y) :
    j.base x ⋖ j.base y :=
  h.image (openImmersionPointOrderEmbedding j)
    (openImmersionPointRange_ordConnected j)

/-- Both dimension-function conditions hold for literal composition with
the open immersion's actual point map. -/
def DimensionFunction.comapOpenImmersion {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j] :
    DimensionFunction X where
  toFun x := δ (j.base x)
  strictMono := δ.strictMono.comp (openImmersionPointOrderEmbedding j).strictMono
  map_covBy h := δ.map_covBy (openImmersion_covBy j h)

@[simp]
theorem DimensionFunction.comapOpenImmersion_apply {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    δ.comapOpenImmersion j x = δ (j.base x) := rfl

@[simp]
theorem DimensionFunction.comapOpenImmersion_id (X : Scheme.{u})
    (δ : DimensionFunction X) : δ.comapOpenImmersion (𝟙 X) = δ := by
  cases δ
  rfl

theorem DimensionFunction.comapOpenImmersion_comp {X Y Z : Scheme.{u}}
    (δ : DimensionFunction Z) (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    (δ.comapOpenImmersion j).comapOpenImmersion i =
      δ.comapOpenImmersion (i ≫ j) := rfl

/-- On a morphism that is both open and closed, the two proved restriction
constructions are the same dimension function. -/
theorem DimensionFunction.comapOpenImmersion_eq_comapClosedImmersion
    {X Y : Scheme.{u}} (δ : DimensionFunction Y) (j : X ⟶ Y)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    δ.comapOpenImmersion j = δ.comapClosedImmersion j := rfl

/-- The reduced ambient closure has the same degree for the actual
restricted dimension function; no absolute-dimension convention is used. -/
theorem supportDegree_openClosureSubscheme {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : IntegralClosedSubscheme X) :
    supportDegree δ (openClosureSubscheme j W) =
      supportDegree (δ.comapOpenImmersion j) W := by
  simp only [supportDegree, openClosureSubscheme_ambientGenericPoint,
    DimensionFunction.comapOpenImmersion_apply]

/-- A nonempty actual support restriction retains its original degree. -/
theorem supportDegree_openRestrictionSubscheme {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (W : IntegralClosedSubscheme Y) [Nonempty (W.val.comap j).subscheme] :
    supportDegree (δ.comapOpenImmersion j) (openRestrictionSubscheme j W) =
      supportDegree δ W := by
  simp only [supportDegree, DimensionFunction.comapOpenImmersion_apply,
    ambientGenericPoint_openRestrictionSubscheme]

/-- The existing finite-cycle restriction preserves the existing degree
submodules, including empty source and trivial coefficient semirings. -/
theorem openRestriction_mem_cyclesOfDegree (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℤ) (c : Cycles Y R) (hc : c ∈ cyclesOfDegree R δ n) :
    openRestriction R j c ∈ cyclesOfDegree R (δ.comapOpenImmersion j) n := by
  apply (mem_cyclesOfDegree_iff R _ n _).mpr
  intro W hW
  rw [openRestriction_apply] at hW
  rw [← supportDegree_openClosureSubscheme]
  exact (mem_cyclesOfDegree_iff R δ n c).mp hc _ hW

/-- The same actual open restriction, restricted to the homogeneous
submodules for the supplied dimension function. -/
def gradedOpenRestriction (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℤ) : cyclesOfDegree R δ n →ₗ[R]
      cyclesOfDegree R (δ.comapOpenImmersion j) n where
  toFun c := ⟨openRestriction R j c.val,
    openRestriction_mem_cyclesOfDegree R δ j n c.val c.property⟩
  map_add' c d := Subtype.ext ((openRestriction R j).map_add c.val d.val)
  map_smul' r c := Subtype.ext ((openRestriction R j).map_smul r c.val)

@[simp]
theorem gradedOpenRestriction_val (R : Type v) [Semiring R]
    {X Y : Scheme.{u}} (δ : DimensionFunction Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℤ) (c : cyclesOfDegree R δ n) :
    (gradedOpenRestriction R δ j n c).val = openRestriction R j c.val := rfl

/-- Graded restriction retains the existing identity cycle map. -/
theorem gradedOpenRestriction_id (R : Type v) [Semiring R]
    (X : Scheme.{u}) (δ : DimensionFunction X) (n : ℤ) :
    gradedOpenRestriction R δ (𝟙 X) n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact LinearMap.congr_fun (openRestriction_id R) c.val

/-- Contravariant composition is inherited on the same actual cycle
representatives, with definitionally equal restricted dimension functions. -/
theorem gradedOpenRestriction_comp (R : Type v) [Semiring R]
    {X Y Z : Scheme.{u}} (δ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℤ) :
    (gradedOpenRestriction R (δ.comapOpenImmersion j) i n).comp
        (gradedOpenRestriction R δ j n) =
      gradedOpenRestriction R δ (i ≫ j) n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact LinearMap.congr_fun (openRestriction_comp j R i) c.val

end

end HodgeConjecture.SchemeCycles
