module

public import HodgeConjecture.Cycles.DimensionFunction

@[expose] public section

/-!
# Restriction of dimension functions to actual closed subschemes

A closed immersion is an embedding of specialization orders with
order-convex image. It preserves immediate specialization, so an ambient
dimension function restricts by the actual point map. The degree of an
integral support computed with that restriction agrees with the degree
of its actual closed image. No ambient integrality or Noetherianity is
required, and no existence of a dimension function is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

def closedImmersionPointOrderEmbedding {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] : X ↪o Y where
  toFun := i.base
  inj' := i.isClosedEmbedding.injective
  map_rel_iff' := by
    intro x y
    change i.base y ⤳ i.base x ↔ y ⤳ x
    exact i.isClosedEmbedding.isInducing.specializes_iff

private theorem closedImmersionPointRange_ordConnected {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] :
    (Set.range (closedImmersionPointOrderEmbedding i)).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact (Scheme.le_iff_specializes.mp hz.2).mem_closed
    i.isClosedEmbedding.isClosed_range hy

/-- A closed immersion preserves immediate specialization, using the
closedness of its actual point image. -/
theorem closedImmersion_covBy {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {x y : X} (h : x ⋖ y) :
    i.base x ⋖ i.base y :=
  h.image (closedImmersionPointOrderEmbedding i)
    (closedImmersionPointRange_ordConnected i)

/-- Restriction is literal composition with the actual closed-immersion
point map; both dimension-function conditions are proved. -/
def DimensionFunction.comapClosedImmersion {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i] :
    DimensionFunction X where
  toFun x := δ (i.base x)
  strictMono := δ.strictMono.comp (closedImmersionPointOrderEmbedding i).strictMono
  map_covBy h := δ.map_covBy (closedImmersion_covBy i h)

@[simp]
theorem DimensionFunction.comapClosedImmersion_apply {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    δ.comapClosedImmersion i x = δ (i.base x) := rfl

@[simp]
theorem DimensionFunction.comapClosedImmersion_id (X : Scheme.{u})
    (δ : DimensionFunction X) : δ.comapClosedImmersion (𝟙 X) = δ := by
  cases δ
  rfl

theorem DimensionFunction.comapClosedImmersion_comp {X Y Z : Scheme.{u}}
    (δ : DimensionFunction Z) (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (δ.comapClosedImmersion j).comapClosedImmersion i =
      δ.comapClosedImmersion (i ≫ j) := rfl

/-- Degree in a closed source is the ambient degree of the actual image;
this is not an assertion that ambient codimension is unchanged. -/
theorem supportDegree_comapClosedImmersion {X Y : Scheme.{u}}
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (Z : IntegralClosedSubscheme X) :
    supportDegree (δ.comapClosedImmersion i) Z =
      supportDegree δ (closedImageSubscheme i Z) := by
  rw [supportDegree_closedImageSubscheme]
  rfl

end

end HodgeConjecture.SchemeCycles
