import HodgeConjecture.Correspondence.GraphComposition

/-!
# Relative products under a change of structural base

For `X → S → B`, there are actual scheme morphisms from the pair and triple
products over `S` to the corresponding products over `B`. They preserve
each coordinate and commute with all three pair projections. When `S → B`
is separated, both comparison morphisms are closed immersions: the pair
comparison is a base change of its diagonal, and the triple comparison is
formed from two base changes of the pair comparison.

No étaleness, properness, or separatedness of `X → S` is required.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {X S B : Scheme.{u}} (p : X ⟶ S) (b : S ⟶ B)

/-- The relative pair product maps to the pair product over the structural
base by the identity on its two `X` coordinates. -/
def pairBaseComparison : pullback p p ⟶ pullback (p ≫ b) (p ≫ b) :=
  pullback.mapDesc p p b

@[reassoc (attr := simp)]
theorem pairBaseComparison_fst :
    pairBaseComparison p b ≫ pullback.fst (p ≫ b) (p ≫ b) =
      pullback.fst p p := by
  simp [pairBaseComparison]

@[reassoc (attr := simp)]
theorem pairBaseComparison_snd :
    pairBaseComparison p b ≫ pullback.snd (p ≫ b) (p ≫ b) =
      pullback.snd p p := by
  simp [pairBaseComparison]

/-- The pair comparison is a closed immersion because it is a base change
of the diagonal of the separated structural-base morphism. -/
instance pairBaseComparison_isClosedImmersion [IsSeparated b] :
    IsClosedImmersion (pairBaseComparison p b) := by
  unfold pairBaseComparison
  infer_instance

/-- The relative triple product maps to the triple product over the
structural base by applying the pair comparison twice over the same middle
coordinate. -/
def tripleBaseComparison : tripleProduct p ⟶ tripleProduct (p ≫ b) :=
  pullback.map (pullback.snd p p) (pullback.fst p p)
    (pullback.snd (p ≫ b) (p ≫ b)) (pullback.fst (p ≫ b) (p ≫ b))
    (pairBaseComparison p b) (pairBaseComparison p b) (𝟙 X)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem tripleBaseComparison_p12 :
    tripleBaseComparison p b ≫ tripleProductP12 (p ≫ b) =
      tripleProductP12 p ≫ pairBaseComparison p b := by
  simp [tripleBaseComparison]

@[reassoc (attr := simp)]
theorem tripleBaseComparison_p23 :
    tripleBaseComparison p b ≫ tripleProductP23 (p ≫ b) =
      tripleProductP23 p ≫ pairBaseComparison p b := by
  simp [tripleBaseComparison]

@[reassoc (attr := simp)]
theorem tripleBaseComparison_p13 :
    tripleBaseComparison p b ≫ tripleProductP13 (p ≫ b) =
      tripleProductP13 p ≫ pairBaseComparison p b := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The triple comparison is a closed immersion whenever the structural
base morphism is separated. -/
instance tripleBaseComparison_isClosedImmersion [IsSeparated b] :
    IsClosedImmersion (tripleBaseComparison p b) := by
  exact MorphismProperty.pullback_map
    (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (pairBaseComparison p b))
    (inferInstance : IsClosedImmersion (pairBaseComparison p b))
    (pairBaseComparison_snd p b).symm (pairBaseComparison_fst p b).symm

end

end HodgeConjecture.SchemeCorrespondence
