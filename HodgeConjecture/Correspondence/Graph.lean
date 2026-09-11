import HodgeConjecture.Correspondence.EtaleClasses
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Graph correspondences over a base

An automorphism of `X` over `S` determines its graph correspondence

`X ← X → X`,

with left leg the identity and right leg the automorphism.  Using
automorphisms of the slice object `Over.mk pX` makes compatibility with the
base part of the type.

Graph correspondences compose exactly as automorphisms do.  Their legs are
finite étale, so their classes land in the finite-étale correspondence
submonoid and linearize to an algebra map from the deck-transformation group
algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- Automorphisms of `X` over `S`. -/
abbrev DeckTransformation :=
  Aut (Over.mk pX)

/-- The underlying scheme automorphism of a deck transformation. -/
abbrev DeckTransformation.toSchemeHom
    (σ : DeckTransformation pX) :
    X ⟶ X :=
  σ.hom.left

/-- A deck transformation commutes with the structure map to the base. -/
@[reassoc (attr := simp)]
theorem DeckTransformation.toSchemeHom_comp
    (σ : DeckTransformation pX) :
    σ.toSchemeHom ≫ pX = pX := by
  simpa using Over.w σ.hom

/-- The graph span of an automorphism over the base. -/
def graph
    (σ : DeckTransformation pX) :
    SchemeCorrespondence pX pX where
  carrier := X
  left := 𝟙 X
  right := σ.toSchemeHom
  over_base := by
    rw [Category.id_comp]
    exact σ.toSchemeHom_comp.symm

@[simp]
theorem graph_left
    (σ : DeckTransformation pX) :
    (graph pX σ).left = 𝟙 X :=
  rfl

@[simp]
theorem graph_right
    (σ : DeckTransformation pX) :
    (graph pX σ).right = σ.toSchemeHom :=
  rfl

/-- The graph of the identity automorphism is the identity correspondence. -/
def graphOneIsom :
    SchemeCorrespondence.Isom
      (graph pX 1)
      (SchemeCorrespondence.identity pX) where
  carrierIso := Iso.refl X
  hom_left := by simp [graph]
  hom_right := by
    change
      𝟙 X =
        (1 : DeckTransformation pX).hom.left
    simp only [
      show (1 : DeckTransformation pX).hom =
        𝟙 (Over.mk pX) from rfl,
      Over.id_left]
    rfl

/--
Convolution of graph spans agrees with multiplication in the automorphism
group.

The `Aut` multiplication convention is function composition:
`(σ * τ).hom = τ.hom ≫ σ.hom`.  Thus `graph σ` acting after `graph τ`
is `graph (σ * τ)`, exactly matching the existing correspondence
multiplication convention.
-/
noncomputable def graphMulIsom
    (σ τ : DeckTransformation pX) :
    SchemeCorrespondence.Isom
      ((graph pX σ).comp (graph pX τ))
      (graph pX (σ * τ)) where
  carrierIso :=
    asIso (pullback.fst τ.toSchemeHom (𝟙 X))
  hom_left := by
    simp [SchemeCorrespondence.comp, graph]
  hom_right := by
    change
      pullback.fst τ.hom.left (𝟙 X) ≫
          (τ.hom.left ≫ σ.hom.left) =
        pullback.snd τ.hom.left (𝟙 X) ≫
          σ.hom.left
    rw [← Category.assoc, pullback.condition]
    simp

/-- Every graph correspondence has finite étale legs. -/
theorem graph_hasFiniteEtaleLegs
    (σ : DeckTransformation pX) :
    HasFiniteEtaleLegs (graph pX σ) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · change IsEtale (𝟙 X)
      exact MorphismProperty.id_mem @IsEtale X
    · change IsEtale σ.toSchemeHom
      exact
        MorphismProperty.of_isIso
          @IsEtale σ.toSchemeHom
  · change IsFinite (𝟙 X)
    exact MorphismProperty.id_mem @IsFinite X
  · change IsFinite σ.toSchemeHom
    infer_instance

/-- A graph correspondence as a finite-étale correspondence class. -/
def graphFiniteEtaleClass
    (σ : DeckTransformation pX) :
    FiniteEtaleClass pX :=
  finiteEtaleClassOf
    (graph pX σ)
    (graph_hasFiniteEtaleLegs pX σ)

/--
Deck transformations map multiplicatively to finite-étale correspondence
classes.
-/
noncomputable def graphClassMonoidHom :
    DeckTransformation pX →*
      FiniteEtaleClass pX where
  toFun := graphFiniteEtaleClass pX
  map_one' := by
    apply Subtype.ext
    exact classOf_eq_of_isom (graphOneIsom pX)
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    change
      classOf (graph pX (σ * τ)) =
        classOf (graph pX σ) *
          classOf (graph pX τ)
    exact
      (classOf_eq_of_isom
        (graphMulIsom pX σ τ).symm).trans
          (classOf_comp
            (pX := pX)
            (graph pX σ) (graph pX τ))

/-- The rational group algebra of deck transformations. -/
abbrev DeckGroupAlgebra :=
  MonoidAlgebra ℚ (DeckTransformation pX)

/--
The algebra map sending a deck transformation to its graph
correspondence.
-/
noncomputable def graphAlgebraMap :
    DeckGroupAlgebra pX →ₐ[ℚ]
      FiniteEtaleFreeAlgebra pX :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ
    (graphClassMonoidHom pX)

@[simp]
theorem graphAlgebraMap_single
    (σ : DeckTransformation pX) :
    graphAlgebraMap pX
        (MonoidAlgebra.single σ 1) =
      finiteEtaleOfScheme
        (graph pX σ)
        (graph_hasFiniteEtaleLegs pX σ) := by
  simp [graphAlgebraMap, graphClassMonoidHom,
    graphFiniteEtaleClass, finiteEtaleOfScheme,
    finiteEtaleClassOf]

end SchemeCorrespondence

end

end HodgeConjecture
