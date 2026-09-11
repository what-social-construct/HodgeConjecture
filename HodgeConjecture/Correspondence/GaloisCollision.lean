import HodgeConjecture.Correspondence.CollisionEtale
import HodgeConjecture.Correspondence.FiniteCoproduct
import HodgeConjecture.Correspondence.FiniteEtaleModel
import HodgeConjecture.Correspondence.FiniteGroupProjector

/-!
# Galois collision sheets and averaging projectors

For a finite Galois cover, the torsor comparison identifies the collision
space with the disjoint union of the graphs of the deck transformations:

`∐ a : G, X ≅ X ×[Y] X`.

Mathlib does not currently package the required scheme-theoretic torsor API.
`GaloisCollisionDecomposition` therefore records the exact geometric datum:
an action over `Y`, an isomorphism of schemes, and its compatibility with
both collision projections.  From this input we prove an isomorphism of
scheme correspondences and, in every finitely additive algebra model, the
class formula

`[X ×[Y] X] = ∑ a : G, [Γ_a]`.

The normalized full graph sum is the finite-group averaging projector.  It
is a genuine convolution idempotent.  The off-diagonal sum obtained by
removing the identity graph is generally not idempotent; nor is it the same
kind of object as the coordinate-ring selector that makes the diagonal
clopen.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v w

variable {S X Y : Scheme.{u}}

/--
An explicit Galois/torsor decomposition of a self-collision scheme.

The action is by automorphisms of `X` over `Y`.  On the `a`-component of the
coproduct, the stored isomorphism to `X ×[Y] X` has projections `id_X` and
`a`.  These equations say precisely that this component is the graph sheet
of `a`.
-/
structure GaloisCollisionDecomposition
    (G : Type u) [Group G]
    (f : X ⟶ Y) where
  action : SchemeCorrespondence.FiniteDeckAction f G
  collisionIso :
    (∐ fun _ : G ↦ X) ≅ collisionSpace f
  collisionIso_hom_fst :
    ∀ a,
      Sigma.ι (fun _ : G ↦ X) a ≫
          collisionIso.hom ≫ collisionFst f =
        𝟙 X
  collisionIso_hom_snd :
    ∀ a,
      Sigma.ι (fun _ : G ↦ X) a ≫
          collisionIso.hom ≫ collisionSnd f =
        (action a).toSchemeHom

namespace GaloisCollisionDecomposition

variable {G : Type u} [Group G] {f : X ⟶ Y}

/--
Postcomposing the base map turns deck transformations over `Y` into deck
transformations over `S`.
-/
noncomputable def actionOverBase
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) :
    SchemeCorrespondence.FiniteDeckAction (f ≫ g) G :=
  ((Over.map g).mapAut (Over.mk f)).comp D.action

@[simp]
theorem actionOverBase_toSchemeHom
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) (a : G) :
    (D.actionOverBase g a).toSchemeHom =
      (D.action a).toSchemeHom :=
  rfl

/-- The graph correspondence of one Galois sheet over the chosen base. -/
def graphCorrespondence
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) (a : G) :
    SchemeCorrespondence (f ≫ g) (f ≫ g) :=
  SchemeCorrespondence.graph
    (f ≫ g) (D.actionOverBase g a)

/-- The literal indexed coproduct of all graph-sheet correspondences. -/
def graphFamilyCorrespondence
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) :
    SchemeCorrespondence (f ≫ g) (f ≫ g) :=
  SchemeCorrespondence.indexedCoprod
    fun a ↦ D.graphCorrespondence g a

/--
The torsor comparison is an isomorphism from the coproduct of graph sheets
to the collision correspondence.
-/
noncomputable def collisionCorrespondenceIso
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) :
    SchemeCorrespondence.Isom
      (D.graphFamilyCorrespondence g)
      (collisionSchemeCorrespondence f g) where
  carrierIso := D.collisionIso
  hom_left := by
    apply Sigma.hom_ext
    intro a
    simpa [graphFamilyCorrespondence,
      graphCorrespondence,
      SchemeCorrespondence.indexedCoprod,
      SchemeCorrespondence.graph,
      collisionSchemeCorrespondence] using
        D.collisionIso_hom_fst a
  hom_right := by
    apply Sigma.hom_ext
    intro a
    simpa [graphFamilyCorrespondence,
      graphCorrespondence,
      SchemeCorrespondence.indexedCoprod,
      SchemeCorrespondence.graph,
      collisionSchemeCorrespondence] using
        D.collisionIso_hom_snd a

section Finite

/-- Every graph sheet in the Galois decomposition has finite étale legs. -/
theorem graphCorrespondence_hasFiniteEtaleLegs
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S) (a : G) :
    SchemeCorrespondence.HasFiniteEtaleLegs
      (D.graphCorrespondence g a) := by
  simpa [graphCorrespondence] using
    SchemeCorrespondence.graph_hasFiniteEtaleLegs
      (f ≫ g) (D.actionOverBase g a)

variable [Fintype G] [IsFinite f] [IsEtale f]

/--
Every finite-étale algebra model sends the geometric Galois sheet
decomposition to the sum of the graph classes.  The model is defined only on
the admissible finite-étale convolution algebra, so this statement does not
quantify over arbitrary infinite-type spans.
-/
theorem classOf_collision_eq_sum_graph
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ)
    :
    χ.classOf (collisionSchemeCorrespondence f g)
        (collisionSchemeCorrespondence_hasFiniteEtaleLegs f g) =
      ∑ a : G,
        χ.classOf (D.graphCorrespondence g a)
          (D.graphCorrespondence_hasFiniteEtaleLegs g a) := by
  let hCollision :=
    collisionSchemeCorrespondence_hasFiniteEtaleLegs f g
  let hGraphs : ∀ a : G,
      SchemeCorrespondence.HasFiniteEtaleLegs
        (D.graphCorrespondence g a) :=
    fun a ↦ D.graphCorrespondence_hasFiniteEtaleLegs g a
  let hFamily :
      SchemeCorrespondence.HasFiniteEtaleLegs
        (D.graphFamilyCorrespondence g) :=
    SchemeCorrespondence.HasFiniteEtaleLegs.of_isom
      (D.collisionCorrespondenceIso g).symm hCollision
  calc
    χ.classOf (collisionSchemeCorrespondence f g) hCollision =
        χ.classOf (D.graphFamilyCorrespondence g) hFamily :=
      χ.classOf_isom hCollision hFamily
        (D.collisionCorrespondenceIso g).symm
    _ = ∑ a : G,
          χ.classOf (D.graphCorrespondence g a) (hGraphs a) := by
      simpa [graphFamilyCorrespondence] using
        χ.classOf_indexedCoprod
          (fun a ↦ D.graphCorrespondence g a) hGraphs hFamily

/--
The algebra realization supplied by a finite-étale model.
-/
noncomputable def finiteEtaleAlgebraRealization
    (pX : X ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ : SchemeCorrespondence.FiniteEtaleAlgebraModel pX Γ) :
    SchemeCorrespondence.FiniteEtaleFreeAlgebra pX →ₐ[ℚ] Γ :=
  χ.realization

@[simp]
theorem finiteEtaleAlgebraRealization_ofScheme
    (pX : X ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ : SchemeCorrespondence.FiniteEtaleAlgebraModel pX Γ)
    (P : SchemeCorrespondence pX pX)
    (hP : SchemeCorrespondence.HasFiniteEtaleLegs P) :
    finiteEtaleAlgebraRealization pX χ
        (SchemeCorrespondence.finiteEtaleOfScheme P hP) =
      χ.classOf P hP := by
  rfl

end Finite

section FiniteAverage

variable [Fintype G]

/--
The averaging projector maps to the normalized sum of the Galois graph
classes in every finite-étale algebra model.
-/
theorem averagingProjector_realizes_normalized_graph_sum
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ) :
    finiteEtaleAlgebraRealization (f ≫ g) χ
        (SchemeCorrespondence.averagingProjector
          (f ≫ g) (D.actionOverBase g)) =
      (Fintype.card G : ℚ)⁻¹ •
        ∑ a : G,
          χ.classOf (D.graphCorrespondence g a)
            (D.graphCorrespondence_hasFiniteEtaleLegs g a) := by
  rw [SchemeCorrespondence.averagingProjector_eq_sum]
  simp [finiteEtaleAlgebraRealization,
    SchemeCorrespondence.FiniteEtaleAlgebraModel.classOf,
    graphCorrespondence]

end FiniteAverage

section Finite

variable [Fintype G] [IsFinite f] [IsEtale f]

/-- The normalized collision class in a chosen finite-étale realization. -/
def normalizedCollisionClass
    (_D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ) :
    Γ :=
  (Fintype.card G : ℚ)⁻¹ •
    χ.classOf (collisionSchemeCorrespondence f g)
      (collisionSchemeCorrespondence_hasFiniteEtaleLegs f g)

/--
Under the geometric sheet decomposition and finite additivity, the
finite-étale averaging projector realizes the normalized collision class.
-/
theorem averagingProjector_realizes_normalizedCollisionClass
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ) :
    finiteEtaleAlgebraRealization (f ≫ g) χ
        (SchemeCorrespondence.averagingProjector
          (f ≫ g) (D.actionOverBase g)) =
      D.normalizedCollisionClass g χ := by
  rw [D.averagingProjector_realizes_normalized_graph_sum g χ,
    normalizedCollisionClass,
    ← D.classOf_collision_eq_sum_graph g χ]

/--
The normalized full collision class is a genuine convolution idempotent in
every finite-étale algebra model.
-/
theorem normalizedCollisionClass_isIdempotent
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ) :
    IsIdempotentElem (D.normalizedCollisionClass g χ) := by
  rw [← D.averagingProjector_realizes_normalizedCollisionClass
    g χ]
  exact
    (SchemeCorrespondence.averagingProjector_isIdempotent
      (f ≫ g) (D.actionOverBase g)).map
        (finiteEtaleAlgebraRealization (f ≫ g) χ)

/--
For a clopen diagonal/off-diagonal decomposition, the off-diagonal class is
the graph sum with the diagonal unit removed.  This is an additive identity,
not an assertion that the off-diagonal class is convolution-idempotent.
-/
theorem classOf_offDiagonal_eq_sum_graph_sub_one
    (D : GaloisCollisionDecomposition G f)
    (E : CollisionSchemeDecomposition f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ) :
    χ.classOf (E.offDiagonalSchemeCorrespondence g)
        (E.offDiagonalSchemeCorrespondence_hasFiniteEtaleLegs g) =
      (∑ a : G,
        χ.classOf (D.graphCorrespondence g a)
          (D.graphCorrespondence_hasFiniteEtaleLegs g a)) - 1 := by
  let hCollision :=
    collisionSchemeCorrespondence_hasFiniteEtaleLegs f g
  let hIdentity :=
    SchemeCorrespondence.HasFiniteEtaleLegs.identity (f ≫ g)
  let hOff :=
    E.offDiagonalSchemeCorrespondence_hasFiniteEtaleLegs g
  let hCoprod :
      SchemeCorrespondence.HasFiniteEtaleLegs
        (SchemeCorrespondence.coprod
          (SchemeCorrespondence.identity (f ≫ g))
          (E.offDiagonalSchemeCorrespondence g)) :=
    SchemeCorrespondence.HasFiniteEtaleLegs.of_isom
      (E.correspondenceDecompositionIsom g) hCollision
  have hdecomp :
      χ.classOf (collisionSchemeCorrespondence f g) hCollision =
        1 + χ.classOf (E.offDiagonalSchemeCorrespondence g) hOff := by
    calc
      χ.classOf (collisionSchemeCorrespondence f g) hCollision =
          χ.classOf
            (SchemeCorrespondence.coprod
              (SchemeCorrespondence.identity (f ≫ g))
              (E.offDiagonalSchemeCorrespondence g)) hCoprod :=
        χ.classOf_isom hCollision hCoprod
          (E.correspondenceDecompositionIsom g)
      _ =
          χ.classOf (SchemeCorrespondence.identity (f ≫ g)) hIdentity +
            χ.classOf (E.offDiagonalSchemeCorrespondence g) hOff :=
        χ.classOf_coprod _ _ hIdentity hOff hCoprod
      _ = 1 + χ.classOf (E.offDiagonalSchemeCorrespondence g) hOff := by
        rw [χ.classOf_identity]
  rw [D.classOf_collision_eq_sum_graph g χ] at hdecomp
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using hdecomp.symm

/--
The normalized collision correspondence supplies an algebraic lift of its
operator under any rational correspondence action.
-/
noncomputable def normalizedCollisionProjectorLift
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ S)
    {Γ : Type v} [Ring Γ] [Algebra ℚ Γ]
    (χ :
      SchemeCorrespondence.FiniteEtaleAlgebraModel
        (f ≫ g) Γ)
    {H : Type w} [AddCommGroup H] [Module ℚ H]
    (ρ : RationalCorrespondenceAction Γ H) :
    AlgebraicProjectorLift ρ
      (ρ.action (D.normalizedCollisionClass g χ)) where
  projector := D.normalizedCollisionClass g χ
  projector_isIdempotent :=
    D.normalizedCollisionClass_isIdempotent g χ
  realizes := rfl

end Finite

end GaloisCollisionDecomposition

end

end HodgeConjecture
