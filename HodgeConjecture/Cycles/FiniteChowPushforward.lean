import HodgeConjecture.Cycles.FinitePrincipalDivisorImage
import HodgeConjecture.Cycles.FiniteGrading
import HodgeConjecture.Cycles.ChowPushforward

/-!
# Finite pushforward on the existing Chow quotient

The target relation is constructed on the actual image carrier using the
actual field norm. The geometric principal-divisor identity proves
preservation of generators and their span, hence quotient descent.
The canonical field grading is preserved by the existing finite-grading
theorem; no degree or relation compatibility is supplied to the final map.

This implements the finite case of Stacks 02RT and the resulting descent:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Actual image relation data, with the rational function constructed by its norm. -/
def PrincipalRelationData.finiteImage {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) : PrincipalRelationData δY n := by
  letI := d.1.val.property
  letI := (imageSubscheme f d.1.val).property
  exact ⟨⟨imageSubscheme f d.1.val, (hdeg d.1.val).trans d.1.property⟩,
    finiteImageNorm f d.1.val d.2⟩

/-- Every genuine principal generator maps to its norm generator on the actual image. -/
theorem gradedFinitePushforward_principalRelation
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) :
    gradedFinitePushforward ℤ δX δY f hdeg n (principalRelation δX n d) =
      principalRelation δY n (d.finiteImage δX δY f hdeg n) := by
  apply Subtype.ext
  exact finitePushforward_ambientPrincipalDivisor f k pY d.1.val d.2

/-- Preservation of the actual relation span follows from the geometric norm identity. -/
theorem principalRelations_le_comap_finitePushforward
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (f : X ⟶ Y) [IsFinite f]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (n : ℤ) :
    principalRelations δX n ≤ (principalRelations δY n).comap
      (gradedFinitePushforward ℤ δX δY f hdeg n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedFinitePushforward ℤ δX δY f hdeg n (principalRelation δX n d) ∈
    principalRelations δY n
  rw [gradedFinitePushforward_principalRelation k pY]
  exact principalRelation_mem δY n _

/-- Finite pushforward on the original Chow groups with the canonical field grading.
No integrality of the ambient schemes or dominance of the finite map is required. -/
def chowFinitePushforward
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ) :
    ChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n →ₗ[ℤ]
      ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n :=
  let δX := DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)
  let δY := DimensionFunction.ofLocallyOfFiniteType k Y pY
  let hdeg := supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f
  (principalRelations δX n).mapQ (principalRelations δY n)
    (gradedFinitePushforward ℤ δX δY f hdeg n)
    (principalRelations_le_comap_finitePushforward k pY δX δY f hdeg n)

/-- Quotient descent retains exactly the existing finite cycle map. -/
@[simp]
theorem chowFinitePushforward_classMap
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ)
    (c : cyclesOfDegree ℤ (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n) :
    chowFinitePushforward k pY f n
        (classMap (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n c) =
      classMap (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
        (gradedFinitePushforward ℤ
          (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY))
          (DimensionFunction.ofLocallyOfFiniteType k Y pY) f
          (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n c) := rfl

/-- On a closed immersion the new descent agrees with the existing Chow operation. -/
theorem chowFinitePushforward_eq_closedImmersionPushforward
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (i : X ⟶ Y) [IsClosedImmersion i] (n : ℤ) :
    chowFinitePushforward k pY i n =
      chowClosedImmersionPushforward
        (DimensionFunction.ofLocallyOfFiniteType k X (i ≫ pY))
        (DimensionFunction.ofLocallyOfFiniteType k Y pY) i
        (fun W ↦ by simpa only [imageSubscheme_eq_closedImageSubscheme] using
          supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY i W) n := by
  apply (principalRelations _ n).quot_hom_ext
  intro c
  change classMap _ n (gradedFinitePushforward ℤ _ _ i _ n c) =
    classMap _ n (gradedClosedImmersionPushforward _ _ i _ n c)
  rw [gradedFinitePushforward_eq_closedImmersionPushforward]

end

end HodgeConjecture.SchemeCycles
