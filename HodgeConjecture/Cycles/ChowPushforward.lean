module

public import HodgeConjecture.Cycles.PrincipalRelations
public import HodgeConjecture.Cycles.GradedPushforward

@[expose] public section

/-!
# Closed pushforward on actual principal relations and their quotient

Each relation carrier is carried to its actual closed image; its rational
function is transported through the actual support-to-image isomorphism.
The geometric principal-divisor identity proves preservation of generators,
then of their generated submodule. Quotient descent is a consequence of
this proof, not an input. Identity and composition retain the existing
geometric cycle maps. No arbitrary proper pushforward or intersection
product is constructed here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Transport actual relation data to the actual closed image, using the
inverse of the contravariant function-field isomorphism. -/
def PrincipalRelationData.closedImage {X Y : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) : PrincipalRelationData δY n := by
  letI := d.1.val.property
  letI := closedImageSubscheme_isIntegral i d.1.val
  refine ⟨⟨closedImageSubscheme i d.1.val, (hdeg d.1.val).trans d.1.property⟩, ?_⟩
  exact Units.map
    (functionFieldEquiv (closedImageSubschemeIso i d.1.val)).symm.toMonoidHom d.2

/-- The image of a genuine principal generator is the genuine generator
on its image carrier, with its transported rational function. -/
theorem gradedClosedImmersionPushforward_principalRelation
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) :
    gradedClosedImmersionPushforward δX δY i hdeg n (principalRelation δX n d) =
      principalRelation δY n (d.closedImage δX δY i hdeg n) := by
  apply Subtype.ext
  exact closedImmersionPushforward_ambientPrincipalDivisor i d.1.val d.2

/-- Preservation of the actual generated relation submodule follows from
the proved geometric generator identity. -/
theorem principalRelations_le_comap_closedImmersionPushforward
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) :
    principalRelations δX n ≤ (principalRelations δY n).comap
      (gradedClosedImmersionPushforward δX δY i hdeg n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change gradedClosedImmersionPushforward δX δY i hdeg n (principalRelation δX n d) ∈
    principalRelations δY n
  rw [gradedClosedImmersionPushforward_principalRelation]
  exact Submodule.subset_span ⟨d.closedImage δX δY i hdeg n, rfl⟩

/-- Closed pushforward on the quotient by genuine principal relations. -/
def chowClosedImmersionPushforward {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) : ChowGroup δX n →ₗ[ℤ] ChowGroup δY n :=
  (principalRelations δX n).mapQ (principalRelations δY n)
    (gradedClosedImmersionPushforward δX δY i hdeg n)
    (principalRelations_le_comap_closedImmersionPushforward δX δY i hdeg n)

@[simp]
theorem chowClosedImmersionPushforward_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    chowClosedImmersionPushforward δX δY i hdeg n (classMap δX n c) =
      classMap δY n (gradedClosedImmersionPushforward δX δY i hdeg n c) := rfl

/-- For the actual restricted dimension function, degree compatibility
is already proved and no comparison hypothesis is supplied. -/
theorem chowClosedImmersionPushforward_restricted_classMap {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (n : ℤ) (c : cyclesOfDegree ℤ (δ.comapClosedImmersion i) n) :
    chowClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n
        (classMap (δ.comapClosedImmersion i) n c) =
      classMap δ n (gradedClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n c) := rfl

/-- The quotient map for the identity is the identity. -/
theorem chowClosedImmersionPushforward_id (X : Scheme.{u}) [IsNoetherian X]
    (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (closedImageSubscheme (𝟙 X) W) = supportDegree δ W)
    (n : ℤ) :
    chowClosedImmersionPushforward δ δ (𝟙 X) hdeg n = LinearMap.id := by
  apply (principalRelations δ n).quot_hom_ext
  intro c
  change classMap δ n (gradedClosedImmersionPushforward δ δ (𝟙 X) hdeg n c) =
    classMap δ n c
  rw [gradedClosedImmersionPushforward_id, LinearMap.id_apply]

/-- Composition on the quotient follows from geometric cycle composition,
not from a separately declared Chow operation. -/
theorem chowClosedImmersionPushforward_comp {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (hj : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (closedImageSubscheme j W) = supportDegree δY W)
    (hij : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (closedImageSubscheme (i ≫ j) W) = supportDegree δX W)
    (n : ℤ) :
    (chowClosedImmersionPushforward δY δZ j hj n).comp
      (chowClosedImmersionPushforward δX δY i hi n) =
        chowClosedImmersionPushforward δX δZ (i ≫ j) hij n := by
  apply (principalRelations δX n).quot_hom_ext
  intro c
  change classMap δZ n
      (((gradedClosedImmersionPushforward δY δZ j hj n).comp
        (gradedClosedImmersionPushforward δX δY i hi n)) c) =
    classMap δZ n (gradedClosedImmersionPushforward δX δZ (i ≫ j) hij n c)
  rw [gradedClosedImmersionPushforward_comp]

end

end HodgeConjecture.SchemeCycles
