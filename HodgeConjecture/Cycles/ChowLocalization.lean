module

public import HodgeConjecture.Cycles.OpenClosedLocalization
public import HodgeConjecture.Cycles.PrincipalRelationLifting
public import HodgeConjecture.Cycles.RationalChowPushforward

@[expose] public section

/-!
# Localization on the existing integral and rational Chow groups

An open-zero Chow class has a representative whose restriction is a
principal relation. Lift that relation, subtract it from the representative,
and apply cycle exactness. This proves kernel equals boundary image on the
actual Chow quotients. Open surjectivity was already proved.

This formalizes Stacks Lemma 42.19.3 (02RX), with a supplied dimension
function and Noetherian ambient scheme:
https://stacks.math.columbia.edu/tag/02RX.
The open and closed sources inherit Noetherianity. No injectivity of closed
Chow pushforward or of integral-to-rational coefficient extension is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem quotient_range_eq_ker
    {R B C D : Type*} [Ring R]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D]
    (i : B →ₗ[R] C) (r : C →ₗ[R] D)
    (RB : Submodule R B) (RC : Submodule R C) (RD : Submodule R D)
    (hi : RB ≤ RC.comap i) (hr : RC ≤ RD.comap r)
    (hexact : LinearMap.range i = LinearMap.ker r) (hrel : RC.map r = RD) :
    LinearMap.range (RB.mapQ RC i hi) = LinearMap.ker (RC.mapQ RD r hr) := by
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨b, rfl⟩ := RB.mkQ_surjective b
    have hb : i b ∈ LinearMap.range i := ⟨b, rfl⟩
    rw [hexact] at hb
    change RD.mkQ (r (i b)) = 0
    rw [show r (i b) = 0 from hb, map_zero]
  · intro hz
    obtain ⟨c, rfl⟩ := RC.mkQ_surjective z
    change RD.mkQ (r c) = 0 at hz
    have hm : r c ∈ RD := (Submodule.Quotient.mk_eq_zero RD).mp hz
    rw [← hrel] at hm
    obtain ⟨a, ha, har⟩ := hm
    have hc : c - a ∈ LinearMap.ker r := by
      rw [LinearMap.mem_ker, map_sub, har, sub_self]
    rw [← hexact] at hc
    obtain ⟨b, hb⟩ := hc
    refine ⟨RB.mkQ b, ?_⟩
    change RC.mkQ (i b) = RC.mkQ c
    have ha0 : RC.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero RC).mpr ha
    rw [hb, map_sub, ha0, sub_zero]

/-- The source of an actual closed immersion inherits Noetherianity from
its target, through its image isomorphism and closed point embedding. -/
theorem closedImmersion_isNoetherian {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] : IsNoetherian Z := by
  letI := idealSubscheme_isNoetherian i.ker
  exact {
    toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion i.toImage
    toCompactSpace := i.isClosedEmbedding.compactSpace }

/-- The integral Chow localization sequence is exact for actual
complementary open and closed immersions. -/
theorem range_chowClosedPushforward_eq_ker_chowOpenRestriction
    {Z U X : Scheme.{u}} [IsNoetherian X] (δ : DimensionFunction X)
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (n : ℤ) :
    letI := closedImmersion_isNoetherian i
    letI := openImmersion_isNoetherian j
    LinearMap.range (chowClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
      (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n) =
      LinearMap.ker (chowOpenRestriction δ j n) := by
  letI := closedImmersion_isNoetherian i
  letI := openImmersion_isNoetherian j
  exact quotient_range_eq_ker _ _ _ _ _ _ _
    (range_gradedClosedPushforward_eq_ker_gradedOpenRestriction ℤ δ i j hcomp n)
    (principalRelations_map_openRestriction δ j n)

/-- Rational Chow exactness follows directly from rational relation lifts
and cycle exactness, without a flatness or rationalization-injectivity premise. -/
theorem range_rationalChowClosedPushforward_eq_ker_rationalChowOpenRestriction
    {Z U X : Scheme.{u}} [IsNoetherian X] (δ : DimensionFunction X)
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (n : ℤ) :
    letI := closedImmersion_isNoetherian i
    letI := openImmersion_isNoetherian j
    LinearMap.range (rationalChowClosedImmersionPushforward
      (δ.comapClosedImmersion i) δ i
      (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n) =
      LinearMap.ker (rationalChowOpenRestriction δ j n) := by
  letI := closedImmersion_isNoetherian i
  letI := openImmersion_isNoetherian j
  exact quotient_range_eq_ker _ _ _ _ _ _ _
    (range_gradedClosedPushforward_eq_ker_gradedOpenRestriction ℚ δ i j hcomp n)
    (rationalPrincipalRelations_map_openRestriction δ j n)

/-- The reduced complement supplies the integral exact sequence, with no
additional support or relation hypothesis. -/
theorem range_chowOpenComplementPushforward_eq_ker
    {U X : Scheme.{u}} [IsNoetherian X] (δ : DimensionFunction X)
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    LinearMap.range (chowClosedImmersionPushforward
      (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
      (openComplementIdeal j).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n) =
      LinearMap.ker (chowOpenRestriction δ j n) :=
  range_chowClosedPushforward_eq_ker_chowOpenRestriction δ _ j (range_openComplement j) n

/-- The reduced complement supplies the rational exact sequence on the
existing Chow groups and their actual geometric maps. -/
theorem range_rationalChowOpenComplementPushforward_eq_ker
    {U X : Scheme.{u}} [IsNoetherian X] (δ : DimensionFunction X)
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    LinearMap.range (rationalChowClosedImmersionPushforward
      (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
      (openComplementIdeal j).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n) =
      LinearMap.ker (rationalChowOpenRestriction δ j n) :=
  range_rationalChowClosedPushforward_eq_ker_rationalChowOpenRestriction
    δ _ j (range_openComplement j) n

end

end HodgeConjecture.SchemeCycles
