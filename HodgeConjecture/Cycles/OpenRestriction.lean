module

public import HodgeConjecture.Cycles.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Open restriction of finitely supported scheme cycles

Restriction is defined on actual integral closed subschemes by pulling back
their ideal sheaves. A nonempty inverse image is an open subscheme of an
integral scheme, hence integral; an empty inverse image contributes zero.
Linear extension gives restriction of the ungraded cycle module.

This construction does not introduce rational equivalence, dimension
grading, or an intersection product. On quasi-compact ambient schemes the
finite-support convention agrees with the usual locally finite cycle sums.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {X U V : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The inverse-image closed subscheme has its actual open map into the
original integral support. -/
def openRestrictionSubschemeMap (Z : IntegralClosedSubscheme X) :
    (Z.val.comap j).subscheme ⟶ Z.val.subscheme :=
  (Z.val.comapIso j).hom ≫ pullback.snd j Z.val.subschemeι

instance openRestrictionSubschemeMap_isOpenImmersion
    (Z : IntegralClosedSubscheme X) :
    IsOpenImmersion (openRestrictionSubschemeMap j Z) := by
  unfold openRestrictionSubschemeMap
  infer_instance

/-- A nonempty open inverse image of an integral support is integral. -/
theorem openRestrictionSubscheme_isIntegral (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    IsIntegral (Z.val.comap j).subscheme := by
  letI := Z.property
  exact isIntegral_of_isOpenImmersion (openRestrictionSubschemeMap j Z)

/-- The actual integral closed support of a nonempty restricted generator. -/
def openRestrictionSubscheme (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] : IntegralClosedSubscheme U :=
  ⟨Z.val.comap j, openRestrictionSubscheme_isIntegral j Z⟩

@[simp]
theorem openRestrictionSubscheme_val (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    (openRestrictionSubscheme j Z).val = Z.val.comap j := rfl

@[simp]
theorem openRestrictionSubscheme_support (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    (openRestrictionSubscheme j Z).val.support =
      Z.val.support.preimage j.continuous := by
  simp

variable (R : Type v) [Semiring R]

/-- Restriction of one integral support, including the empty-intersection case. -/
def openRestrictionGenerator (Z : IntegralClosedSubscheme X) : Cycles U R := by
  classical
  exact if h : Nonempty (Z.val.comap j).subscheme then
    @fundamentalCycle U R _ (@openRestrictionSubscheme X U j _ Z h)
  else 0

@[simp]
theorem openRestrictionGenerator_of_nonempty (Z : IntegralClosedSubscheme X)
    [Nonempty (Z.val.comap j).subscheme] :
    openRestrictionGenerator j R Z =
      fundamentalCycle R (openRestrictionSubscheme j Z) := by
  simp [openRestrictionGenerator,
    show Nonempty (Z.val.comap j).subscheme from inferInstance]

@[simp]
theorem openRestrictionGenerator_of_isEmpty (Z : IntegralClosedSubscheme X)
    [IsEmpty (Z.val.comap j).subscheme] :
    openRestrictionGenerator j R Z = 0 := by
  simp [openRestrictionGenerator]

/-- Open restriction of actual finitely supported, ungraded scheme cycles. -/
def openRestriction (R : Type v) [Semiring R] (j : U ⟶ X) [IsOpenImmersion j] :
    Cycles X R →ₗ[R] Cycles U R :=
  Finsupp.linearCombination R (openRestrictionGenerator j R)

@[simp]
theorem openRestriction_single (Z : IntegralClosedSubscheme X) (r : R) :
    openRestriction R j (Finsupp.single Z r) =
      r • openRestrictionGenerator j R Z := by
  simp [openRestriction]

@[simp]
theorem openRestriction_fundamentalCycle (Z : IntegralClosedSubscheme X) :
    openRestriction R j (fundamentalCycle R Z) =
      openRestrictionGenerator j R Z := by
  simp [fundamentalCycle]

theorem openRestriction_fundamentalCycle_of_nonempty
    (Z : IntegralClosedSubscheme X) [Nonempty (Z.val.comap j).subscheme] :
    openRestriction R j (fundamentalCycle R Z) =
      fundamentalCycle R (openRestrictionSubscheme j Z) := by
  simp

theorem openRestriction_fundamentalCycle_of_isEmpty
    (Z : IntegralClosedSubscheme X) [IsEmpty (Z.val.comap j).subscheme] :
    openRestriction R j (fundamentalCycle R Z) = 0 := by
  simp

/-- A specified equality of actual ideal sheaves identifies the restricted
cycle without exposing the nonemptiness proof in the resulting generator. -/
theorem openRestriction_fundamentalCycle_of_comap_eq
    (Z : IntegralClosedSubscheme X) (W : IntegralClosedSubscheme U)
    (h : Z.val.comap j = W.val) :
    openRestriction R j (fundamentalCycle R Z) = fundamentalCycle R W := by
  letI := W.property
  haveI : Nonempty (Z.val.comap j).subscheme := by
    rw [h]
    infer_instance
  rw [openRestriction_fundamentalCycle_of_nonempty]
  exact congrArg (fundamentalCycle R) (Subtype.ext h)

@[simp]
theorem openRestrictionGenerator_id (Z : IntegralClosedSubscheme X) :
    openRestrictionGenerator (𝟙 X) R Z = fundamentalCycle R Z := by
  letI := Z.property
  haveI : Nonempty (Z.val.comap (𝟙 X)).subscheme := by
    simpa using (inferInstance : Nonempty Z.val.subscheme)
  rw [openRestrictionGenerator_of_nonempty]
  congr 1
  exact Subtype.ext (by simp)

@[simp]
theorem openRestriction_id : openRestriction R (𝟙 X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro Z r
  simp [fundamentalCycle, Finsupp.smul_single]

/-- Restricting an integral generator through two opens gives the same
cycle as restricting along their composite, including both empty cases. -/
theorem openRestrictionGenerator_comp (k : V ⟶ U) [IsOpenImmersion k]
    (Z : IntegralClosedSubscheme X) :
    openRestriction R k (openRestrictionGenerator j R Z) =
      openRestrictionGenerator (k ≫ j) R Z := by
  classical
  by_cases h : Nonempty (Z.val.comap j).subscheme
  · letI := h
    let W := openRestrictionSubscheme j Z
    have hc : Z.val.comap (k ≫ j) = W.val.comap k := by
      simp [W]
    rw [openRestrictionGenerator_of_nonempty,
      openRestriction_fundamentalCycle]
    change openRestrictionGenerator k R W = _
    by_cases hW : Nonempty (W.val.comap k).subscheme
    · letI := hW
      haveI : Nonempty (Z.val.comap (k ≫ j)).subscheme := by
        rw [hc]
        infer_instance
      rw [openRestrictionGenerator_of_nonempty,
        openRestrictionGenerator_of_nonempty]
      exact congrArg (fundamentalCycle R) (Subtype.ext hc.symm)
    · haveI : IsEmpty (W.val.comap k).subscheme := not_nonempty_iff.mp hW
      haveI : IsEmpty (Z.val.comap (k ≫ j)).subscheme := by
        rw [hc]
        infer_instance
      simp
  · haveI : IsEmpty (Z.val.comap j).subscheme := not_nonempty_iff.mp h
    haveI : IsEmpty ((Z.val.comap j).comap k).subscheme :=
      Function.isEmpty
        (((Z.val.comap j).comapIso k).hom ≫
          pullback.snd k (Z.val.comap j).subschemeι).base
    haveI : IsEmpty (Z.val.comap (k ≫ j)).subscheme := by
      simpa only [Scheme.IdealSheafData.comap_comp] using
        (inferInstance : IsEmpty ((Z.val.comap j).comap k).subscheme)
    simp

/-- Open restriction is contravariantly functorial on actual finite cycles. -/
theorem openRestriction_comp (k : V ⟶ U) [IsOpenImmersion k] :
    (openRestriction R k).comp (openRestriction R j) =
      openRestriction R (k ≫ j) := by
  apply Finsupp.lhom_ext
  intro Z r
  simp [openRestrictionGenerator_comp]

end

end HodgeConjecture.SchemeCycles
