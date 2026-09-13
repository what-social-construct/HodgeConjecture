import HodgeConjecture.Realization.Chow.Examples.SplitChowAlgebra
import HodgeConjecture.Correspondence.Examples.SplitSpanCoproduct
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Option

/-!
# An actual Chow graph block on a point plus a finite split scheme

The encoding is constructed in Chow: add the distinguished point-pair class
to the proper pushforward of the given class along the distinguished source
column. Decoding is the actual flat pullback along that column. Matrix
coordinates calculate these geometric operations and prove idempotence.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

namespace SplitChowTateBlock

open SplitZeroCycles SplitChowCorrespondence Classical
open scoped BigOperators

variable (I : Type) [Fintype I] [DecidableEq I]

/-- The actual proper pushforward along the distinguished source column. -/
def column : Chow ℂ I ℚ →ₗ[ℚ] EndAlgebra ℂ (Option I) :=
  chowPushforward ℂ ℚ (fun i : I ↦ (none, some i))

/-- Point coordinates of the geometric column pushforward. -/
theorem matrix_column (z : Chow ℂ I ℚ) :
    matrixAlgEquiv ℂ (Option I) (column I z) =
      fun output input ↦
        if input = none then output.elim 0 (chowCoordinates ℂ I ℚ z) else 0 := by
  ext output input
  change chowCoordinates ℂ (Option I × Option I) ℚ
    (chowPushforward ℂ ℚ (fun i : I ↦ (none, some i)) z) (input, output) = _
  rw [chowCoordinates_pushforward]
  cases output <;> cases input <;> simp [Prod.mk.injEq]

/-- The actual affine Chow graph block: the distinguished point-pair class
plus the proper pushforward along its lower-left column. -/
def encode (z : Chow ℂ I ℚ) : EndAlgebra ℂ (Option I) :=
  let p : EndAlgebra ℂ (Option I) := pointCorrespondence ℂ none none
  p + column I z

/-- Lower-left decoding is flat pullback along the actual column inclusion. -/
def decode : EndAlgebra ℂ (Option I) →ₗ[ℚ] Chow ℂ I ℚ :=
  chowPullback ℂ ℚ (fun i : I ↦ (none, some i))

/-- The geometric encoding has the expected graph-projector matrix:
the distinguished column is `(1, z)` and every other column is zero. -/
theorem matrix_encode (z : Chow ℂ I ℚ) :
    matrixAlgEquiv ℂ (Option I) (encode I z) =
      fun output input ↦
        if input = none then output.elim 1 (chowCoordinates ℂ I ℚ z) else 0 := by
  unfold encode
  rw [map_add, matrix_column]
  simp only [matrixAlgEquiv_apply, matrixCoordinates_pointCorrespondence]
  ext output input
  cases output <;> cases input <;> simp [Matrix.single]

/-- The geometric decoder extracts the actual lower-left Chow coefficient. -/
@[simp]
theorem coordinates_decode (c : EndAlgebra ℂ (Option I)) (i : I) :
    chowCoordinates ℂ I ℚ (decode I c) i =
      matrixAlgEquiv ℂ (Option I) c (some i) none := by
  exact chowCoordinates_pullback ℂ ℚ (fun i : I ↦ (none, some i)) c i

/-- Decoding the actual graph block recovers the original Chow class. -/
@[simp]
theorem decode_encode (z : Chow ℂ I ℚ) : decode I (encode I z) = z := by
  apply (chowCoordinates ℂ I ℚ).injective
  ext i
  rw [coordinates_decode, matrix_encode]
  rfl

/-- The constructed Chow correspondence is idempotent under actual geometric
correspondence composition. -/
theorem encode_isIdempotent (z : Chow ℂ I ℚ) : IsIdempotentElem (encode I z) := by
  change encode I z * encode I z = encode I z
  apply (matrixAlgEquiv ℂ (Option I)).injective
  rw [map_mul, matrix_encode]
  ext output input
  by_cases h : input = none <;> simp [Matrix.mul_apply, h]

/-- Distinct Chow classes give distinct actual graph correspondences. -/
theorem encode_injective : Function.Injective (encode I) := by
  intro z w h
  simpa only [decode_encode] using congrArg (decode I) h

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SplitPointGeometry

/-- The option-indexed split scheme is the actual coproduct of the
distinguished rational point and the original finite split scheme. -/
def optionSchemeIso :
    scheme ℂ (Option I) ≅ Spec (.of ℂ) ⨿ scheme ℂ I :=
  isoOfEquiv ℂ ((Equiv.optionEquivSumPUnit I).trans (Equiv.sumComm _ _)) ≪≫
    sumSchemeIso ℂ PUnit I ≪≫ coprod.mapIso (singletonIso ℂ) (Iso.refl _)

omit [Fintype I] [DecidableEq I] in
/-- The distinguished point is precisely the first coproduct summand. -/
@[simp, reassoc]
theorem optionSchemeIso_inl_inv :
    coprod.inl ≫ (optionSchemeIso I).inv = pointInclusion ℂ (Option I) none := by
  simp [optionSchemeIso, sumDesc, isoOfEquiv, singletonIso, Function.comp_def]

omit [Fintype I] [DecidableEq I] in
/-- The original split scheme is precisely the second coproduct summand. -/
@[simp, reassoc]
theorem optionSchemeIso_inr_inv :
    coprod.inr ≫ (optionSchemeIso I).inv =
      mapOfFunction ℂ (some : I → Option I) := by
  simp [optionSchemeIso, sumDesc, isoOfEquiv, Function.comp_def]

omit [Fintype I] [DecidableEq I] in
@[simp, reassoc]
theorem pointInclusion_optionSchemeIso :
    pointInclusion ℂ (Option I) none ≫ (optionSchemeIso I).hom = coprod.inl := by
  apply (cancel_mono (optionSchemeIso I).inv).mp
  simp

omit [Fintype I] [DecidableEq I] in
@[simp, reassoc]
theorem mapSome_optionSchemeIso :
    mapOfFunction ℂ (some : I → Option I) ≫ (optionSchemeIso I).hom = coprod.inr := by
  apply (cancel_mono (optionSchemeIso I).inv).mp
  simp

end SplitChowTateBlock

end

end HodgeConjecture
