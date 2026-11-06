module

public import HodgeConjecture.Cycles.Basic
public import HodgeConjecture.Cycles.ResidueDegree
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Finite-cycle pushforward along closed immersions

An integral support whose map into the target is a closed immersion is
isomorphic to its actual scheme-theoretic image. Its image cycle therefore
has coefficient one. This supportwise construction does not require the
ambient morphism to be proper or a closed immersion.

When the ambient morphism itself is a closed immersion, every integral
support satisfies this condition. Linear extension gives pushforward on
the existing finite, ungraded cycle module, compatibly with identities
and composition. No rational-equivalence quotient or intersection product
is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y T : Scheme.{u}} (f : X ⟶ Y)

/-- A support that is closed in the target is isomorphic to its actual
scheme-theoretic image, even if the ambient map is not proper. -/
def closedImageSubschemeIso (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    Z.val.subscheme ≅ (Z.val.map f).subscheme :=
  asIso (Z.val.subschemeι ≫ f).toImage

@[reassoc (attr := simp)]
theorem closedImageSubschemeIso_hom_subschemeι (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    (closedImageSubschemeIso f Z).hom ≫ (Z.val.map f).subschemeι =
      Z.val.subschemeι ≫ f :=
  (Z.val.subschemeι ≫ f).toImage_imageι

/-- The actual support-to-image map induces degree one on residue fields,
in particular at the generic point of the integral support. -/
theorem closedImageSubschemeIso_residueDegree (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] (x : Z.val.subscheme) :
    let i := (closedImageSubschemeIso f Z).hom
    letI : Algebra ((Z.val.map f).subscheme.residueField (i.base x))
        (Z.val.subscheme.residueField x) :=
      (i.residueFieldMap x).hom.toAlgebra
    Module.finrank ((Z.val.map f).subscheme.residueField (i.base x))
      (Z.val.subscheme.residueField x) = 1 :=
  residueFieldMap_finrank_of_isIso (closedImageSubschemeIso f Z).hom x

/-- The actual image ideal defines an integral closed subscheme. -/
theorem closedImageSubscheme_isIntegral (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    IsIntegral (Z.val.map f).subscheme := by
  letI := Z.property
  exact isIntegral_of_iso (closedImageSubschemeIso f Z)

/-- The support-to-image isomorphism sends the actual generic point to the
actual generic point, as needed for the cycle pushforward degree. -/
theorem closedImageSubschemeIso_genericPoint (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    letI := Z.property
    letI := closedImageSubscheme_isIntegral f Z
    (closedImageSubschemeIso f Z).hom.base
        (genericPoint Z.val.subscheme) =
      genericPoint (Z.val.map f).subscheme := by
  letI := Z.property
  letI := closedImageSubscheme_isIntegral f Z
  exact genericPoint_eq_of_isOpenImmersion (closedImageSubschemeIso f Z).hom

/-- The integral image support, using the actual mapped ideal sheaf. -/
def closedImageSubscheme (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] : IntegralClosedSubscheme Y :=
  ⟨Z.val.map f, closedImageSubscheme_isIntegral f Z⟩

@[simp]
theorem closedImageSubscheme_val (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    (closedImageSubscheme f Z).val = Z.val.map f := rfl

variable (R : Type v) [Semiring R]

/-- The image cycle of one support that maps by a closed immersion. -/
def closedImageCycle (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] : Cycles Y R :=
  fundamentalCycle R (closedImageSubscheme f Z)

/-- The coefficient in the image cycle is the degree of the actual residue
extension. A support-to-image isomorphism makes this degree equal to one. -/
theorem closedImageCycle_eq_residueDegree_smul (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] (x : Z.val.subscheme) :
    let i := (closedImageSubschemeIso f Z).hom
    letI : Algebra ((Z.val.map f).subscheme.residueField (i.base x))
        (Z.val.subscheme.residueField x) :=
      (i.residueFieldMap x).hom.toAlgebra
    closedImageCycle f R Z =
      Module.finrank ((Z.val.map f).subscheme.residueField (i.base x))
        (Z.val.subscheme.residueField x) •
          fundamentalCycle R (closedImageSubscheme f Z) := by
  let i := (closedImageSubschemeIso f Z).hom
  letI : Algebra ((Z.val.map f).subscheme.residueField (i.base x))
      (Z.val.subscheme.residueField x) :=
    (i.residueFieldMap x).hom.toAlgebra
  dsimp only
  rw [closedImageSubschemeIso_residueDegree f Z x, one_smul]
  rfl

/-- A supplied equality of actual image ideals identifies the image cycle. -/
theorem closedImageCycle_of_map_eq (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)]
    (W : IntegralClosedSubscheme Y) (h : Z.val.map f = W.val) :
    closedImageCycle f R Z = fundamentalCycle R W :=
  congrArg (fundamentalCycle R) (Subtype.ext h)

/-- Pushforward on actual finite cycles along a closed immersion. -/
def closedImmersionPushforward (R : Type v) [Semiring R]
    (f : X ⟶ Y) [IsClosedImmersion f] : Cycles X R →ₗ[R] Cycles Y R :=
  Finsupp.linearCombination R (fun Z ↦ closedImageCycle f R Z)

@[simp]
theorem closedImmersionPushforward_single [IsClosedImmersion f]
    (Z : IntegralClosedSubscheme X) (r : R) :
    closedImmersionPushforward R f (Finsupp.single Z r) =
      r • closedImageCycle f R Z := by
  simp [closedImmersionPushforward]

@[simp]
theorem closedImmersionPushforward_fundamentalCycle [IsClosedImmersion f]
    (Z : IntegralClosedSubscheme X) :
    closedImmersionPushforward R f (fundamentalCycle R Z) =
      fundamentalCycle R (closedImageSubscheme f Z) := by
  simp [fundamentalCycle, closedImageCycle]

/-- Identification of pushforward with a specified actual integral image. -/
theorem closedImmersionPushforward_fundamentalCycle_of_map_eq
    [IsClosedImmersion f] (Z : IntegralClosedSubscheme X)
    (W : IntegralClosedSubscheme Y) (h : Z.val.map f = W.val) :
    closedImmersionPushforward R f (fundamentalCycle R Z) =
      fundamentalCycle R W := by
  rw [closedImmersionPushforward_fundamentalCycle]
  exact congrArg (fundamentalCycle R) (Subtype.ext h)

@[simp]
theorem closedImageCycle_id (Z : IntegralClosedSubscheme X) :
    closedImageCycle (𝟙 X) R Z = fundamentalCycle R Z := by
  exact closedImageCycle_of_map_eq (𝟙 X) R Z Z (by simp)

@[simp]
theorem closedImmersionPushforward_id :
    closedImmersionPushforward R (𝟙 X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro Z r
  simp [fundamentalCycle, Finsupp.smul_single]

/-- Actual scheme-theoretic images give functorial cycle pushforward. -/
theorem closedImmersionPushforward_comp [IsClosedImmersion f]
    (g : Y ⟶ T) [IsClosedImmersion g] :
    (closedImmersionPushforward R g).comp (closedImmersionPushforward R f) =
      closedImmersionPushforward R (f ≫ g) := by
  apply Finsupp.lhom_ext
  intro Z r
  simp only [LinearMap.comp_apply, closedImmersionPushforward_single, map_smul]
  congr 1
  change closedImmersionPushforward R g
    (fundamentalCycle R (closedImageSubscheme f Z)) = _
  rw [closedImmersionPushforward_fundamentalCycle]
  exact congrArg (fundamentalCycle R) (Subtype.ext (by
    simp only [closedImageSubscheme_val, Scheme.IdealSheafData.map_comp]))

end

end HodgeConjecture.SchemeCycles
