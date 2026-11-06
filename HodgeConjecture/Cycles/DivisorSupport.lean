module

public import HodgeConjecture.Cycles.PointSupport
public import HodgeConjecture.Cycles.SupportCodimension
public import HodgeConjecture.Cycles.SchemeLocalOrder
public import HodgeConjecture.Cycles.ClosedImmersionPushforward

@[expose] public section

/-!
# Prime divisors as actual integral closed supports

Codimension is measured by chains of irreducible closed subsets containing
the actual support. The stalk-dimension theorem identifies the codimension-one
subtype of the existing integral cycle generators with `DivisorPoint`.
Scheme isomorphisms transport these generators by the existing ideal-sheaf
image operation and preserve their signed local coefficients.

This is a support identification, not a finite-support theorem or a new
cycle module. Principal-divisor assembly and rational equivalence come later.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}}

/-- The actual closed support, with its proved irreducibility. -/
def integralSupport (Z : IntegralClosedSubscheme X) :
    TopologicalSpace.IrreducibleCloseds X where
  carrier := Z.val.support
  isClosed' := Z.val.support.isClosed
  isIrreducible' := (ambientGenericPoint_isGenericPoint Z).isIrreducible

@[simp]
theorem integralSupport_coe (Z : IntegralClosedSubscheme X) :
    (integralSupport Z : Set X) = Z.val.support := rfl

theorem integralSupport_eq_pointClosure (Z : IntegralClosedSubscheme X) :
    integralSupport Z = pointClosureOrderIso X (ambientGenericPoint Z) := by
  ext x
  change x ∈ Z.val.support ↔ x ∈ closure {ambientGenericPoint Z}
  rw [(ambientGenericPoint_isGenericPoint Z).def]
  rfl

/-- Codimension of the actual integral support: lengths of chains of
irreducible closed supersets, not a difference of absolute dimensions. -/
def supportCodimension (Z : IntegralClosedSubscheme X) : ℕ∞ :=
  Order.coheight (integralSupport Z)

/-- Topological support codimension equals the dimension of its ambient
generic-point local ring. No finiteness or integrality of `X` is assumed. -/
theorem supportCodimension_eq_stalkDim (Z : IntegralClosedSubscheme X) :
    (supportCodimension Z : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk (ambientGenericPoint Z)) := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight]
  exact point_coheight_eq_stalkDim X (ambientGenericPoint Z)

theorem supportCodimension_eq_one_iff (Z : IntegralClosedSubscheme X) :
    supportCodimension Z = 1 ↔
      ringKrullDim (X.presheaf.stalk (ambientGenericPoint Z)) = 1 := by
  rw [← supportCodimension_eq_stalkDim]
  exact WithBot.coe_inj.symm

/-- Prime divisors are a subtype of the existing actual integral cycle
generators, selected by their topological codimension. -/
def PrimeDivisor (X : Scheme.{u}) :=
  {Z : IntegralClosedSubscheme X // supportCodimension Z = 1}

/-- Taking reduced closure and taking the ambient generic point restrict
to mutually inverse maps in codimension one. -/
def divisorPointEquivPrimeDivisor (X : Scheme.{u}) :
    DivisorPoint X ≃ PrimeDivisor X where
  toFun x := ⟨pointSupport X x.val, (supportCodimension_eq_one_iff _).mpr (by
    rw [ambientGenericPoint_pointSupport]
    exact x.property)⟩
  invFun Z := ⟨ambientGenericPoint Z.val,
    (supportCodimension_eq_one_iff Z.val).mp Z.property⟩
  left_inv x := Subtype.ext (ambientGenericPoint_pointSupport X x.val)
  right_inv Z := Subtype.ext (pointSupport_ambientGenericPoint Z.val)

@[simp]
theorem divisorPointEquivPrimeDivisor_val (x : DivisorPoint X) :
    (divisorPointEquivPrimeDivisor X x).val = pointSupport X x.val := rfl

@[simp]
theorem divisorPointEquivPrimeDivisor_symm_val (Z : PrimeDivisor X) :
    ((divisorPointEquivPrimeDivisor X).symm Z).val = ambientGenericPoint Z.val := rfl

/-- The ambient generic point is carried by the actual support-to-image
isomorphism, also when only the support composite is a closed immersion. -/
theorem ambientGenericPoint_closedImageSubscheme (f : X ⟶ Y)
    (Z : IntegralClosedSubscheme X) [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    ambientGenericPoint (closedImageSubscheme f Z) = f.base (ambientGenericPoint Z) := by
  letI := Z.property
  letI := closedImageSubscheme_isIntegral f Z
  change (Z.val.map f).subschemeι.base (genericPoint (Z.val.map f).subscheme) =
    f.base (Z.val.subschemeι.base (genericPoint Z.val.subscheme))
  rw [← closedImageSubschemeIso_genericPoint f Z]
  change ((closedImageSubschemeIso f Z).hom ≫ (Z.val.map f).subschemeι).base
    (genericPoint Z.val.subscheme) = _
  rw [closedImageSubschemeIso_hom_subschemeι]
  rfl

/-- The existing closed-image operation agrees with reduced point closure. -/
theorem closedImage_pointSupport (f : X ⟶ Y) (x : X)
    [IsClosedImmersion ((pointSupport X x).val.subschemeι ≫ f)] :
    closedImageSubscheme f (pointSupport X x) = pointSupport Y (f.base x) := by
  rw [← pointSupport_ambientGenericPoint (closedImageSubscheme f (pointSupport X x)),
    ambientGenericPoint_closedImageSubscheme, ambientGenericPoint_pointSupport]

/-- Support codimension is preserved by scheme isomorphisms. -/
theorem supportCodimension_iso (e : X ≅ Y) (Z : IntegralClosedSubscheme X) :
    supportCodimension (closedImageSubscheme e.hom Z) = supportCodimension Z := by
  apply WithBot.coe_injective
  rw [supportCodimension_eq_stalkDim, ambientGenericPoint_closedImageSubscheme,
    stalkDimension_iso, supportCodimension_eq_stalkDim]

/-- The existing point equivalence, expressed on its actual prime supports. -/
def primeDivisorEquiv (e : X ≅ Y) : PrimeDivisor X ≃ PrimeDivisor Y :=
  (divisorPointEquivPrimeDivisor X).symm.trans
    ((divisorPointEquiv e).trans (divisorPointEquivPrimeDivisor Y))

/-- Prime-divisor transport is literally the existing scheme-theoretic image. -/
theorem primeDivisorEquiv_val (e : X ≅ Y) (Z : PrimeDivisor X) :
    (primeDivisorEquiv e Z).val = closedImageSubscheme e.hom Z.val := by
  change pointSupport Y (e.hom.base (ambientGenericPoint Z.val)) = _
  rw [← ambientGenericPoint_closedImageSubscheme,
    pointSupport_ambientGenericPoint]

/-- A finite-cycle generator transports by the already constructed pushforward. -/
theorem closedImmersionPushforward_pointSupport (R : Type v) [Semiring R]
    (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    closedImmersionPushforward R f (fundamentalCycle R (pointSupport X x)) =
      fundamentalCycle R (pointSupport Y (f.base x)) := by
  rw [closedImmersionPushforward_fundamentalCycle, closedImage_pointSupport]

/-- The local coefficient on a prime support reuses the unique existing order. -/
def primeDivisorOrder (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (Z : PrimeDivisor X) (f : X.functionFieldˣ) : ℤ :=
  divisorOrder X ((divisorPointEquivPrimeDivisor X).symm Z) f

@[simp]
theorem primeDivisorOrder_pointSupport [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (f : X.functionFieldˣ) :
    primeDivisorOrder X (divisorPointEquivPrimeDivisor X x) f = divisorOrder X x f := by
  simp [primeDivisorOrder]

/-- The coefficient comparison now holds on actual integral closed supports. -/
theorem primeDivisorOrder_iso [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (Z : PrimeDivisor X) (f : Y.functionFieldˣ) :
    primeDivisorOrder X Z (Units.map (functionFieldEquiv e).toMonoidHom f) =
      primeDivisorOrder Y (primeDivisorEquiv e Z) f := by
  simpa [primeDivisorOrder, primeDivisorEquiv] using
    divisorOrder_iso e ((divisorPointEquivPrimeDivisor X).symm Z) f

end

end HodgeConjecture.SchemeCycles
