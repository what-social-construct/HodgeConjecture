import HodgeConjecture.Cycles.AffineDimensionFunction
import HodgeConjecture.Cycles.DimensionFunctionRestriction
import HodgeConjecture.Cycles.FiniteTypeSchemeDimension
import HodgeConjecture.Cycles.CycleDegree

/-!
# Dimension functions on actual affine schemes over a field

An affine scheme with a locally finite-type structural morphism to the
spectrum of a field has an actual dimension function: integer point
height. The structural morphism supplies the finite-type algebra on
global sections. The dimension-function laws are transported from its
spectrum through the canonical scheme isomorphism, using the existing
closed-immersion restriction for that isomorphism.

The value at the ambient generic point of an integral closed support
therefore records its actual topological Krull dimension. No ambient
integrality, reducedness or normality is assumed, and the empty affine
scheme is allowed. This is an affine construction, not an assertion of
height invariance under arbitrary open immersions or chartwise gluing.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

private theorem point_height_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    Order.height (e.hom.base x) = Order.height x := by
  apply WithBot.coe_injective
  rw [point_height_eq_supportDim, point_height_eq_supportDim,
    ← closedImage_pointSupport e.hom x]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (closedImageSubschemeIso e.hom (pointSupport X x))).isHomeomorph).symm

private theorem affine_pointHeight_dimensionLaws
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    StrictMono (fun x : X ↦ ((Order.height x).toNat : ℤ)) ∧
      ∀ {x y : X}, x ⋖ y →
        ((Order.height y).toNat : ℤ) = ((Order.height x).toNat : ℤ) + 1 := by
  let q : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of k) := X.isoSpec.inv ≫ p
  haveI : LocallyOfFiniteType q := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective q
  change Spec.map φ = q at hφ
  have h : RingHom.FiniteType φ.hom := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  algebraize [φ.hom]
  let δ := (DimensionFunction.ofSpecFiniteType k Γ(X, ⊤)).comapClosedImmersion
    X.isoSpec.hom
  have hδ (x : X) : δ x = ((Order.height x).toNat : ℤ) := by
    change DimensionFunction.ofSpecFiniteType k Γ(X, ⊤) (X.isoSpec.hom.base x) = _
    rw [DimensionFunction.ofSpecFiniteType_eq_pointHeight, point_height_iso]
  constructor
  · intro x y hxy
    simpa only [hδ] using δ.strictMono hxy
  · intro x y hxy
    simpa only [hδ] using δ.map_covBy hxy

/-- Integer point height is a dimension function on an actual affine
scheme locally of finite type over a field. The structural morphism,
not a separately supplied sections algebra or grading law, is the input. -/
def DimensionFunction.ofAffineLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    DimensionFunction X where
  toFun x := (Order.height x).toNat
  strictMono := (affine_pointHeight_dimensionLaws k X p).1
  map_covBy := (affine_pointHeight_dimensionLaws k X p).2

/-- The constructor retains literal integer point height. -/
@[simp]
theorem DimensionFunction.ofAffineLocallyOfFiniteType_apply
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    ofAffineLocallyOfFiniteType k X p x = ((Order.height x).toNat : ℤ) := rfl

/-- Every value of this affine dimension function is nonnegative. -/
theorem DimensionFunction.ofAffineLocallyOfFiniteType_nonneg
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    0 ≤ ofAffineLocallyOfFiniteType k X p x := Int.natCast_nonneg _

/-- The degree of an actual integral closed support is its actual finite
Krull dimension, without truncating any infinite value. -/
theorem supportDegree_ofAffineLocallyOfFiniteType_eq_iff
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofAffineLocallyOfFiniteType k X p) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  have hfin := affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType k X p
  have h := point_height_toNat_eq X hfin (ambientGenericPoint W)
  rw [pointSupport_ambientGenericPoint] at h
  rw [← h]
  change ((Order.height (ambientGenericPoint W)).toNat : ℤ) = (n : ℤ) ↔
    ((Order.height (ambientGenericPoint W)).toNat : WithBot ℕ∞) = (n : WithBot ℕ∞)
  norm_cast

/-- Over nontrivial coefficients, homogeneity of a fundamental cycle
is exactly the dimension condition on its actual closed carrier. -/
theorem fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type v) [Semiring R] [Nontrivial R]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈
        cyclesOfDegree R (DimensionFunction.ofAffineLocallyOfFiniteType k X p) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  rw [fundamentalCycle_mem_cyclesOfDegree_iff,
    supportDegree_ofAffineLocallyOfFiniteType_eq_iff]

end

end HodgeConjecture.SchemeCycles
