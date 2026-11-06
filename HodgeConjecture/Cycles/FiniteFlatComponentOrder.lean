module

public import HodgeConjecture.Cycles.ComponentLocalLength
public import HodgeConjecture.Cycles.FlatComponentFunction
public import HodgeConjecture.Cycles.FiniteDivisorPoints
public import HodgeConjecture.Cycles.PrincipalRelations
public import HodgeConjecture.Cycles.OpenClosedLocalization

@[expose] public section

/-! The principal-divisor coefficient on an actual reduced component is
the corresponding difference of colengths in the original ambient stalk. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The principal divisor on an existing reduced source component, pushed into the
original ambient cycle module through its original closed inclusion. -/
def flatComponentPrincipalDivisor {X Y : Scheme.{u}} [IsNoetherian X] [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] (W : irreducibleComponents X) (g : Y.functionFieldˣ) :
    Cycles X ℤ := by
  letI := (pointSupport X W.2.1.genericPoint).property
  exact ambientPrincipalDivisor (pointSupport X W.2.1.genericPoint)
    (Units.map (flatComponentFunctionFieldMap f W).hom.toMonoidHom g)

/-- The original component divisor is homogeneous in the existing dimension grading. -/
theorem flatComponentPrincipalDivisor_mem_cyclesOfDegree
    {X Y : Scheme.{u}} [IsNoetherian X] [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (δ : DimensionFunction X) (W : irreducibleComponents X) (g : Y.functionFieldˣ) :
    flatComponentPrincipalDivisor f W g ∈ cyclesOfDegree ℤ δ (δ W.2.1.genericPoint - 1) := by
  letI := (pointSupport X W.2.1.genericPoint).property
  simpa only [flatComponentPrincipalDivisor, ambientPrincipalDivisor, supportDegree,
    ambientGenericPoint_pointSupport] using
    principalDivisor_closedSupport_mem_cyclesOfDegree δ (pointSupport X W.2.1.genericPoint)
      (Units.map (flatComponentFunctionFieldMap f W).hom.toMonoidHom g)

theorem flatComponent_principalDivisor_apply_fraction
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X)
    (hy : ringKrullDim (Y.presheaf.stalk (f.base x)) = 1)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)})
    (g : Y.functionFieldˣ) (a b : Y.presheaf.stalk (f.base x))
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = (g : Y.functionField)) :
    letI := (pointSupport X W.1.2.1.genericPoint).property
    ambientPrincipalDivisor (pointSupport X W.1.2.1.genericPoint)
        (Units.map (flatComponentFunctionFieldMap f W.1).hom.toMonoidHom g)
        (pointSupport X x) =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ (Ideal.span {(f.stalkMap x).hom a} ⊔
          (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ (Ideal.span {(f.stalkMap x).hom b} ⊔
          (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal))).toNat : ℤ) := by
  let Z := pointSupport X W.1.2.1.genericPoint
  letI := Z.property
  letI : IsNoetherian Z.val.subscheme := idealSubscheme_isNoetherian Z.val
  let h := Z.val.subschemeι ≫ f
  letI : IsDominant h := pointSupport_component_isDominant_comp f W.1
  let z := componentPoint x W
  have hz : ringKrullDim (Z.val.subscheme.presheaf.stalk z) = 1 := by
    rw [stalkDimension_finite_dominant k p h z]
    exact hy
  let u := Units.map (functionFieldMapOfDominant h).hom.toMonoidHom g
  have hcoeff : ambientPrincipalDivisor Z u (pointSupport X x) =
      principalDivisor Z.val.subscheme u (pointSupport Z.val.subscheme z) := by
    have he : closedImageSubscheme Z.val.subschemeι
        (pointSupport Z.val.subscheme z) = pointSupport X x :=
      closedImage_pointSupport Z.val.subschemeι z
    change closedImmersionPushforward ℤ Z.val.subschemeι _ (pointSupport X x) = _
    rw [← he, closedImmersionPushforward_apply_image]
  change ambientPrincipalDivisor Z u (pointSupport X x) = _
  rw [hcoeff]
  have hprincipal : principalDivisor Z.val.subscheme u (pointSupport Z.val.subscheme z) =
      divisorOrder Z.val.subscheme ⟨z, hz⟩ u :=
    (principalDivisor_apply_prime Z.val.subscheme u
      (divisorPointEquivPrimeDivisor Z.val.subscheme ⟨z, hz⟩)).trans
        (primeDivisorOrder_pointSupport ⟨z, hz⟩ u)
  rw [hprincipal]
  have hg' : Units.mk0 (algebraMap (Y.presheaf.stalk (h.base z)) Y.functionField a)
        (by simpa only [map_zero] using
          (IsFractionRing.injective (Y.presheaf.stalk (h.base z)) Y.functionField).ne ha) /
      Units.mk0 (algebraMap (Y.presheaf.stalk (h.base z)) Y.functionField b)
        (by simpa only [map_zero] using
          (IsFractionRing.injective (Y.presheaf.stalk (h.base z)) Y.functionField).ne hb) = g :=
    Units.ext hg
  have horder := divisorOrder_dominant_fraction h ⟨z, hz⟩ a b ha hb
  rw [hg'] at horder
  rw [horder]
  have hmap (v : Y.presheaf.stalk (f.base x)) :
      (h.stalkMap z).hom v =
        (Z.val.subschemeι.stalkMap z).hom ((f.stalkMap x).hom v) := by
    exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
      (Scheme.Hom.stalkMap_comp Z.val.subschemeι f z)) v
  rw [hmap a, hmap b, ← componentPoint_principal_quotient_length x W ((f.stalkMap x).hom a),
    ← componentPoint_principal_quotient_length x W ((f.stalkMap x).hom b)]

end

end HodgeConjecture.SchemeCycles
