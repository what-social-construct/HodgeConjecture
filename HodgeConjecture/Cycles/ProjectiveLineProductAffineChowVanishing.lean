module

public import HodgeConjecture.Cycles.UFDChowVanishing
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension
public import HodgeConjecture.Cycles.OpenGrading
public import HodgeConjecture.Geometry.ProjectiveLineProductAffineDimension
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The actual affine product chart has no divisor Chow classes

The chart coordinate ring is a two-variable polynomial ring over the
field. The affine UFD principal-divisor calculation therefore kills
every codimension-one Chow class on the actual chart used in product
localization.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.ProjectiveLineProductAffineChowVanishing

open AlgebraicGeometry CategoryTheory SchemeCycles TensorProduct
open HodgeConjecture.ProjectiveLineProductChow
open HodgeConjecture.ProjectiveLineProductFiberCodimension

noncomputable section

universe u

variable (k : Type u) [Field k]

abbrev coordinateRing := Polynomial k ⊗[k] Polynomial k

private instance coordinateRing_ufd :
    UniqueFactorizationMonoid (coordinateRing k) :=
  (projectiveLineAffineProductRingEquiv k).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

instance coordinateRing_isNoetherian :
    IsNoetherianRing (coordinateRing k) :=
  Algebra.FiniteType.isNoetherianRing k (coordinateRing k)

abbrev chartScheme : Scheme.{u} := Spec (.of (coordinateRing k))

instance chartScheme_isNoetherian : IsNoetherian (chartScheme k) := by
  unfold chartScheme
  infer_instance

private theorem chart_generic_degree_two
    (p : chartScheme k ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p
      (genericPoint (chartScheme k)) = 2 := by
  let δ := DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p
  have htop : topologicalKrullDim (chartScheme k) = (2 : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (coordinateRing k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      projectiveLineAffineProduct_ringKrullDim]
  have hdim := integral_topologicalKrullDim_eq_ofLocallyOfFiniteType
    k (chartScheme k) p
  rw [htop] at hdim
  have hnat : (δ (genericPoint (chartScheme k))).toNat = 2 := by
    exact_mod_cast hdim.symm
  have hnonneg := DimensionFunction.ofLocallyOfFiniteType_nonneg
    k (chartScheme k) p (genericPoint (chartScheme k))
  calc
    δ (genericPoint (chartScheme k)) =
        ((δ (genericPoint (chartScheme k))).toNat : ℤ) :=
      (Int.toNat_of_nonneg hnonneg).symm
    _ = 2 := by exact_mod_cast hnat

private theorem chart_degree_one_codimension_one
    (p : chartScheme k ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme (chartScheme k))
    (hW : supportDegree
      (DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p) W = 1) :
    supportCodimension W = 1 := by
  let δ := DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p
  have hgeneric : δ (genericPoint (chartScheme k)) = 2 :=
    chart_generic_degree_two k p
  apply (supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
    k (chartScheme k) p W 1).mp
  change supportDegree δ W = δ (genericPoint (chartScheme k)) - (1 : ℤ)
  calc
    supportDegree δ W = 1 := hW
    _ = δ (genericPoint (chartScheme k)) - (1 : ℤ) := by
      rw [hgeneric]
      norm_num

/-- The actual affine chart `Spec(k[X] ⊗ k[X])` has zero rational
degree-one Chow group in its structural grading. -/
theorem chart_rationalChowGroup_one_eq_zero
    (p : chartScheme k ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (c : RationalChowGroup
      (DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p) 1) :
    c = 0 :=
  spec_rationalChowGroup_one_eq_zero
    (CommRingCat.of (coordinateRing k))
    (DimensionFunction.ofLocallyOfFiniteType k (chartScheme k) p)
    (chart_generic_degree_two k p)
    (chart_degree_one_codimension_one k p) c

private theorem chart_grading_eq :
    ∀ (j : chartScheme k ⟶ projectiveLineProduct k) [IsOpenImmersion j],
      (dimensionFunction k).comapOpenImmersion j =
        DimensionFunction.ofLocallyOfFiniteType k (chartScheme k)
          (j ≫ projectiveLineProductStructureMorphism k) := by
  intro j _
  unfold dimensionFunction
  unfold DimensionFunction.comapOpenImmersion DimensionFunction.ofLocallyOfFiniteType
  congr 1
  funext x
  exact (DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion
    k (projectiveLineProductStructureMorphism k)
    j x).symm

/-- The actual open-chart grading inherited from `P¹ × P¹` has zero
rational degree-one Chow group. This is the input to product localization. -/
theorem chart_restricted_rationalChowGroup_one_eq_zero
    (j : chartScheme k ⟶ projectiveLineProduct k) [IsOpenImmersion j]
    (c : RationalChowGroup
      ((dimensionFunction k).comapOpenImmersion j) 1) :
    c = 0 := by
  let p : chartScheme k ⟶ Spec (.of k) :=
    j ≫ projectiveLineProductStructureMorphism k
  have hδ := chart_grading_eq k j
  have hgeneric : ((dimensionFunction k).comapOpenImmersion j)
      (genericPoint (chartScheme k)) = 2 := by
    rw [hδ]
    exact chart_generic_degree_two k p
  have hgrade : ∀ W : IntegralClosedSubscheme (chartScheme k),
      supportDegree ((dimensionFunction k).comapOpenImmersion j) W = 1 →
        supportCodimension W = 1 := by
    intro W hW
    apply chart_degree_one_codimension_one k p W
    rwa [← hδ]
  exact spec_rationalChowGroup_one_eq_zero
    (CommRingCat.of (coordinateRing k))
    ((dimensionFunction k).comapOpenImmersion j) hgeneric hgrade c

end

end HodgeConjecture.ProjectiveLineProductAffineChowVanishing

end
