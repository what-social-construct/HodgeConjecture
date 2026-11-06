module

public import HodgeConjecture.Cycles.FiniteFlatComponentOrder
public import HodgeConjecture.Cycles.FiniteFlatLocalOrder
public import HodgeConjecture.Cycles.EquidimensionalDivisorPoint
public import HodgeConjecture.Cycles.FinitePrincipalDivisor
public import HodgeConjecture.Cycles.FiniteFiberClosedBaseChange

@[expose] public section

/-! Principal-divisor pullback with the original cycle maps and the
actual reduced source components, retaining their nilpotent multiplicities. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- A homogeneous cycle has zero coefficient at a point of a different degree. -/
theorem cycle_apply_point_eq_zero_of_degree_ne {X : Scheme.{u}}
    (δ : DimensionFunction X) (n : ℤ) (c : Cycles X ℤ)
    (hc : c ∈ cyclesOfDegree ℤ δ n) (x : X) (hx : δ x ≠ n) :
    c (pointSupport X x) = 0 := by
  by_contra h
  apply hx
  simpa only [supportDegree, ambientGenericPoint_pointSupport] using
    ((mem_cyclesOfDegree_iff ℤ δ n c).mp hc) (pointSupport X x) h

/-- A component principal divisor has zero coefficient away from that actual component. -/
theorem flatComponentPrincipalDivisor_apply_of_not_mem
    {X Y : Scheme.{u}} [IsNoetherian X] [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (W : irreducibleComponents X) (g : Y.functionFieldˣ) (x : X) (hx : x ∉ (W : Set X)) :
    flatComponentPrincipalDivisor f W g (pointSupport X x) = 0 := by
  let Z := pointSupport X W.2.1.genericPoint
  letI := Z.property
  have hnot : x ∉ Set.range Z.val.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact (Set.ext_iff.mp (pointSupport_component_support W) x).not.mpr hx
  exact closedImmersionPushforward_apply_point_of_not_mem_range ℤ Z.val.subschemeι _ x hnot

/-- At a divisor point of the target with one-dimensional source stalk, the actual
finite flat pullback coefficient is the sum of the actual component principal-divisor
coefficients weighted by the original generic fiber multiplicities. -/
theorem finiteFlat_principalDivisor_apply_eq_components
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X)
    (hy : ringKrullDim (Y.presheaf.stalk (f.base x)) = 1)
    (hx : ringKrullDim (X.presheaf.stalk x) = 1) (g : Y.functionFieldˣ) :
    finiteFiberPullback f ℤ (principalDivisor Y g) (pointSupport X x) =
      ∑ᶠ W : {W : irreducibleComponents X // x ∈ (W : Set X)},
        (finiteFiberMultiplicity f W.1.2.1.genericPoint : ℤ) *
          (letI := (pointSupport X W.1.2.1.genericPoint).property
          ambientPrincipalDivisor (pointSupport X W.1.2.1.genericPoint)
            (Units.map (flatComponentFunctionFieldMap f W.1).hom.toMonoidHom g)
            (pointSupport X x)) := by
  classical
  obtain ⟨a, b, ha, hb, hg⟩ := exists_local_fraction (f.base x) g
  have hgval : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = (g : Y.functionField) :=
    congrArg Units.val hg
  rw [finiteFiberPullback_apply_pointSupport, principalDivisor_apply_point Y g ⟨f.base x, hy⟩]
  have hlocal := finiteFlat_localOrder_fraction_eq_minimalPrime_sum f x hy hx a b ha hb
  rw [hg] at hlocal
  rw [hlocal]
  symm
  apply finsum_eq_of_bijective (irreducibleComponentsEquivMinimalPrimes x)
    (irreducibleComponentsEquivMinimalPrimes x).bijective
  intro W
  rw [flatComponent_principalDivisor_apply_fraction k p f x hy W g a b ha hb hgval,
    component_localized_length x W,
    finiteFiberMultiplicity_over_genericPoint f W.1.2.1.genericPoint
      (map_genericPoint_irreducibleComponent_eq_genericPoint f W.1)]
  rfl

/-- The actual finite flat pullback of a principal divisor is the sum of the actual
component principal divisors, with the original generic fiber multiplicities. -/
theorem finiteFlat_pullback_principalDivisor_eq_sum_components
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (g : Y.functionFieldˣ) :
    finiteFiberPullback f ℤ (principalDivisor Y g) =
      ∑ᶠ W : irreducibleComponents X,
        (finiteFiberMultiplicity f W.2.1.genericPoint : ℤ) •
          flatComponentPrincipalDivisor f W g := by
  classical
  letI : Fintype (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).fintype
  let δX := DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)
  let δY := DimensionFunction.ofLocallyOfFiniteType k Y p
  let n := δY (genericPoint Y)
  have hgenX (W : irreducibleComponents X) : δX W.2.1.genericPoint = n := by
    dsimp only [δX, n]
    rw [DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p f,
      map_genericPoint_irreducibleComponent_eq_genericPoint f W]
  have hgenY (W : irreducibleComponents Y) : δY W.2.1.genericPoint = n := by
    exact congrArg δY (map_genericPoint_irreducibleComponent_eq_genericPoint (𝟙 Y) W)
  have hcompDegree (W : irreducibleComponents X) :
      flatComponentPrincipalDivisor f W g ∈ cyclesOfDegree ℤ δX (n - 1) := by
    rw [← hgenX W]
    exact flatComponentPrincipalDivisor_mem_cyclesOfDegree f δX W g
  have hleftDegree : finiteFiberPullback f ℤ (principalDivisor Y g) ∈
      cyclesOfDegree ℤ δX (n - 1) :=
    finiteFiberPullback_mem_cyclesOfDegree f k ℤ p (n - 1) _
      (principalDivisor_mem_cyclesOfDegree δY g)
  apply Finsupp.ext
  intro Z
  rw [← pointSupport_ambientGenericPoint Z]
  let x := ambientGenericPoint Z
  change finiteFiberPullback f ℤ (principalDivisor Y g) (pointSupport X x) = _
  rw [finsum_eq_sum_of_fintype, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, zsmul_eq_mul]
  rw [← finsum_eq_sum_of_fintype]
  by_cases hx : δX x = n - 1
  · have hdimX := stalkDim_eq_one_of_degree_eq_component_sub_one δX hgenX hx
    have hxy : δY (f.base x) = n - 1 := by
      rw [← DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p f]
      exact hx
    have hdimY := stalkDim_eq_one_of_degree_eq_component_sub_one δY hgenY hxy
    rw [finiteFlat_principalDivisor_apply_eq_components k p f x hdimY hdimX]
    let term (W : irreducibleComponents X) : ℤ :=
      (finiteFiberMultiplicity f W.2.1.genericPoint : ℤ) *
        flatComponentPrincipalDivisor f W g (pointSupport X x)
    change (∑ᶠ W : {W : irreducibleComponents X // x ∈ (W : Set X)}, term W.val) =
      ∑ᶠ W : irreducibleComponents X, term W
    rw [finsum_subtype_eq_finsum_cond]
    apply finsum_congr
    intro W
    by_cases hxW : x ∈ (W : Set X)
    · simp only [hxW, finsum_true]
    · simp only [hxW, finsum_false,
        term, flatComponentPrincipalDivisor_apply_of_not_mem f W g x hxW, mul_zero]
  · rw [cycle_apply_point_eq_zero_of_degree_ne δX (n - 1) _ hleftDegree x hx]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro W
    rw [cycle_apply_point_eq_zero_of_degree_ne δX (n - 1) _ (hcompDegree W) x hx, mul_zero]

end

end HodgeConjecture.SchemeCycles
