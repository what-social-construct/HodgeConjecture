import HodgeConjecture.Cycles.CycleDegree
import HodgeConjecture.Cycles.DimensionFunctionRestriction
import HodgeConjecture.Cycles.PrincipalDivisor

/-!
# Homogeneous principal divisors and their ambient closed images

The existing finite principal-divisor cycle is homogeneous of degree one
less than the generic-point degree for an explicitly supplied dimension
function. The existing closed pushforward preserves the degree computed
by restriction of an ambient dimension function. In particular an actual
integral closed relation carrier gives a degree-one-lower ambient cycle.

Homogeneity is proved from prime codimension, actual generic-point images,
and the finite coefficient formula, not assumed as relation data. This
module constructs no rational-equivalence subgroup or Chow quotient.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- The already-constructed finite principal divisor lies in the
one-lower-degree submodule of the existing integral cycle module. -/
theorem principalDivisor_mem_cyclesOfDegree {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (δ : DimensionFunction X) (f : X.functionFieldˣ) :
    principalDivisor X f ∈ cyclesOfDegree ℤ δ (δ (genericPoint X) - 1) := by
  rw [mem_cyclesOfDegree_iff]
  intro Z hZ
  have hcodim : supportCodimension Z = 1 := by
    by_contra h
    exact hZ (principalDivisor_apply_of_not_prime X f Z h)
  exact supportDegree_primeDivisor δ ⟨Z, hcodim⟩

/-- Existing closed pushforward preserves degree for the actual restricted
dimension function, with no separately supplied degree-compatibility law. -/
theorem closedImmersionPushforward_mem_cyclesOfDegree_comap
    {X Y : Scheme.{u}} (R : Type v) [Semiring R]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R (δ.comapClosedImmersion i) n) :
    closedImmersionPushforward R i c ∈ cyclesOfDegree R δ n :=
  closedImmersionPushforward_mem_cyclesOfDegree R (δ.comapClosedImmersion i) δ
    i n c hc (fun Z ↦ (supportDegree_comapClosedImmersion δ i Z).symm)

/-- The degree of a pushed principal divisor is computed in its integral
source, then carried to the actual ambient image. -/
theorem closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X.functionFieldˣ) :
    closedImmersionPushforward ℤ i (principalDivisor X f) ∈
      cyclesOfDegree ℤ δ (δ (i.base (genericPoint X)) - 1) :=
  closedImmersionPushforward_mem_cyclesOfDegree_comap ℤ δ i _ _
    (principalDivisor_mem_cyclesOfDegree (δ.comapClosedImmersion i) f)

/-- On an actual integral closed carrier `W`, its principal divisor gives
an ambient cycle of degree `deg(W) - 1`. Only the carrier must be locally
Noetherian and quasi-compact; the ambient scheme need not be integral. -/
theorem principalDivisor_closedSupport_mem_cyclesOfDegree {X : Scheme.{u}}
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ,
    closedImmersionPushforward ℤ W.val.subschemeι
      (principalDivisor W.val.subscheme f) ∈
        cyclesOfDegree ℤ δ (supportDegree δ W - 1) := by
  letI := W.property
  intro f
  exact closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree
    δ W.val.subschemeι f

end

end HodgeConjecture.SchemeCycles
