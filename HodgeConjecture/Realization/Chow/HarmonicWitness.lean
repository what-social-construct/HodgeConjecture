module

public import HodgeConjecture.LinearAlgebra.Harmonic.Cohomology
public import HodgeConjecture.Realization.Chow.UpstairsGeneration

@[expose] public section

/-!
# Harmonic certificates for the existing upstairs descent theorem

An injective rational linear map to a finite harmonic space is explicit
comparison data. An exact difference of its two harmonic witnesses certifies
the equality required by `normalizedPushforward_cycleClass`. The cycle,
geometric comparison, positive-degree transfer and pushforward compatibility
remain supplied; this adapter does not construct prescribed cycle witnesses.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture

variable {ChowX HX ChowY HY : Type*}
  [AddCommGroup ChowX] [Module ℚ ChowX] [AddCommGroup HX] [Module ℚ HX]
  [AddCommGroup ChowY] [Module ℚ ChowY] [AddCommGroup HY] [Module ℚ HY]
  {Vertex Edge Face : Type*} [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : Harmonic.OrientedTwoComplex Vertex Edge Face}

/-- Harmonic class verification discharges the original equality argument. -/
theorem normalizedPushforward_cycleClass_of_harmonicWitness
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ChowY →ₗ[ℚ] HY) (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX)
    (hPush : M.cycleClass.comp pushCH = T.push.comp clY)
    (F : Harmonic.CellularSheaf X)
    (W : HY →ₗ[ℚ] F.harmonicOneSubspace) (faithful : Function.Injective W)
    (z : ChowY) (α : HX)
    (certificate : F.IsExactOneCochain
      ((W (clY z) : F.C1) - (W (T.pull α) : F.C1))) :
    M.cycleClass ((T.degree : ℚ)⁻¹ • pushCH z) = α :=
  normalizedPushforward_cycleClass M clY T pushCH hPush z α
    (F.eq_of_exact_harmonicWitness_sub W faithful certificate)

end HodgeConjecture

end
