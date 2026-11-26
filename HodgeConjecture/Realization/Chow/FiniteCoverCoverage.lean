module

public import HodgeConjecture.Realization.Chow.FiniteCoverageCertificate
public import HodgeConjecture.Realization.Chow.HarmonicWitness

@[expose] public section

/-!
# Aggregate coverage from an actual cover comparison

The cover's cohomology transfer has positive degree and its cycle pushforward
commutes with the original cycle-class map. A supplied upstairs cycle for
each coordinate column represents the pullback of that column. Normalized
geometric pushforward then constructs the downstairs cycles of the existing
aggregate certificate.

The model and its full independently specified Hodge basis remain fixed.
The comparison square, degree law and upstairs column representatives are
explicit proof gates. No generation assumption is inferred from the existence
of a cover. Concrete scheme maps and their comparison proofs instantiate this
API in `Betti/Examples/SplitGeometricCoverage.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.FiniteCoverageCertificate

variable {ChowX HX ChowY HY ι : Type*}
  [AddCommGroup ChowX] [Module ℚ ChowX] [AddCommGroup HX] [Module ℚ HX]
  [AddCommGroup ChowY] [Module ℚ ChowY] [AddCommGroup HY] [Module ℚ HY]
  [Fintype ι] [DecidableEq ι]

/-- Actual normalized pushforwards of the selected upstairs cycles. -/
def normalizedCoverCycles (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX) (upstairs : ι → ChowY) : ι → ChowX :=
  fun j => (T.degree : ℚ)⁻¹ • pushCH (upstairs j)

/-- A proved cover square binds columns before arithmetic rank is checked. -/
def of_degree_transfer
    (M : RationalHodgeCycleClassModel ChowX HX)
    (b : Module.Basis ι ℚ M.hodgeClasses)
    (clY : ChowY →ₗ[ℚ] HY) (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX)
    (push_comparison : M.cycleClass.comp pushCH = T.push.comp clY)
    (upstairs : ι → ChowY) (A : Matrix ι ι ℚ)
    (arithmetic : ModularRankCertificate.Certificate ι)
    (upstairs_columns : ∀ j, clY (upstairs j) =
      T.pull (b.equivFun.symm (fun i => A i j) : HX)) : Certificate M b where
  cycles := normalizedCoverCycles T pushCH upstairs
  coordinates := A
  arithmetic := arithmetic
  column_binding j := Subtype.ext
    (normalizedPushforward_cycleClass M clY T pushCH push_comparison
      (upstairs j) (b.equivFun.symm (fun i => A i j) : HX) (upstairs_columns j))

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : Harmonic.OrientedTwoComplex Vertex Edge Face}

/-- Faithful harmonic witnesses can discharge the upstairs generation columns. -/
def of_degree_transfer_harmonic
    (M : RationalHodgeCycleClassModel ChowX HX)
    (b : Module.Basis ι ℚ M.hodgeClasses)
    (clY : ChowY →ₗ[ℚ] HY) (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX)
    (push_comparison : M.cycleClass.comp pushCH = T.push.comp clY)
    (upstairs : ι → ChowY) (A : Matrix ι ι ℚ)
    (arithmetic : ModularRankCertificate.Certificate ι)
    (F : Harmonic.CellularSheaf X)
    (W : HY →ₗ[ℚ] F.harmonicOneSubspace) (faithful : Function.Injective W)
    (column_certificates : ∀ j, F.IsExactOneCochain
      ((W (clY (upstairs j)) : F.C1) -
        (W (T.pull (b.equivFun.symm (fun i => A i j) : HX)) : F.C1))) :
    Certificate M b :=
  of_degree_transfer M b clY T pushCH push_comparison upstairs A arithmetic
    (fun j => F.eq_of_exact_harmonicWitness_sub W faithful (column_certificates j))

end HodgeConjecture.FiniteCoverageCertificate

end
