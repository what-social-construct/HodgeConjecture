import HodgeConjecture.Cycles.DimensionFunction
import HodgeConjecture.Cycles.ClosedImmersionPushforward
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Degree submodules of the existing finite-cycle module

A chosen dimension function assigns a degree to each actual integral
closed support through its ambient generic point. Degree-`n` cycles are
the supported submodule of the existing finite-cycle module, not a second
free module. Distinct degrees are disjoint.

The existing closed-immersion pushforward preserves degree when its
actual integral image supports have the corresponding degrees. This is
a plain compatibility equality for dimension functions, not a relation
or Chow-descent hypothesis.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}}

/-- The degree-`n` submodule of the existing finite cycles, using actual
support degrees for the chosen dimension function. -/
def cyclesOfDegree (R : Type v) [Semiring R] (δ : DimensionFunction X) (n : ℤ) :
    Submodule R (Cycles X R) :=
  Finsupp.supported R R {Z | supportDegree δ Z = n}

/-- A cycle is homogeneous exactly when every nonzero coefficient has
the prescribed degree. -/
theorem mem_cyclesOfDegree_iff (R : Type v) [Semiring R]
    (δ : DimensionFunction X) (n : ℤ) (c : Cycles X R) :
    c ∈ cyclesOfDegree R δ n ↔
      ∀ Z : IntegralClosedSubscheme X, c Z ≠ 0 → supportDegree δ Z = n := by
  change (c.support : Set (IntegralClosedSubscheme X)) ⊆
    {Z | supportDegree δ Z = n} ↔ _
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_setOf_eq]

/-- A single coefficient on a degree-`n` support is a degree-`n` cycle. -/
theorem single_mem_cyclesOfDegree (R : Type v) [Semiring R]
    (δ : DimensionFunction X) (n : ℤ) (Z : IntegralClosedSubscheme X)
    (r : R) (hZ : supportDegree δ Z = n) :
    Finsupp.single Z r ∈ cyclesOfDegree R δ n :=
  Finsupp.single_mem_supported R r hZ

/-- The existing fundamental cycle lies in the degree of its actual support. -/
theorem fundamentalCycle_mem_cyclesOfDegree (R : Type v) [Semiring R]
    (δ : DimensionFunction X) (n : ℤ) (Z : IntegralClosedSubscheme X)
    (hZ : supportDegree δ Z = n) :
    fundamentalCycle R Z ∈ cyclesOfDegree R δ n :=
  single_mem_cyclesOfDegree R δ n Z 1 hZ

/-- Over nontrivial coefficients, membership of a fundamental cycle also
detects the support degree. The nontriviality assumption is essential. -/
theorem fundamentalCycle_mem_cyclesOfDegree_iff (R : Type v) [Semiring R] [Nontrivial R]
    (δ : DimensionFunction X) (n : ℤ) (Z : IntegralClosedSubscheme X) :
    fundamentalCycle R Z ∈ cyclesOfDegree R δ n ↔ supportDegree δ Z = n := by
  constructor
  · intro h
    exact (mem_cyclesOfDegree_iff R δ n _).mp h Z (by simp)
  · exact fundamentalCycle_mem_cyclesOfDegree R δ n Z

/-- Distinct degrees intersect only in the zero cycle, even when the
coefficient semiring itself is trivial. -/
theorem cyclesOfDegree_disjoint (R : Type v) [Semiring R]
    (δ : DimensionFunction X) (n m : ℤ) (hnm : n ≠ m) :
    Disjoint (cyclesOfDegree R δ n) (cyclesOfDegree R δ m) := by
  apply Finsupp.disjoint_supported_supported
  exact Set.disjoint_left.mpr fun Z hn hm ↦ hnm (hn.symm.trans hm)

/-- Actual closed pushforward preserves a homogeneous cycle when the
source degree agrees with the degree of each actual image support. -/
theorem closedImmersionPushforward_mem_cyclesOfDegree (R : Type v) [Semiring R]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R δX n)
    (hdeg : ∀ Z : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i Z) = supportDegree δX Z) :
    closedImmersionPushforward R i c ∈ cyclesOfDegree R δY n := by
  have hle : cyclesOfDegree R δX n ≤
      (cyclesOfDegree R δY n).comap (closedImmersionPushforward R i) := by
    change Finsupp.supported R R {Z | supportDegree δX Z = n} ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨Z, hZ, rfl⟩
    change closedImmersionPushforward R i (fundamentalCycle R Z) ∈ cyclesOfDegree R δY n
    rw [closedImmersionPushforward_fundamentalCycle]
    exact fundamentalCycle_mem_cyclesOfDegree R δY n (closedImageSubscheme i Z)
      ((hdeg Z).trans hZ)
  exact hle hc

end

end HodgeConjecture.SchemeCycles
