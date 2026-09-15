import HodgeConjecture.Cycles.LowDimensionalDimensionFunction
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.KrullDimension.PID

/-!
# A dimension function on the actual affine line

The scheme is literally `Spec k[T]`. Its dimension is proved to be one
from the polynomial PID, and the existing low-dimensional constructor
therefore supplies its dimension function without a grading-law input.
The generic point has degree one and the origin, defined by the kernel
of the actual constant-coefficient map, has degree zero.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles.Examples

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The affine line is the actual spectrum of a one-variable polynomial algebra. -/
abbrev affineLine (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The exact dimension-one calculation uses the proved polynomial PID theorem. -/
theorem affineLine_dimension (k : Type u) [Field k] :
    topologicalKrullDim (affineLine k) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one (Polynomial k) (Polynomial.not_isField k)

/-- The canonical dimension function on the actual affine line. -/
def affineLineDimensionFunction (k : Type u) [Field k] : DimensionFunction (affineLine k) :=
  DimensionFunction.ofKrullDimLEOne (affineLine k) (affineLine_dimension k).le

/-- The generic point has the actual scheme's dimension, one. -/
theorem affineLineDimensionFunction_genericPoint (k : Type u) [Field k] :
    affineLineDimensionFunction k (genericPoint (affineLine k)) = 1 := by
  have h := genericPoint_height_eq_topologicalKrullDim (affineLine k)
  rw [affineLine_dimension] at h
  have hh : Order.height (genericPoint (affineLine k)) = 1 := WithBot.coe_inj.mp h
  change ((Order.height (genericPoint (affineLine k))).toNat : ℤ) = 1
  simp only [hh, ENat.toNat_one, Nat.cast_one]

/-- The origin's defining maximal ideal is the kernel of evaluation at zero. -/
theorem affineLineOriginIdeal_isMaximal (k : Type u) [Field k] :
    (RingHom.ker (Polynomial.constantCoeff : Polynomial k →+* k)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a ↦ ⟨Polynomial.C a, by simp⟩)

/-- The actual point cut out by the constant-coefficient kernel. -/
def affineLineOrigin (k : Type u) [Field k] : affineLine k :=
  ⟨RingHom.ker Polynomial.constantCoeff, (affineLineOriginIdeal_isMaximal k).isPrime⟩

theorem affineLineOrigin_isClosed (k : Type u) [Field k] :
    IsClosed ({affineLineOrigin k} : Set (affineLine k)) := by
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (affineLineOriginIdeal_isMaximal k)

/-- The origin has degree zero, proved from its actual closedness. -/
theorem affineLineDimensionFunction_origin (k : Type u) [Field k] :
    affineLineDimensionFunction k (affineLineOrigin k) = 0 := by
  have hmin : IsMin (affineLineOrigin k) := by
    intro y hy
    have hmem : y ∈ ({affineLineOrigin k} : Set (affineLine k)) :=
      (Scheme.le_iff_specializes.mp hy).mem_closed (affineLineOrigin_isClosed k)
        (Set.mem_singleton _)
    exact (Set.mem_singleton_iff.mp hmem).symm.le
  change ((Order.height (affineLineOrigin k)).toNat : ℤ) = 0
  simp only [Order.height_eq_zero.mpr hmin, ENat.toNat_zero, Nat.cast_zero]

end

end HodgeConjecture.SchemeCycles.Examples
