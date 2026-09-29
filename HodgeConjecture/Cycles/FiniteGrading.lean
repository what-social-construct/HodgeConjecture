import HodgeConjecture.Cycles.FiniteResidueField
import HodgeConjecture.Cycles.FieldDimensionFunction
import HodgeConjecture.Cycles.GradedFinitePushforward
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Finite maps preserve the existing field-induced grading

The actual residue-field map is algebraic. Its scalar tower with the two
independently defined structural actions follows from their existing
naturality theorem. Mathlib's transcendence-degree tower formula therefore
preserves the full cardinal before passage to the integer-valued dimension
function. Evaluating at the original support generic point discharges the
existing finite pushforward's degree-compatibility premise.

No new dimension function, cycle module or pushforward is constructed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- A finite morphism preserves the full structural residue-field
transcendence degree, without a locally finite-type structural hypothesis. -/
theorem residueFieldBase_trdeg_eq_of_isFinite
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsFinite f] (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Algebra.trdeg k (Y.residueField (f.base x)) = Algebra.trdeg k (X.residueField x) := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower k (Y.residueField (f.base x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq' (residueFieldBaseMap_comp k p f x).symm
  letI : Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) :=
    residueFieldMap_isAlgebraic_of_isFinite f x
  simpa only [trdeg_eq_zero, add_zero] using
    (trdeg_add_eq (A := X.residueField x) k (Y.residueField (f.base x)))

/-- The original field-induced dimension function is preserved pointwise
by a finite morphism. The source structural map is the actual composite. -/
theorem DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] (x : X) :
    ofLocallyOfFiniteType k X (f ≫ p) x =
      ofLocallyOfFiniteType k Y p (f.base x) := by
  rw [ofLocallyOfFiniteType_apply, ofLocallyOfFiniteType_apply,
    residueFieldBase_trdeg_eq_of_isFinite k p f x]

/-- Actual finite images preserve the existing field-induced support degree. -/
theorem supportDegree_imageSubscheme_ofLocallyOfFiniteType
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] (W : IntegralClosedSubscheme X) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k Y p) (imageSubscheme f W) =
      supportDegree (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)) W := by
  rw [supportDegree_imageSubscheme, supportDegree,
    DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p f]

/-- The existing finite cycle pushforward preserves the canonical field
grading without a supplied degree-compatibility hypothesis. -/
theorem finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType
    (k : Type u) [Field k] (R : Type v) [Semiring R] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsFinite f] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)) n) :
    finitePushforward R f c ∈
      cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k Y p) n :=
  finitePushforward_mem_cyclesOfDegree R
    (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p))
    (DimensionFunction.ofLocallyOfFiniteType k Y p) f n c hc
    (supportDegree_imageSubscheme_ofLocallyOfFiniteType k p f)

end

end HodgeConjecture.SchemeCycles
