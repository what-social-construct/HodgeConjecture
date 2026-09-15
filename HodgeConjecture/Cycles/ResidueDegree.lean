import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Degree one through the actual residue map of a scheme isomorphism -/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- An actual scheme isomorphism induces a degree-one extension on residue
fields, with scalars supplied by its actual residue map. -/
theorem residueFieldMap_finrank_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Module.finrank (Y.residueField (f.base x)) (X.residueField x) = 1 := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply finrank_eq_one (1 : X.residueField x) one_ne_zero
  intro w
  obtain ⟨c, hc⟩ :=
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.surjective w
  refine ⟨c, ?_⟩
  simpa [Algebra.smul_def] using hc

end

end HodgeConjecture.SchemeCycles
