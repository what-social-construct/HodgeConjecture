module

public import HodgeConjecture.Boundary.Normalization.GluedNormalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Normal local rings of the original glued normalization

The integral closure of any commutative ring in a field is an integrally
closed domain. Its fraction field embeds into the ambient field, without
requiring that embedding to be onto. Localization gives normal affine
stalks, and the original chart open immersions transfer these local rings
to the same glued normalization scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Integral closure in a field is integrally closed in its own fraction field,
even when the ambient field is larger than that fraction field. -/
theorem normalizedCoordinateRing_isIntegrallyClosed
    (B N : Type u) [CommRing B] [Field N] [Algebra B N] :
    IsIntegrallyClosed (normalizedCoordinateRing B N) := by
  let T := normalizedCoordinateRing B N
  let f : FractionRing T →ₐ[T] N :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId T N)
      (IsIntegralClosure.algebraMap_injective T B N)
  exact f.isIntegrallyClosedIn f.injective
    (IsIntegrallyClosedIn.of_isIntegralClosure (R := B))

/-- The actual stalks of each affine normalization are integrally closed. -/
theorem normalizedAffineModel_stalk_isIntegrallyClosed
    (B N : Type u) [CommRing B] [Field N] [Algebra B N]
    (z : normalizedAffineModel B N) :
    IsIntegrallyClosed ((normalizedAffineModel B N).presheaf.stalk z) := by
  let T := normalizedCoordinateRing B N
  letI : IsIntegrallyClosed T := normalizedCoordinateRing_isIntegrallyClosed B N
  letI : IsIntegrallyClosed (Localization.AtPrime z.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime z.asIdeal)
      z.asIdeal.primeCompl z.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv
    (StructureSheaf.stalkIso T z).toRingEquiv

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

/-- Every actual local ring of the original glued normalization is a domain. -/
theorem gluedNormalizationModel_stalk_isDomain (z : gluedNormalizationModel X N) :
    IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) := by
  obtain ⟨U, x, rfl⟩ := (gluedNormalizationOpenCover X N).exists_eq z
  letI : Algebra Γ(X, U.val) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
  let T := normalizedCoordinateRing Γ(X, U.val) N
  let e := (asIso ((normalizationChartToGlued X N U).stalkMap x)).commRingCatIsoToRingEquiv
  let s := (StructureSheaf.stalkIso T x).symm.toRingEquiv
  exact (e.trans s).toMulEquiv.isDomain _

/-- Every actual local ring of the same glued normalization is integrally closed. -/
theorem gluedNormalizationModel_stalk_isIntegrallyClosed
    (z : gluedNormalizationModel X N) :
    IsIntegrallyClosed ((gluedNormalizationModel X N).presheaf.stalk z) := by
  obtain ⟨U, x, rfl⟩ := (gluedNormalizationOpenCover X N).exists_eq z
  letI : Algebra Γ(X, U.val) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra
  letI : IsIntegrallyClosed (((affineNormalizationDiagram X N).obj U).presheaf.stalk x) :=
    normalizedAffineModel_stalk_isIntegrallyClosed Γ(X, U.val) N x
  exact IsIntegrallyClosed.of_equiv
    (asIso ((normalizationChartToGlued X N U).stalkMap x)).symm.commRingCatIsoToRingEquiv

end

end HodgeConjecture.CollisionFoundations
