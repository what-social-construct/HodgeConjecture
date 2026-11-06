module

public import HodgeConjecture.Boundary.Normalization.GluedNormalizationChart
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

/-!
# Target-local properties of the original glued normalization

The actual nonempty affine base charts cover the whole base. Their proved
inverse-image comparisons transfer target-local morphism properties to the
existing global map, using the original germ-derived structural maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-- The actual nonempty affine opens cover every scheme, including the empty scheme. -/
theorem nonemptyAffineChart_iSup_eq_top (X : Scheme.{u}) :
    (⨆ U : NonemptyAffineChart X, U.val) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
  exact (le_iSup (fun U : NonemptyAffineChart X => U.val)
    ⟨U, hU, ⟨⟨x, hx⟩⟩⟩) hx

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance normalizationPropertyAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

/-- A target-local property of the global map is exactly that property of
the original normalization maps to the nonempty affine base charts. -/
theorem gluedNormalizationToBase_property_iff
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        P (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P)
    (f := gluedNormalizationToBase X N)
    (fun U : NonemptyAffineChart X => U.val) (nonemptyAffineChart_iSup_eq_top X)]
  apply forall_congr'
  intro U
  have h := P.cancel_left_of_respectsIso (normalizationChartPreimageIso X N U).hom
    (gluedNormalizationToBase X N ∣_ U.val)
  rw [normalizationChartPreimageIso_hom_comp_restrict] at h
  exact h.symm

/-- The global normalization map is affine without a finite-degree or normal-base premise. -/
instance gluedNormalizationToBase_isAffineHom : IsAffineHom (gluedNormalizationToBase X N) := by
  apply (gluedNormalizationToBase_property_iff X N (@IsAffineHom)).mpr
  intro U
  letI : IsAffine U.val.toScheme := U.property.1
  letI : IsAffine (normalizedAffineModel Γ(X, U.val) N) := by
    unfold normalizedAffineModel
    infer_instance
  exact isAffineHom_of_isAffine _

/-- Finiteness is equivalent to finiteness of the original actual chart maps. -/
theorem gluedNormalizationToBase_isFinite_iff :
    IsFinite (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        IsFinite (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  gluedNormalizationToBase_property_iff X N (@IsFinite)

/-- Scheme étaleness is equivalent to scheme étaleness of those same chart maps. -/
theorem gluedNormalizationToBase_isEtale_iff :
    Etale (gluedNormalizationToBase X N) ↔
      ∀ U : NonemptyAffineChart X,
        Etale (normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv) :=
  gluedNormalizationToBase_property_iff X N (@Etale)

end

end HodgeConjecture.CollisionFoundations
