import HodgeConjecture.Boundary.Normalization.AffineSections
import HodgeConjecture.Boundary.Normalization.ConjugateBoundary
import Mathlib.RingTheory.Localization.Integral

/-!
# Sections outside the fixed--moving boundary

For a normalized cover and a nontrivial subgroup `I` of its Galois group,
this module constructs the actual structure-sheaf sections on
`Spec T \ V(fixedMovingBoundaryIdeal C I)`.  The normalization ring `T` has
fraction field `N`, so the generic germ embeds these sections in `N` as a
`T`-subalgebra.  Faithfulness of the action on the fraction field proves
that the open set is nonempty.

The construction uses the supplied normalized cover but no boundary
separation or uniform trace-landing hypothesis.  The underlying section
module is the `.toSubmodule` of `boundarySectionSubalgebra`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace NormalizationInertia

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j)

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

include C in
omit [IsScalarTower B K L] in
/-- The normal-closure field is the fraction field of its integral-closure
model.  Finite dimensionality comes from the supplied normal closure. -/
theorem normalization_isFractionRing : IsFractionRing T₀ N := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : FiniteDimensional K N := C.normalClosure.finiteNormal
  exact integralClosure.isFractionRing_of_finite_extension K N

/-- The complement of the fixed--moving boundary in the normalization. -/
def fixedMovingBoundaryOpen (I : Subgroup C.GaloisGroup) :
    (Spec (.of T₀)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (fixedMovingBoundaryIdeal C I))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

omit [IsScalarTower B K L] in
/-- A nontrivial subgroup has nonzero fixed-locus ideal, because the action
on the integral closure determines its action on the fraction field. -/
theorem fixedLocusIdeal_ne_bot
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    fixedLocusIdeal I ≠ ⊥ := by
  letI : IsFractionRing T₀ N := normalization_isFractionRing C
  intro h
  apply hI
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  have hfix := (fixedLocusIdeal_le_iff I (⊥ : Ideal T₀)).mp (le_of_eq h)
  have heq : σ.toRingHom = (1 : C.GaloisGroup).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := T₀)
    intro t
    have ht := hfix ⟨σ, hσ⟩ t
    have ht' : normalClosureNormalizationRingEquiv (B := B) σ t = t :=
      sub_eq_zero.mp (by simpa only [Ideal.mem_bot] using ht)
    exact congrArg (fun a : T₀ => (a : N)) ht'
  exact AlgEquiv.ext fun x => congrArg (fun f : N →+* N => f x) heq

/-- The generic point remains outside the fixed--moving boundary whenever
the subgroup is nontrivial. -/
theorem fixedMovingBoundaryOpen_nonempty
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    Nonempty (fixedMovingBoundaryOpen C I) := by
  refine ⟨⟨(⊥ : PrimeSpectrum T₀), ?_⟩⟩
  change ¬ fixedMovingBoundaryIdeal C I ≤ (⊥ : Ideal T₀)
  intro h
  apply fixedLocusIdeal_ne_bot C I hI
  apply le_bot_iff.mp
  exact le_trans
    (show fixedLocusIdeal I ≤ fixedMovingBoundaryIdeal C I from le_sup_left) h

/-- The genuine structure-sheaf section ring on the boundary complement. -/
abbrev BoundarySectionRing (I : Subgroup C.GaloisGroup) :=
  Γ(Spec (.of T₀), fixedMovingBoundaryOpen C I)

-- Expose Mathlib's existing affine-section algebra through the ring abbreviation.
local instance (I : Subgroup C.GaloisGroup) : Algebra T₀ (BoundarySectionRing C I) :=
  inferInstanceAs
    (Algebra T₀
      ((Spec.structureSheaf T₀).val.obj (Opposite.op (fixedMovingBoundaryOpen C I))))

/-- The generic-germ algebra map from boundary sections to the specified
normal-closure field. -/
def boundarySectionsToNormalClosure
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    BoundarySectionRing C I →ₐ[T₀] N := by
  letI := normalization_isFractionRing C
  letI := fixedMovingBoundaryOpen_nonempty C I hI
  exact affineSectionsToFractionField (T := .of T₀) (N := N)
    (fixedMovingBoundaryOpen C I)

/-- A boundary section is determined by its generic germ. -/
theorem boundarySectionsToNormalClosure_injective
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    Function.Injective (boundarySectionsToNormalClosure C I hI) := by
  letI := normalization_isFractionRing C
  letI := fixedMovingBoundaryOpen_nonempty C I hI
  exact affineSectionsToFractionField_injective (T := .of T₀) (N := N)
    (fixedMovingBoundaryOpen C I)

/-- The actual boundary-section algebra inside the normal-closure field. -/
def boundarySectionSubalgebra
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) : Subalgebra T₀ N :=
  (boundarySectionsToNormalClosure C I hI).range

/-- The boundary section ring is canonically isomorphic to its image. -/
def boundarySectionsEquivSubalgebra
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    BoundarySectionRing C I ≃ₐ[T₀] boundarySectionSubalgebra C I hI := by
  letI := normalization_isFractionRing C
  letI := fixedMovingBoundaryOpen_nonempty C I hI
  exact affineSectionsEquivSubalgebra (T := .of T₀) (N := N)
    (fixedMovingBoundaryOpen C I)

/-- Membership in the section subalgebra means being the germ of an actual
regular section on the boundary complement. -/
@[simp]
theorem mem_boundarySectionSubalgebra_iff
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) (z : N) :
    z ∈ boundarySectionSubalgebra C I hI ↔
      ∃ s : BoundarySectionRing C I, boundarySectionsToNormalClosure C I hI s = z :=
  Iff.rfl

/-- Every normalization-ring element restricts to a boundary section. -/
theorem normalization_mem_boundarySectionSubalgebra
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) (t : T₀) :
    (t : N) ∈ boundarySectionSubalgebra C I hI :=
  (boundarySectionSubalgebra C I hI).algebraMap_mem t

end NormalizationInertia

end

end HodgeConjecture
