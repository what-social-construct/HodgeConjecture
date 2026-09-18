import HodgeConjecture.Boundary.Normalization.ConjugateBoundary
import HodgeConjecture.Boundary.Sheets.GaloisSheets

/-!
# Boundary separation for a fully visible normalization

If the marked open contains the whole intermediate normalization, every
pulled-back conjugate boundary is empty. The faithful sheet action of the
normal closure then makes the moving-boundary ideal the unit ideal for
every nontrivial subgroup. This gives conjugate-boundary separation directly,
without a regular pair or a Noetherian hypothesis.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.NormalizationInertia

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)

omit [IsFractionRing B K] in
/-- Full visibility of the marked normalization persists on every conjugate
sheet pulled back to the common normal closure. -/
theorem pulledBackConjugateVisibleOpen_eq_univ_of_surjective
    (hVisible : Function.Surjective j.base) (g : C.GaloisGroup) :
    pulledBackConjugateVisibleOpen C g = Set.univ := by
  simp [pulledBackConjugateVisibleOpen, Set.range_eq_univ.mpr hVisible]

omit [IsFractionRing B K] in
/-- A fully visible intermediate normalization has no pulled-back conjugate
boundary. -/
theorem pulledBackConjugateBoundary_eq_empty_of_surjective
    (hVisible : Function.Surjective j.base) (g : C.GaloisGroup) :
    pulledBackConjugateBoundary C g = ∅ := by
  rw [pulledBackConjugateBoundary,
    pulledBackConjugateVisibleOpen_eq_univ_of_surjective C hVisible]
  exact Set.compl_univ

omit [IsFractionRing B K] in
/-- The canonical ideal of an empty conjugate boundary is the unit ideal. -/
theorem pulledBackConjugateBoundaryIdeal_eq_top_of_surjective
    (hVisible : Function.Surjective j.base) (g : C.GaloisGroup) :
    pulledBackConjugateBoundaryIdeal C g = ⊤ := by
  rw [pulledBackConjugateBoundaryIdeal,
    pulledBackConjugateBoundary_eq_empty_of_surjective C hVisible,
    PrimeSpectrum.vanishingIdeal_empty]

omit [IsFractionRing B K] in
/-- In a fully visible normal closure, every nontrivial subgroup moves a
sheet whose boundary ideal is the unit ideal. -/
theorem movingBoundaryIdeal_eq_top_of_surjective
    [PerfectField K]
    (hVisible : Function.Surjective j.base)
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I = ⊤ := by
  obtain ⟨s, hs⟩ :=
    CollisionFoundations.exists_sheet_moved_of_normalCore_eq_bot
      I C.normalClosure.intermediateFixingSubgroup
      C.normalClosure.intermediateFixingSubgroup_normalCore_eq_bot hI
  revert hs
  refine Quotient.inductionOn s ?_
  intro g hs
  have hg : ¬ I ≤ C.normalClosure.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom := by
    intro hle
    apply hs
    simpa using
      (CollisionFoundations.inertiaInvisibleAt_conjugateSheet_iff
        I C.normalClosure.intermediateFixingSubgroup g).2 hle
  apply top_unique
  rw [← pulledBackConjugateBoundaryIdeal_eq_top_of_surjective C hVisible g]
  exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

omit [IsFractionRing B K] in
/-- Full visibility makes the existing fixed--moving ideal the unit ideal
for every nontrivial subgroup. -/
theorem fixedMovingBoundaryIdeal_eq_top_of_surjective
    [PerfectField K]
    (hVisible : Function.Surjective j.base)
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥) :
    fixedMovingBoundaryIdeal C I = ⊤ := by
  simp [fixedMovingBoundaryIdeal,
    movingBoundaryIdeal_eq_top_of_surjective C hVisible I hI]

omit [IsFractionRing B K] in
/-- Full visibility establishes conjugate-boundary separation directly:
the unit fixed--moving ideal lies in no prime. -/
theorem conjugateBoundarySeparation_of_surjective
    [PerfectField K]
    (hVisible : Function.Surjective j.base) :
    ConjugateBoundarySeparation C := by
  intro I hI p _ hle
  rw [fixedMovingBoundaryIdeal_eq_top_of_surjective C hVisible I hI] at hle
  exact p.isPrime.ne_top (top_le_iff.mp hle)

end

end HodgeConjecture.NormalizationInertia
