module

import HodgeConjecture.Boundary.Normalization.AffineSections
import HodgeConjecture.Boundary.Normalization.BoundarySections
import HodgeConjecture.Boundary.Normalization.BoundedOverring
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
Focused SP65 regressions. Run with
`lake env lean research/BoundarySectionsVerification.lean`.
These check actual section maps and their specialization to the existing
normalization. The conditional bounded-overring test supplies its bound
explicitly; no uniform geometric bound or surjectivity onto the field is
asserted. All 21 new public declarations have an enforced axiom allowlist.
-/

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.NormalizationInertia

set_option maxHeartbeats 800000

noncomputable section

section Affine

variable {T : CommRingCat} [IsDomain T]
variable {F : Type*} [Field F] [Algebra T F] [IsFractionRing T F]
variable (V W : (Spec T).Opens) [Nonempty V] [Nonempty W]

-- The actual generic-germ map is multiplicative, not merely linear.
example (s t : Γ(Spec T, V)) :
    affineSectionsToFractionField (N := F) V (s * t) =
      affineSectionsToFractionField V s * affineSectionsToFractionField V t :=
  map_mul _ s t

example (t : T) :
    affineSectionsToFractionField (N := F) V
      (algebraMap T Γ(Spec T, V) t) = algebraMap T F t :=
  affineSectionsToFractionField_algebraMap V t

example (s t : Γ(Spec T, V))
    (h : affineSectionsToFractionField (N := F) V s =
      affineSectionsToFractionField V t) : s = t :=
  affineSectionsToFractionField_injective V h

example (hWV : W ≤ V) (s : Γ(Spec T, V)) :
    affineSectionsToFractionField (N := F) W
      ((Spec T).presheaf.map (homOfLE hWV).op s) =
        affineSectionsToFractionField V s :=
  affineSectionsToFractionField_restrict V W hWV s

example (hWV : W ≤ V) :
    affineSectionSubalgebra (N := F) V ≤ affineSectionSubalgebra W :=
  affineSectionSubalgebra_anti V W hWV

example (z : F) : z ∈ affineSectionSubalgebra V ↔
    ∃ s : Γ(Spec T, V), affineSectionsToFractionField V s = z :=
  mem_affineSectionSubalgebra_iff V z

example (s : Γ(Spec T, V)) :
    (affineSectionsEquivSubalgebra (N := F) V s : F) =
      affineSectionsToFractionField V s :=
  affineSectionsEquivSubalgebra_apply V s

example (s : Γ(Spec T, V)) :
    (affineSectionsEquivSubalgebra (N := F) V).symm
      (affineSectionsEquivSubalgebra V s) = s :=
  (affineSectionsEquivSubalgebra V).symm_apply_apply s

-- Full affine sections recover the base, not the whole fraction field.
example :
    letI : Nonempty (⊤ : (Spec T).Opens) := ⟨⟨(⊥ : PrimeSpectrum T), trivial⟩⟩
    affineSectionSubalgebra (T := T) (N := F) ⊤ = ⊥ := by
  letI : Nonempty (⊤ : (Spec T).Opens) := ⟨⟨(⊥ : PrimeSpectrum T), trivial⟩⟩
  exact affineSectionSubalgebra_top

-- B0 applies to the actual image, with its uniform bound still a premise.
example [IsNoetherianRing T] [IsIntegrallyClosed T]
    (a : T) (ha : a ≠ 0)
    (h : ∀ s : Γ(Spec T, V),
      algebraMap T F a * affineSectionsToFractionField V s ∈
        Set.range (algebraMap T F)) :
    affineSectionSubalgebra (N := F) V = ⊥ := by
  apply subalgebra_eq_bot_of_nonzero_mul_mem_base T F
    (affineSectionSubalgebra V) a ha
  rintro ⟨z, hz⟩
  obtain ⟨s, rfl⟩ := (mem_affineSectionSubalgebra_iff V z).mp hz
  exact h s

end Affine

section Boundary

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
variable (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

local instance : Algebra T₀ (BoundarySectionRing C I) :=
  inferInstanceAs (Algebra T₀
    ((Spec.structureSheaf T₀).obj.obj (Opposite.op (fixedMovingBoundaryOpen C I))))

example : IsFractionRing T₀ N := normalization_isFractionRing C

example : fixedLocusIdeal I ≠ ⊥ ∧ Nonempty (fixedMovingBoundaryOpen C I) :=
  ⟨fixedLocusIdeal_ne_bot C I hI, fixedMovingBoundaryOpen_nonempty C I hI⟩

example (s t : BoundarySectionRing C I)
    (h : boundarySectionsToNormalClosure C I hI s =
      boundarySectionsToNormalClosure C I hI t) : s = t :=
  boundarySectionsToNormalClosure_injective C I hI h

example (s t : BoundarySectionRing C I) (a : T₀) :
    boundarySectionsToNormalClosure C I hI (s * t) =
      boundarySectionsToNormalClosure C I hI s *
        boundarySectionsToNormalClosure C I hI t ∧
    boundarySectionsToNormalClosure C I hI
      (algebraMap T₀ (BoundarySectionRing C I) a) = algebraMap T₀ N a :=
  ⟨map_mul _ s t, (boundarySectionsToNormalClosure C I hI).commutes a⟩

example (s : BoundarySectionRing C I) :
    (boundarySectionsEquivSubalgebra C I hI).symm
      (boundarySectionsEquivSubalgebra C I hI s) = s :=
  (boundarySectionsEquivSubalgebra C I hI).symm_apply_apply s

example (a : T₀) : (a : N) ∈ boundarySectionSubalgebra C I hI ∧
    ∃ s : BoundarySectionRing C I, boundarySectionsToNormalClosure C I hI s = a := by
  have ha := normalization_mem_boundarySectionSubalgebra C I hI a
  exact ⟨ha, (mem_boundarySectionSubalgebra_iff C I hI a).mp ha⟩

end Boundary

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.NormalizationInertia.affineSectionsToFractionField,
      `HodgeConjecture.NormalizationInertia.affineSectionsToFractionField_injective,
      `HodgeConjecture.NormalizationInertia.affineSectionsToFractionField_algebraMap,
      `HodgeConjecture.NormalizationInertia.affineSectionsToFractionField_restrict,
      `HodgeConjecture.NormalizationInertia.affineSectionSubalgebra,
      `HodgeConjecture.NormalizationInertia.mem_affineSectionSubalgebra_iff,
      `HodgeConjecture.NormalizationInertia.affineSectionsEquivSubalgebra,
      `HodgeConjecture.NormalizationInertia.affineSectionsEquivSubalgebra_apply,
      `HodgeConjecture.NormalizationInertia.affineSectionSubalgebra_anti,
      `HodgeConjecture.NormalizationInertia.affineSectionSubalgebra_top,
      `HodgeConjecture.NormalizationInertia.normalization_isFractionRing,
      `HodgeConjecture.NormalizationInertia.fixedMovingBoundaryOpen,
      `HodgeConjecture.NormalizationInertia.fixedLocusIdeal_ne_bot,
      `HodgeConjecture.NormalizationInertia.fixedMovingBoundaryOpen_nonempty,
      `HodgeConjecture.NormalizationInertia.BoundarySectionRing,
      `HodgeConjecture.NormalizationInertia.boundarySectionsToNormalClosure,
      `HodgeConjecture.NormalizationInertia.boundarySectionsToNormalClosure_injective,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra,
      `HodgeConjecture.NormalizationInertia.boundarySectionsEquivSubalgebra,
      `HodgeConjecture.NormalizationInertia.mem_boundarySectionSubalgebra_iff,
      `HodgeConjecture.NormalizationInertia.normalization_mem_boundarySectionSubalgebra] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
