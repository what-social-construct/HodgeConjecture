import HodgeConjecture.Collision.DecompositionDefect
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.Locus

/-!
# Boundary contact and the Noether different

For a surjective ring homomorphism `μ : C → A`, let `J = ker μ`.  The
annihilator of `J` maps to an ideal of `A`; this is the Noether different
attached to the presentation:

`μ(ann(J)) ⊆ A`.

The contact quotient

`C / (J + ann(J))`

is canonically isomorphic to `A` modulo this different.  For the collision
algebra `C = A ⊗[B] A`, this identifies the diagonal/off-diagonal contact
quotient with a ramification ideal on the diagonal.

The final section relates global vanishing of this contact quotient to the
standard unramified locus.  Codimension-one inertia can then be attached using
the reusable valuation and normalization machinery in the boundary stage.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra
open scoped TensorProduct

noncomputable section

universe u v

section SurjectiveMap

variable {C : Type u} {A : Type v}
variable [CommRing C] [CommRing A]

/-- The image of the annihilator of the diagonal kernel. -/
def noetherDifferentIdeal (μ : C →+* A) : Ideal A :=
  (RingHom.ker μ).annihilator.map μ

/-- The canonical map from the collision algebra to the different quotient. -/
def contactQuotientMap (μ : C →+* A) :
    C →+* A ⧸ noetherDifferentIdeal μ :=
  (Ideal.Quotient.mk (noetherDifferentIdeal μ)).comp μ

/-- A surjective diagonal map remains surjective after quotienting by the different. -/
theorem contactQuotientMap_surjective
    (μ : C →+* A) (hμ : Function.Surjective μ) :
    Function.Surjective (contactQuotientMap μ) := by
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨c, rfl⟩ := hμ a
  exact ⟨c, rfl⟩

/-- The contact ideal is exactly the kernel of the different-quotient map. -/
theorem contactQuotientMap_ker
    (μ : C →+* A) (hμ : Function.Surjective μ) :
    RingHom.ker (contactQuotientMap μ) =
      contactIdeal (RingHom.ker μ) := by
  ext x
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (noetherDifferentIdeal μ) (μ x) = 0 ↔
    x ∈ contactIdeal (RingHom.ker μ)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change μ x ∈ (RingHom.ker μ).annihilator.map μ ↔
    x ∈ contactIdeal (RingHom.ker μ)
  rw [← Ideal.mem_comap,
    Ideal.comap_map_of_surjective μ hμ]
  simp only [contactIdeal, RingHom.ker_eq_comap_bot, sup_comm]

/--
The diagonal/off-diagonal contact quotient is the quotient of the diagonal by
the Noether different.
-/
noncomputable def contactRingEquivNoetherDifferentQuotient
    (μ : C →+* A) (hμ : Function.Surjective μ) :
    ContactRing (RingHom.ker μ) ≃+*
      A ⧸ noetherDifferentIdeal μ :=
  (Ideal.quotEquivOfEq (contactQuotientMap_ker μ hμ).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (contactQuotientMap_surjective μ hμ))

end SurjectiveMap

section Collision

variable (B : Type u) (A : Type v)
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The Noether different obtained from the abstract collision algebra. -/
def collisionNoetherDifferentIdeal : Ideal A :=
  noetherDifferentIdeal
    (collisionMultiplication B A).toRingHom

/--
The collision contact quotient is canonically the diagonal algebra modulo
the collision Noether different.
-/
noncomputable def collisionContactRingEquivDifferentQuotient :
    CollisionContactRing B A ≃+*
      A ⧸ collisionNoetherDifferentIdeal B A :=
  contactRingEquivNoetherDifferentQuotient
    (collisionMultiplication B A).toRingHom
    (collisionMultiplication_surjective B A)

end Collision

section Locus

-- Mathlib's current support description of `unramifiedLocus` is stated
-- with the base and algebra in a common universe.
variable (B A : Type u)
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The complement of the standard unramified locus. -/
def collisionRamificationLocus :
    Set (PrimeSpectrum A) :=
  (Algebra.unramifiedLocus B A)ᶜ

/-- The ramification locus is the support of relative Kähler differentials. -/
theorem collisionRamificationLocus_eq_support :
    collisionRamificationLocus B A =
      Module.support A Ω[A⁄B] := by
  rw [collisionRamificationLocus,
    Algebra.unramifiedLocus_eq_compl_support (R := B) (A := A), compl_compl]

/--
For an essentially finite-type algebra, the ramification locus is empty
exactly when the collision contact quotient vanishes globally.
-/
theorem collisionRamificationLocus_eq_empty_iff_contactRing_subsingleton
    [EssFiniteType B A] :
    collisionRamificationLocus B A = ∅ ↔
      Subsingleton (CollisionContactRing B A) := by
  rw [collisionRamificationLocus, Set.compl_empty_iff]
  exact (Algebra.unramifiedLocus_eq_univ_iff (R := B) (A := A)).trans
    (collisionContactRing_subsingleton_iff_formallyUnramified B A).symm

end Locus

end

end HodgeConjecture
