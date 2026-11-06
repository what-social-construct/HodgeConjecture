module

public import HodgeConjecture.CommutativeAlgebra.FiniteFiberLength
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-! Quotient lengths in a square of local rings obtained by surjections.
These identities compare actual rings and their original maps. -/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

/-- Quotienting a ring first does not alter the subsequent quotient length when its
kernel already lies in the ideal being killed. -/
theorem length_quotient_map_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I : Ideal R)
    (hker : RingHom.ker φ ≤ I) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map φ) := by
  let J := I.map φ
  let ψ : R →+* S ⧸ J := (Ideal.Quotient.mk J).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hkerψ : RingHom.ker ψ = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective φ hφ,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  letI : Algebra R S := φ.toAlgebra
  letI : Algebra R (S ⧸ J) := ψ.toAlgebra
  letI : IsScalarTower R S (S ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  have hlen : Module.length R (R ⧸ RingHom.ker ψ) = Module.length R (S ⧸ J) :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R (S ⧸ J))
      hψ).toLinearEquiv.length_eq
  calc
    Module.length R (R ⧸ I) = Module.length R (R ⧸ RingHom.ker ψ) := by rw [hkerψ]
    _ = Module.length R (S ⧸ J) := hlen
    _ = Module.length S (S ⧸ J) := Module.length_eq_of_surjective (M := S ⧸ J) hφ

/-- In a commutative square of local rings whose horizontal arrows are surjective,
base change of the defining kernel preserves the length of the closed-fiber quotient. -/
theorem closedFiber_length_of_quotient_square
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsLocalRing A'] [IsLocalRing B] [IsLocalRing B']
    (α : A →+* B) (β : A' →+* B') (φ : A →+* A') (ψ : B →+* B')
    [IsLocalHom φ] (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hcomm : ψ.comp α = β.comp φ)
    (hker : RingHom.ker ψ = (RingHom.ker φ).map α) :
    Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map α) =
      Module.length B' (B' ⧸ (IsLocalRing.maximalIdeal A').map β) := by
  have hkerφ : RingHom.ker φ ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    rw [← IsLocalRing.maximalIdeal_comap φ]
    change φ a ∈ IsLocalRing.maximalIdeal A'
    rw [show φ a = 0 from ha]
    exact Ideal.zero_mem _
  have hkerψ : RingHom.ker ψ ≤ (IsLocalRing.maximalIdeal A).map α := by
    rw [hker]
    exact Ideal.map_mono hkerφ
  rw [length_quotient_map_of_surjective ψ hψ _ hkerψ,
    Ideal.map_map, hcomm, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective φ hφ]

end

end HodgeConjecture.CommutativeAlgebra
