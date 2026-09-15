import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Transport of the actual local order of vanishing

Mathlib's `Ring.ord R a` is the length of the actual principal quotient
`R / (a)`. A ring isomorphism preserves this length through its order
isomorphism of ideal lattices. It therefore preserves the existing
zero-preserving order homomorphism and its extension to fraction fields.

The fraction-field comparison uses compatible actual ring and field
isomorphisms, with the Noetherian and dimension-at-most-one assumptions
needed to define `Ring.ordFrac` explicit. No divisor or order function is
postulated or redefined here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring isomorphism preserves the length of the actual principal quotient. -/
theorem ord_ringEquiv (eR : R ≃+* S) (a : R) :
    Ring.ord S (eR a) = Ring.ord R a := by
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  simpa only [RingEquiv.idealComapOrderIso_symm_apply, Ideal.map_span,
    Set.image_singleton] using
      Order.coheight_orderIso eR.idealComapOrderIso.symm (Ideal.span {a})

/-- The zero-preserving order homomorphism also respects the ring isomorphism. -/
theorem ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial S]
    (eR : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (eR a) = Ring.ordMonoidWithZeroHom R a := by
  have hmem : eR a ∈ nonZeroDivisors S ↔ a ∈ nonZeroDivisors R := by
    constructor
    · exact mem_nonZeroDivisors_of_injective eR.injective
    · intro ha
      exact mem_nonZeroDivisors_of_injective eR.symm.injective (by simpa using ha)
  by_cases ha : a ∈ nonZeroDivisors R
  · simp [Ring.ordMonoidWithZeroHom, ha, hmem.mpr ha, ord_ringEquiv]
  · have he : eR a ∉ nonZeroDivisors S := fun he ↦ ha (hmem.mp he)
    simp [Ring.ordMonoidWithZeroHom, ha, he]

/-- Compatible ring and field isomorphisms preserve the existing fraction-field
order of vanishing, including its zero value. -/
theorem ordFrac_ringEquiv {K L : Type*} [Field K] [Field L]
    [Nontrivial R] [Nontrivial S]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    (eR : R ≃+* S) (eK : K ≃+* L)
    (h : ∀ a : R, eK (algebraMap R K a) = algebraMap S L (eR a)) (f : K) :
    Ring.ordFrac S (eK f) = Ring.ordFrac R f := by
  have hbase (a : R) :
      Ring.ordFrac S (eK (algebraMap R K a)) = Ring.ordFrac R (algebraMap R K a) := by
    rw [h]
    by_cases ha : a = 0
    · simp [ha]
    · rw [Ring.ordFrac_eq_ord (R := S) (K := L) (eR a) (by simpa using ha),
        Ring.ordFrac_eq_ord (R := R) (K := K) a ha, ordMonoidWithZeroHom_ringEquiv]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  simp only [map_div₀, hbase]

end

end HodgeConjecture.SchemeCycles
