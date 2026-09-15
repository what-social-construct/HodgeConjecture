import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.SetTheory.Cardinal.ToNat

/-!
# Strict transcendence-degree drop under a proper domain quotient

A transcendence basis of a quotient can be lifted to algebraically
independent elements of the original algebra. The quotient map is
injective on their generated subalgebra. If that lifted family were
already a transcendence basis, any nonzero element of the kernel would
be algebraic over that subalgebra, contradicting the injectivity there.

For finite transcendence degree, a noninjective surjection between
domains therefore strictly lowers transcendence degree. Applied to
actual prime quotients of a finite-type algebra, this gives strict
antitonicity along prime inclusion, including for reducible ambient
algebras. This is strict decrease, not yet an exact unit-step formula.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open Function Set Algebra MvPolynomial Cardinal

noncomputable section

universe u v

private theorem kernel_comap_adjoin_eq_bot
    (k : Type u) [Field k] {A B : Type v} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) {ι : Type v} (x : ι → A)
    (hx : AlgebraicIndependent k (f ∘ x)) :
    (RingHom.ker f.toRingHom).comap
      (algebraMap (Algebra.adjoin k (Set.range x)) A) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change f (a : A) = 0 at ha
  rw [Ideal.mem_bot]
  have hm : (a : A) ∈ (aeval x : MvPolynomial ι k →ₐ[k] A).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact a.property
  obtain ⟨p, hp⟩ := hm
  change (aeval x : MvPolynomial ι k →ₐ[k] A) p = (a : A) at hp
  have hcomp : (aeval (f ∘ x) : MvPolynomial ι k →ₐ[k] B) = f.comp (aeval x) := by
    ext
    simp
  have hpzero : (aeval (f ∘ x) : MvPolynomial ι k →ₐ[k] B) p = 0 := by
    rw [hcomp]
    change f (aeval x p) = 0
    rwa [hp]
  have hp0 := hx.eq_zero_of_aeval_eq_zero p hpzero
  apply Subtype.ext
  simpa only [hp0, map_zero] using hp.symm

/-- A noninjective surjection between domains strictly lowers finite
transcendence degree, by its actual nonzero kernel. -/
theorem trdeg_lt_of_surjective_of_not_injective
    (k : Type u) [Field k] {A B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) (hnot : ¬ Function.Injective f)
    (hfin : Algebra.trdeg k A < ℵ₀) : Algebra.trdeg k B < Algebra.trdeg k A := by
  classical
  apply lt_of_le_of_ne (trdeg_le_of_surjective f hf)
  intro heq
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k B
  let x : s → A := fun t ↦ (hf t.val).choose
  have hfx : f ∘ x = (Subtype.val : s → B) :=
    funext fun t ↦ (hf t.val).choose_spec
  have hxmap : AlgebraicIndependent k (f ∘ x) := by rw [hfx]; exact hs.1
  have hx : AlgebraicIndependent k x := hxmap.of_comp f
  have hxbase : IsTranscendenceBasis k x :=
    hx.isTranscendenceBasis_of_trdeg_le hfin (by rw [hs.cardinalMk_eq_trdeg, heq])
  letI := hxbase.isAlgebraic
  have hker : RingHom.ker f.toRingHom ≠ ⊥ := by
    intro h
    exact hnot ((RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr h)
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hnonzero := Ideal.comap_ne_bot_of_algebraic_mem hane ha
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin k (Set.range x)) a)
  exact hnonzero (kernel_comap_adjoin_eq_bot k f x hxmap)

/-- Strict inclusion of prime ideals strictly decreases the actual
quotient algebras' transcendence degrees. The ambient algebra may be reducible. -/
theorem primeQuotient_trdeg_strictAnti (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    StrictAnti (fun p : PrimeSpectrum A ↦ Algebra.trdeg k (A ⧸ p.asIdeal)) := by
  intro p q hpq
  let f : A ⧸ p.asIdeal →ₐ[k] A ⧸ q.asIdeal :=
    Ideal.Quotient.liftₐ p.asIdeal (Ideal.Quotient.mkₐ k q.asIdeal)
      (fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hpq.le ha))
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hnot : ¬ Function.Injective f := by
    intro hinj
    obtain ⟨a, haq, hap⟩ := SetLike.exists_of_lt hpq
    apply hap
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hinj
    change Ideal.Quotient.mk q.asIdeal a = f 0
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr haq
  exact trdeg_lt_of_surjective_of_not_injective k f hf hnot
    (trdeg_lt_aleph0 (R := k) (S := A ⧸ p.asIdeal))

/-- The finite natural-valued quotient transcendence degrees retain
strict antitonicity; conversion to natural numbers is lossless here. -/
theorem primeQuotient_trdeg_toNat_strictAnti (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    StrictAnti (fun p : PrimeSpectrum A ↦ (Algebra.trdeg k (A ⧸ p.asIdeal)).toNat) := by
  intro p q hpq
  exact Cardinal.toNat_lt_toNat (primeQuotient_trdeg_strictAnti k A hpq)
    (trdeg_lt_aleph0 (R := k) (S := A ⧸ p.asIdeal))

end

end HodgeConjecture.SchemeCycles
