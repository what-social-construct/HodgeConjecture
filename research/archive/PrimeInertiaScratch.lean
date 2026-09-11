/-!
Archived exploratory source.  Its prime-inertia and invariant-ring
constructions were promoted to the active normalization modules; this file is
retained only as provenance and is not a build target.
-/

import HodgeConjecture.Boundary.Normalization.FixedRingUnramified
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false

#check Ideal.Quotient.stabilizerHom
#check Ideal.Quotient.stabilizerHom_apply
#check Subgroup.map
#check Subgroup.mem_map
#check MulAction.stabilizer
#check Ideal.Quotient.eq_zero_iff_mem
#check Ideal.pointwise_smul_eq_comap
#check Ideal.mem_pointwise_smul_iff_inv_smul_mem
#check Ideal.smul_mem_pointwise_smul_iff
#check MonoidHom.mem_ker
#check IsIntegralClosure.equiv
#check IsIntegrallyClosed.isIntegral_iff
#check IntermediateField.botEquiv
#check Algebra.botEquivOfInjective

namespace Scratch

open scoped Pointwise

variable {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Group G] [MulSemiringAction G S] [SMulCommClass G A S]

noncomputable def primeInertiaSubgroup
    (Q : Ideal S) [Q.IsPrime] : Subgroup G :=
  (MonoidHom.ker
    (Ideal.Quotient.stabilizerHom Q (Q.under A) G)).map
      (MulAction.stabilizer G Q).subtype

theorem mem_primeInertiaSubgroup_iff
    (Q : Ideal S) [Q.IsPrime] (g : G) :
    g ∈ primeInertiaSubgroup (A := A) Q ↔
      g • Q = Q ∧ ∀ x : S, g • x - x ∈ Q := by
  constructor
  · intro hg
    rw [primeInertiaSubgroup, Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hstab : (h : G) • Q = Q := h.property
    refine ⟨hstab, ?_⟩
    intro x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub]
    change
      (Ideal.Quotient.stabilizerHom Q (Q.under A) G h)
          (Ideal.Quotient.mk Q x) -
        Ideal.Quotient.mk Q x = 0
    rw [(MonoidHom.mem_ker.mp hh)]
    exact sub_self _
  · rintro ⟨hstab, hres⟩
    let h : MulAction.stabilizer G Q := ⟨g, hstab⟩
    rw [primeInertiaSubgroup, Subgroup.mem_map]
    refine ⟨h, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (g • x) = Ideal.Quotient.mk Q x
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hres x

end Scratch

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

noncomputable def testBaseEquiv
    [PerfectField K] [IsIntegrallyClosed B]
    (D : CollisionFoundations.NormalClosureData K L N) :
    B ≃ₐ[B]
      FixedSubgroupNormalizationRing
        (B := B) (⊤ : Subgroup D.galoisGroup) := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra.IsSeparable K N :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : IsGalois K N := IsGalois.mk
  let eFixed :
      IntermediateField.fixedField
          (⊤ : Subgroup D.galoisGroup) ≃ₐ[K] K :=
    (IntermediateField.equivOfEq
      (IsGalois.fixedField_top (F := K) (E := N))).trans
        (IntermediateField.botEquiv K N)
  let eClosure :
      integralClosure B
          (IntermediateField.fixedField
            (⊤ : Subgroup D.galoisGroup)) ≃ₐ[B]
        integralClosure B K :=
    (eFixed.restrictScalars B).mapIntegralClosure
  let eBase : integralClosure B K ≃ₐ[B] B :=
    IsIntegralClosure.equiv B (integralClosure B K) K B
  exact eBase.symm.trans <|
    eClosure.symm.trans <|
      fixedFieldNormalizationEquivFixedRing
        (B := B) (⊤ : Subgroup D.galoisGroup)

end

end HodgeConjecture.NormalizationInertia
