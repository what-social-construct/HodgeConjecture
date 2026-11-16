module

public import HodgeConjecture.Cycles.UFDPrincipalDivisor
public import HodgeConjecture.Cycles.RationalChow

/-!
# Codimension-one Chow groups of affine UFDs

When every degree-one carrier has codimension one and the generic point has
degree two, every generator of the degree-one cycle module is the actual
principal divisor of a height-one prime generator. Hence the existing
principal-relation submodule fills the whole cycle module.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TensorProduct

noncomputable section

universe u

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]
  [UniqueFactorizationMonoid A]

/-- For an affine UFD with generic degree two and every degree-one carrier
at codimension one, every degree-one cycle is an actual finite
sum of principal divisors. -/
theorem spec_principalRelations_one_eq_top
    (δ : DimensionFunction (Spec A))
    (hgeneric : δ (genericPoint (Spec A)) = 2)
    (hgrade : ∀ W : IntegralClosedSubscheme (Spec A),
      supportDegree δ W = 1 → supportCodimension W = 1) :
    principalRelations δ 1 = ⊤ := by
  have hle : cyclesOfDegree ℤ δ 1 ≤
      (principalRelations δ 1).map (cyclesOfDegree ℤ δ 1).subtype := by
    change Finsupp.supported ℤ ℤ {W | supportDegree δ W = 1} ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨W, hW, rfl⟩
    change fundamentalCycle ℤ W ∈
      (principalRelations δ 1).map (cyclesOfDegree ℤ δ 1).subtype
    obtain ⟨f, hf⟩ := spec_fundamentalCycle_eq_principalDivisor A W (hgrade W hW)
    have hdeg : δ (genericPoint (Spec A)) - 1 = 1 := by omega
    have hpd : (⟨principalDivisor (Spec A) f,
        by simpa only [hdeg] using principalDivisor_mem_cyclesOfDegree δ f⟩ :
          cyclesOfDegree ℤ δ 1) ∈ principalRelations δ 1 :=
      principalDivisor_mem_principalRelations_of_genericDegree_eq
        (Spec A) δ f 1 hdeg
    refine ⟨⟨fundamentalCycle ℤ W,
      fundamentalCycle_mem_cyclesOfDegree ℤ δ 1 W hW⟩, ?_, rfl⟩
    change (⟨fundamentalCycle ℤ W,
      fundamentalCycle_mem_cyclesOfDegree ℤ δ 1 W hW⟩ :
        cyclesOfDegree ℤ δ 1) ∈ principalRelations δ 1
    have hceq : (⟨fundamentalCycle ℤ W,
        fundamentalCycle_mem_cyclesOfDegree ℤ δ 1 W hW⟩ :
          cyclesOfDegree ℤ δ 1) =
        (⟨principalDivisor (Spec A) f,
          by simpa only [hdeg] using principalDivisor_mem_cyclesOfDegree δ f⟩ :
          cyclesOfDegree ℤ δ 1) := Subtype.ext hf
    exact hceq.symm ▸ hpd
  apply Submodule.eq_top_iff'.mpr
  intro c
  obtain ⟨z, hz, hzc⟩ := hle c.property
  have heq : z = c := Subtype.ext hzc
  exact heq ▸ hz

/-- The existing degree-one Chow quotient of such an affine UFD is zero. -/
theorem spec_chowGroup_one_eq_zero
    (δ : DimensionFunction (Spec A))
    (hgeneric : δ (genericPoint (Spec A)) = 2)
    (hgrade : ∀ W : IntegralClosedSubscheme (Spec A),
      supportDegree δ W = 1 → supportCodimension W = 1)
    (c : ChowGroup δ 1) : c = 0 := by
  have htop := spec_principalRelations_one_eq_top A δ hgeneric hgrade
  obtain ⟨z, rfl⟩ := classMap_surjective δ 1 c
  apply (classMap_eq_zero_iff δ 1 z).mpr
  rw [htop]
  trivial

/-- The rational Chow quotient vanishes for the same actual principal
relations, by the proved rationalization equivalence. -/
theorem spec_rationalChowGroup_one_eq_zero
    (δ : DimensionFunction (Spec A))
    (hgeneric : δ (genericPoint (Spec A)) = 2)
    (hgrade : ∀ W : IntegralClosedSubscheme (Spec A),
      supportDegree δ W = 1 → supportCodimension W = 1)
    (c : RationalChowGroup δ 1) : c = 0 := by
  have ht : ∀ t : ℚ ⊗[ℤ] ChowGroup δ 1, t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul q z => rw [spec_chowGroup_one_eq_zero A δ hgeneric hgrade z, tmul_zero]
    | add t s ht hs => rw [ht, hs, zero_add]
  apply (chowRationalizationEquiv δ 1).symm.injective
  simpa using ht ((chowRationalizationEquiv δ 1).symm c)

end

end HodgeConjecture.SchemeCycles

end
