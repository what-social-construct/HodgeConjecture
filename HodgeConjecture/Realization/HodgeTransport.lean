module

public import HodgeConjecture.Realization.HodgeFiltration

@[expose] public section

/-!
# Transport along a rational cohomology equivalence

Scalar extension of the original rational equivalence commutes with the
canonical conjugation. It therefore transports opposed filtrations and
their rational Hodge targets, without choosing a new real structure.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture

universe u v

variable {H : Type u} {K : Type v}
variable [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K]

namespace RationalComplexification

/-- Rational scalar extension preserves the canonical conjugate subspace. -/
theorem conjugateSubmodule_map (e : H ≃ₗ[ℚ] K) (W : Submodule ℂ (Space H)) :
    conjugateSubmodule K (W.map (LinearEquiv.baseChange ℚ ℂ _ _ e).toLinearMap) =
      (conjugateSubmodule H W).map (LinearEquiv.baseChange ℚ ℂ _ _ e).toLinearMap := by
  ext z
  simp only [mem_conjugateSubmodule, Submodule.mem_map_equiv]
  change map e.symm.toLinearMap (conjugation K z) ∈ W ↔
    conjugation H (map e.symm.toLinearMap z) ∈ W
  rw [conjugation_map]

end RationalComplexification

namespace HodgeFiltration

/-- Membership in a transported rational target is membership under the original rational inverse. -/
theorem mem_rationalHodgeClasses_map (e : H ≃ₗ[ℚ] K)
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ) (x : K) :
    x ∈ rationalHodgeClasses (fun k ↦ (F k).map (LinearEquiv.baseChange ℚ ℂ _ _ e).toLinearMap) p ↔
      e.symm x ∈ rationalHodgeClasses F p := by
  simp only [mem_rationalHodgeClasses_iff, Submodule.mem_map_equiv]
  rfl

end HodgeFiltration

namespace PureRationalHodgeStructure

/-- Transport purity through the scalar extension of an actual rational equivalence. -/
def transport {weight : ℤ} (S : PureRationalHodgeStructure H weight) (e : H ≃ₗ[ℚ] K) :
    PureRationalHodgeStructure K weight where
  finiteDimensional := by
    have := S.finiteDimensional
    exact e.finiteDimensional
  filtration p := (S.filtration p).map (LinearEquiv.baseChange ℚ ℂ _ _ e).toLinearMap
  antitone _p _q hpq := Submodule.map_mono (S.antitone hpq)
  exhaustive := by
    obtain ⟨p, hp⟩ := S.exhaustive
    refine ⟨p, ?_⟩
    rw [hp, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LinearEquiv.baseChange ℚ ℂ _ _ e).surjective
  separated := by
    obtain ⟨p, hp⟩ := S.separated
    exact ⟨p, by rw [hp, Submodule.map_bot]⟩
  opposed p := by
    rw [RationalComplexification.conjugateSubmodule_map]
    exact Submodule.isCompl_map (LinearEquiv.baseChange ℚ ℂ _ _ e) (S.opposed p)

theorem mem_rationalHodgeClasses_transport (p : ℤ)
    (S : PureRationalHodgeStructure H (2 * p)) (e : H ≃ₗ[ℚ] K) (x : K) :
    x ∈ rationalHodgeClasses p (S.transport e) ↔
      e.symm x ∈ rationalHodgeClasses p S :=
  HodgeFiltration.mem_rationalHodgeClasses_map e S.filtration p x

end PureRationalHodgeStructure

end HodgeConjecture
