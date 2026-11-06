module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

/-!
# A uniform denominator for the normalization trace dual

The existing trace dual of the unit submodule is bounded by the span of a
finite trace-dual basis. Clearing that finite basis gives one nonzero
normalization element that clears every member of the trace dual.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

variable (B K T N : Type*)
variable [CommRing B] [Field K] [CommRing T] [Field N]
variable [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
variable [IsScalarTower B K N] [IsScalarTower B T N]

/-- Membership in the existing trace dual of the unit submodule means
integral-valued trace against every normalization element. -/
theorem mem_traceDual_unit_iff (z : N) :
    z ∈ Submodule.traceDual B K (1 : Submodule T N) ↔
      ∀ t : T, Algebra.trace K N (z * algebraMap T N t) ∈
        (algebraMap B K).range := by
  rw [Submodule.mem_traceDual]
  constructor
  · intro hz t
    exact hz (algebraMap T N t) (Submodule.mem_one.mpr ⟨t, rfl⟩)
  · intro hz a ha
    obtain ⟨t, rfl⟩ := Submodule.mem_one.mp ha
    exact hz t

variable [IsIntegralClosure T B N]
variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

/-- An integral generic basis bounds the trace dual of the unit submodule
by its finite trace-dual span over the normalization. -/
theorem traceDual_unit_le_span_traceDual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K N) (hb : ∀ i, IsIntegral B (b i)) :
    Submodule.traceDual B K (1 : Submodule T N) ≤
      Submodule.span T (Set.range
        ((Algebra.traceForm K N).dualBasis (traceForm_nondegenerate K N) b)) := by
  intro z hz
  let b' := (Algebra.traceForm K N).dualBasis (traceForm_nondegenerate K N) b
  rw [← b'.sum_repr z]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := T)).mp (hb i)
  obtain ⟨r, hr⟩ := (mem_traceDual_unit_iff B K T N z).mp hz t
  have hrepr : b'.repr z i = algebraMap B K r := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← ht]
    exact hr.symm
  rw [hrepr, IsScalarTower.algebraMap_smul]
  exact ((Submodule.span T (Set.range b')).restrictScalars B).smul_mem r
    (Submodule.subset_span (Set.mem_range_self i))

variable [IsDomain B] [IsDomain T]
variable [IsFractionRing B K] [IsFractionRing T N]

/-- A single nonzero normalization element clears the entire trace dual.
No Noetherianity or module-finiteness of the normalization is required. -/
theorem exists_nonzero_traceDual_unit_denominator :
    ∃ d : T, d ≠ 0 ∧
      ∀ z ∈ Submodule.traceDual B K (1 : Submodule T N),
        algebraMap T N d * z ∈ (algebraMap T N).range := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral B K N
  let b' := (Algebra.traceForm K N).dualBasis (traceForm_nondegenerate K N) b
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors T) b'
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  intro z hz
  have hzspan := traceDual_unit_le_span_traceDual B K T N b hb hz
  have hcleared : (d : T) • z ∈ (1 : Submodule T N) := by
    refine Submodule.span_induction
      (p := fun z _ => (d : T) • z ∈ (1 : Submodule T N)) ?_ ?_ ?_ ?_ hzspan
    · rintro _ ⟨i, rfl⟩
      exact Submodule.mem_one.mpr (hd i)
    · simp
    · intro x y hx hy ihx ihy
      simpa only [smul_add] using (1 : Submodule T N).add_mem ihx ihy
    · intro a x hx ih
      rw [smul_smul, mul_comm, ← smul_smul]
      exact (1 : Submodule T N).smul_mem a ih
  simpa only [Algebra.smul_def, RingHom.mem_range] using Submodule.mem_one.mp hcleared

end

end HodgeConjecture.NormalizationInertia
