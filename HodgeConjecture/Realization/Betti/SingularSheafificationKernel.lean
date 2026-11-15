module

public import HodgeConjecture.Realization.Betti.SingularLocallyZero
public import HodgeConjecture.SheafCohomology.ComplexKernel

@[expose] public section

/-!
# Acyclicity of the actual global singular sheafification kernel

This is the native categorical kernel of `globalCochainsToSheaf`.
Its original inclusion identifies its degreewise range with locally
zero cochains. The existing cover kernels supply actual primitives in
this native kernel. No global surjectivity or sheaf acyclicity is assumed.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace

variable (X : TopCat.{0})

/-- The actual categorical kernel of the existing global cochain map. -/
abbrev sheafificationKernel := kernel (globalCochainsToSheaf X)

abbrev sheafificationKernelInclusion : sheafificationKernel X ⟶ complex X :=
  kernel.ι (globalCochainsToSheaf X)

theorem kernelInclusion_locallyZero (n : ℕ) (z : (sheafificationKernel X).X n) :
    LocallyZero X n ((sheafificationKernelInclusion X).f n z) :=
  (globalCochainsToSheaf_eq_zero_iff X n _).mp
    (SheafCohomology.ComplexKernel.map_inclusion_eq_zero (globalCochainsToSheaf X) n z)

/-- Membership in the range of the native inclusion is exactly local vanishing. -/
theorem mem_range_kernelInclusion_iff (n : ℕ) (φ : Cochain X n) :
    φ ∈ LinearMap.range ((sheafificationKernelInclusion X).f n).hom ↔ LocallyZero X n φ := by
  rw [SheafCohomology.ComplexKernel.range_inclusion, LinearMap.mem_ker]
  exact globalCochainsToSheaf_eq_zero_iff X n φ

/-- Every locally zero original cochain belongs to the actual categorical kernel. -/
theorem exists_kernel_preimage (n : ℕ) (φ : Cochain X n) (hφ : LocallyZero X n φ) :
    ∃ z : (sheafificationKernel X).X n, (sheafificationKernelInclusion X).f n z = φ :=
  SheafCohomology.ComplexKernel.exists_preimage (globalCochainsToSheaf X) n φ
    ((globalCochainsToSheaf_eq_zero_iff X n φ).mpr hφ)

theorem kernel_zero_cochain (z : (sheafificationKernel X).X 0) : z = 0 := by
  apply SheafCohomology.ComplexKernel.inclusion_injective (globalCochainsToSheaf X) 0
  rw [map_zero]
  exact LocallyZero.eq_zero X (kernelInclusion_locallyZero X 0 z)

theorem kernel_zero_isZero : IsZero ((sheafificationKernel X).X 0) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun z w ↦ (kernel_zero_cochain X z).trans (kernel_zero_cochain X w).symm⟩

/-- A closed element has a primitive in the same actual categorical kernel. -/
theorem exists_kernel_primitive (n : ℕ) (z : (sheafificationKernel X).X (n + 1))
    (hz : (sheafificationKernel X).d (n + 1) (n + 2) z = 0) :
    ∃ b : (sheafificationKernel X).X n, (sheafificationKernel X).d n (n + 1) b = z := by
  let φ : Cochain X (n + 1) := (sheafificationKernelInclusion X).f (n + 1) z
  have hclosed : differential X (n + 1) φ = 0 := by
    have h := SheafCohomology.ComplexKernel.inclusion_d
      (globalCochainsToSheaf X) (n + 1) (n + 2) z
    rw [hz, map_zero, complex_d] at h
    exact h.symm
  obtain ⟨b, hbLocal, hb⟩ := exists_locallyZero_primitive X n φ
    (kernelInclusion_locallyZero X (n + 1) z) hclosed
  obtain ⟨a, ha⟩ := exists_kernel_preimage X n b hbLocal
  refine ⟨a, ?_⟩
  apply SheafCohomology.ComplexKernel.inclusion_injective (globalCochainsToSheaf X) (n + 1)
  rw [SheafCohomology.ComplexKernel.inclusion_d, ha, complex_d]
  exact hb

/-- Positive exactness holds on the original native categorical kernel complex. -/
theorem sheafificationKernel_exactAt_positive (n : ℕ) :
    (sheafificationKernel X).ExactAt (n + 1) := by
  rw [(sheafificationKernel X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((sheafificationKernel X).d n (n + 1))
    ((sheafificationKernel X).d (n + 1) (n + 2)) _).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  exact exists_kernel_primitive X n

/-- The actual global sheafification-unit kernel is acyclic in every degree. -/
theorem sheafificationKernel_acyclic : (sheafificationKernel X).Acyclic := by
  intro n
  cases n with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    exact kernel_zero_isZero X
  | succ n => exact sheafificationKernel_exactAt_positive X n

theorem kernel_homology_isZero (n : ℕ) : IsZero ((sheafificationKernel X).homology n) :=
  (sheafificationKernel_acyclic X n).isZero_homology

end HodgeConjecture.SingularCochains
