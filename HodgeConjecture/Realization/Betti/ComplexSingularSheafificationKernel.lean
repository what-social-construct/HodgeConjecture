module

public import HodgeConjecture.Realization.Betti.ComplexSingularLocallyZero
public import HodgeConjecture.SheafCohomology.ComplexKernel

@[expose] public noncomputable section

/-!
# Acyclicity of the native complex singular sheafification kernel

The categorical kernel of the original complex-valued global unit consists
degreewise of cochains vanishing on an open neighborhood of every point.
Cover-small chain duality supplies primitives inside that same kernel.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace HodgeConjecture.SingularCoefficientChange

open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace

variable (X : TopCat.{0})

abbrev sheafificationKernel := kernel (globalCochainsToSheaf X)

abbrev sheafificationKernelInclusion : sheafificationKernel X ⟶ complexCochains X :=
  kernel.ι (globalCochainsToSheaf X)

theorem kernelInclusion_locallyZero (n : ℕ) (z : (sheafificationKernel X).X n) :
    LocallyZero X n ((sheafificationKernelInclusion X).f n z) :=
  (globalCochainsToSheaf_eq_zero_iff X n _).mp
    (SheafCohomology.ComplexKernel.map_inclusion_eq_zero (globalCochainsToSheaf X) n z)

theorem mem_range_kernelInclusion_iff (n : ℕ) (φ : (complexCochains X).X n) :
    φ ∈ LinearMap.range ((sheafificationKernelInclusion X).f n).hom ↔ LocallyZero X n φ := by
  rw [SheafCohomology.ComplexKernel.range_inclusion, LinearMap.mem_ker]
  exact globalCochainsToSheaf_eq_zero_iff X n φ

theorem exists_kernel_preimage (n : ℕ) (φ : (complexCochains X).X n)
    (hφ : LocallyZero X n φ) :
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

theorem exists_kernel_primitive (n : ℕ) (z : (sheafificationKernel X).X (n + 1))
    (hz : (sheafificationKernel X).d (n + 1) (n + 2) z = 0) :
    ∃ b : (sheafificationKernel X).X n, (sheafificationKernel X).d n (n + 1) b = z := by
  let φ : (complexCochains X).X (n + 1) := (sheafificationKernelInclusion X).f (n + 1) z
  have hclosed : (complexCochains X).d (n + 1) (n + 2) φ = 0 := by
    have h := SheafCohomology.ComplexKernel.inclusion_d
      (globalCochainsToSheaf X) (n + 1) (n + 2) z
    rw [hz, map_zero] at h
    exact h.symm
  obtain ⟨b, hbLocal, hb⟩ := exists_locallyZero_primitive X n φ
    (kernelInclusion_locallyZero X (n + 1) z) hclosed
  obtain ⟨a, ha⟩ := exists_kernel_preimage X n b hbLocal
  refine ⟨a, ?_⟩
  apply SheafCohomology.ComplexKernel.inclusion_injective (globalCochainsToSheaf X) (n + 1)
  rw [SheafCohomology.ComplexKernel.inclusion_d]
  change (complexCochains X).d n (n + 1)
    ((sheafificationKernelInclusion X).f n a) = φ
  rw [ha]
  exact hb

theorem sheafificationKernel_exactAt_positive (n : ℕ) :
    (sheafificationKernel X).ExactAt (n + 1) := by
  rw [(sheafificationKernel X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((sheafificationKernel X).d n (n + 1))
    ((sheafificationKernel X).d (n + 1) (n + 2)) _).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  exact exists_kernel_primitive X n

theorem sheafificationKernel_acyclic : (sheafificationKernel X).Acyclic := by
  intro n
  cases n with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    exact kernel_zero_isZero X
  | succ n => exact sheafificationKernel_exactAt_positive X n

theorem kernel_homology_isZero (n : ℕ) : IsZero ((sheafificationKernel X).homology n) :=
  (sheafificationKernel_acyclic X n).isZero_homology

end HodgeConjecture.SingularCoefficientChange
