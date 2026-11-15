module

public import HodgeConjecture.SheafCohomology.ComplexKernel
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

/-! # Comparing a surjective cochain map with its actual native kernel -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SheafCohomology.ComplexKernel

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {k : Type u} [CommRing k]
  {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

/-- The native kernel sequence and its actual long exact sequence prove the comparison. -/
theorem quasiIso_of_surjective_of_acyclic (hsurj : ∀ n, Function.Surjective (f.f n))
    (hker : (kernel f).Acyclic) : QuasiIso f := by
  have : Epi f := epi_of_epi_f f (fun n ↦ (ModuleCat.epi_iff_surjective _).mpr (hsurj n))
  have : Epi (ShortComplex.kernelSequence f).g := by change Epi f; infer_instance
  have hs : (ShortComplex.kernelSequence f).ShortExact := ⟨ShortComplex.kernelSequence_exact f⟩
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap f n) :=
    (hs.homology_exact₂ n).mono_g ((hker n).isZero_homology.eq_zero_of_src _)
  have : Epi (homologyMap f n) :=
    (hs.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((hker (n + 1)).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end HodgeConjecture.SheafCohomology.ComplexKernel
