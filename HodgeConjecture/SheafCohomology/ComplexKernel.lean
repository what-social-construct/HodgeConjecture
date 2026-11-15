module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# The native kernel of a module-valued cochain map, degree by degree

Evaluation preserves exactness. The original kernel inclusion therefore
has exactly the usual linear-map kernel as its range in every degree.
This exposes actual elements of the native categorical kernel without
constructing another complex of kernel modules.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SheafCohomology.ComplexKernel

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {k : Type u} [CommRing k]
  {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

/-- The actual native kernel sequence stays exact under degreewise evaluation. -/
theorem degree_exact (n : ℕ) :
    ((ShortComplex.kernelSequence f).map (eval _ _ n)).Exact :=
  (ShortComplex.kernelSequence_exact f).map (eval _ _ n)

theorem range_inclusion (n : ℕ) :
    LinearMap.range ((kernel.ι f).f n).hom = LinearMap.ker (f.f n).hom :=
  (degree_exact f n).moduleCat_range_eq_ker

/-- A cochain killed by the map lifts to an element of its actual categorical kernel. -/
theorem exists_preimage (n : ℕ) (z : K.X n) (hz : f.f n z = 0) :
    ∃ a : (kernel f).X n, (kernel.ι f).f n a = z :=
  (ShortComplex.moduleCat_exact_iff _).mp (degree_exact f n) z hz

theorem inclusion_injective (n : ℕ) : Function.Injective ((kernel.ι f).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

theorem map_inclusion_eq_zero (n : ℕ) (a : (kernel f).X n) :
    f.f n ((kernel.ι f).f n a) = 0 := by
  have h := congrArg (fun g ↦ (g.f n).hom a) (kernel.condition f)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] using h

theorem inclusion_d (i j : ℕ) (a : (kernel f).X i) :
    (kernel.ι f).f j ((kernel f).d i j a) = K.d i j ((kernel.ι f).f i a) := by
  have h := congrArg (fun q ↦ q.hom a) ((kernel.ι f).comm i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

end HodgeConjecture.SheafCohomology.ComplexKernel
