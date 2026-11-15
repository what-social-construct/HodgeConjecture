module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

/-!
# The shared exact augmented-complex criterion

This assembles an actual augmentation into a native cochain map. Exactness
at degree zero, its monomorphism, and positive exactness prove that same
map is a quasi-isomorphism. No comparison input is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SheafCohomology.AugmentedComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : C) (K : CochainComplex C ℕ) (f : S ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0)

def comparison : (CochainComplex.single₀ C).obj S ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K S).symm ⟨f, hf⟩

@[simp]
theorem comparison_zero : (comparison S K f hf).f 0 = f :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

theorem quasiIsoAt_zero (hex : (ShortComplex.mk f (K.d 0 1) hf).Exact) [Mono f] :
    QuasiIsoAt (comparison S K f hf) 0 := by
  rw [quasiIsoAt_iff' _ 0 0 1 (by simp) (by simp)]
  apply (ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)).mpr
  change (ShortComplex.mk ((comparison S K f hf).f 0) (K.d 0 1) _).Exact ∧
    Mono ((comparison S K f hf).f 0)
  simpa only [comparison_zero] using And.intro hex (inferInstance : Mono f)

theorem quasiIsoAt_positive (n : ℕ) (hex : K.ExactAt (n + 1)) :
    QuasiIsoAt (comparison S K f hf) (n + 1) := by
  apply (quasiIsoAt_iff_exactAt (comparison S K f hf) (n + 1) ?_).mpr hex
  apply HomologicalComplex.ExactAt.of_isZero
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 S (n + 1) (by omega)

theorem quasiIso (hex : (ShortComplex.mk f (K.d 0 1) hf).Exact) [Mono f]
    (hpos : ∀ n : ℕ, K.ExactAt (n + 1)) : QuasiIso (comparison S K f hf) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact quasiIsoAt_zero S K f hf hex
  | succ n => exact quasiIsoAt_positive S K f hf n (hpos n)

end HodgeConjecture.SheafCohomology.AugmentedComplex
