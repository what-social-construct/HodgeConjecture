module

public import HodgeConjecture.Realization.Betti.ComplexSingularPresheaf
public import HodgeConjecture.SheafCohomology.LocalExactness
public import HodgeConjecture.SheafCohomology.AugmentedComplex

@[expose] public noncomputable section

/-!
# The native complex constant-sheaf resolution

The original complex-valued functionals, with their actual transpose
differential, resolve the native complex constant sheaf. The local
neighborhood argument and sheafification criterion are shared with the
original rational resolution.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite

namespace HodgeConjecture.SingularCoefficientChange

variable (X : TopCat.{0})

abbrev constantSheaf := SheafCohomology.ConstantLift.sheaf ℂ X

def augmentation : constantSheaf X ⟶ cochainSheaf X 0 :=
  (SheafCohomology.sheafification ℂ X).map (constantPresheafMap X)

theorem augmentation_differential : augmentation X ≫ sheafDifferential X 0 = 0 := by
  unfold augmentation
  change (SheafCohomology.sheafification ℂ X).map (constantPresheafMap X) ≫
    (SheafCohomology.sheafification ℂ X).map (presheafDifferential X 0) = 0
  rw [← Functor.map_comp, constantPresheafMap_differential, Functor.map_zero]

instance augmentation_mono : Mono (augmentation X) := by
  apply SheafCohomology.ConstantLift.map_mono
  intro U hU
  let : Nonempty ((Opens.toTopCat X).obj U) := hU.to_subtype
  exact constantCochain_injective _

def comparison : (CochainComplex.single₀ _).obj (constantSheaf X) ⟶ sheafComplex X :=
  SheafCohomology.AugmentedComplex.comparison _ _ (augmentation X)
    (by simpa only [SheafCohomology.CochainPresheaf.sheafComplex_d] using augmentation_differential X)

@[simp]
theorem comparison_zero : (comparison X).f 0 = augmentation X :=
  SheafCohomology.AugmentedComplex.comparison_zero _ _ _ _

variable [StronglyLocallyContractibleSpace X]

theorem augmentation_exact :
    (ShortComplex.mk (augmentation X) (sheafDifferential X 0) (augmentation_differential X)).Exact := by
  apply SheafCohomology.LocalExactness.sheafify_exact_of_exists_local_preimage
    (ShortComplex.mk (constantPresheafMap X) (presheafDifferential X 0) (constantPresheafMap_differential X))
  exact SheafCohomology.CochainPresheaf.locally_constant_zero ℂ functor X constantCochain
    (fun f c ↦ pullback_constantCochain _ f c)
    (fun S _ x z hz ↦ closed_zero_constant S x z hz)

theorem sheaf_exact_positive (n : ℕ) :
    (ShortComplex.mk (sheafDifferential X n) (sheafDifferential X (n + 1))
      (SheafCohomology.CochainPresheaf.sheafDifferential_comp ℂ functor X n)).Exact := by
  apply SheafCohomology.LocalExactness.sheafify_exact_of_exists_local_preimage
    (ShortComplex.mk (presheafDifferential X n) (presheafDifferential X (n + 1))
      (SheafCohomology.CochainPresheaf.differential_comp ℂ functor X n))
  exact SheafCohomology.CochainPresheaf.locally_exact_positive ℂ functor X
    (fun S _ j z hz ↦ exists_primitive S j z hz) n

theorem sheafComplex_exactAt_positive (n : ℕ) : (sheafComplex X).ExactAt (n + 1) := by
  rw [(sheafComplex X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((sheafComplex X).d n (n + 1))
    ((sheafComplex X).d (n + 1) (n + 2)) _).Exact
  simpa only [SheafCohomology.CochainPresheaf.sheafComplex_d] using sheaf_exact_positive X n

theorem comparison_quasiIso : QuasiIso (comparison X) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIso
  · simpa only [SheafCohomology.CochainPresheaf.sheafComplex_d] using augmentation_exact X
  · exact sheafComplex_exactAt_positive X

end HodgeConjecture.SingularCoefficientChange
