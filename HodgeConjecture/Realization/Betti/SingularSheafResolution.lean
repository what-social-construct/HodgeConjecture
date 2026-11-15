module

public import HodgeConjecture.Realization.Betti.SingularLocalExactness
public import HodgeConjecture.SheafCohomology.LocalExactness
public import HodgeConjecture.SheafCohomology.AugmentedComplex

@[expose] public section

/-!
# The actual constant-sheaf resolution by singular cochain sheaves

The augmentation and differential are obtained by native sheafification
of the existing singular cochains. Contractible neighborhood bases prove
local exactness, hence a quasi-isomorphism in every degree.

This is a statement about sheaf complexes. Computing derived global
sections by the original global cochains requires a further comparison.
In particular, no flasqueness claim is inferred merely from surjective
restriction maps of the raw presheaf.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory TopologicalSpace Opposite

variable (X : TopCat.{0})

/-- The same native rational constant sheaf used by the shared sheaf layer. -/
abbrev constantSheaf := SheafCohomology.ConstantLift.sheaf ℚ X

/-- Sheafification of the literal constant singular zero-cochain. -/
def augmentation : constantSheaf X ⟶ cochainSheaf X 0 :=
  (SheafCohomology.sheafification ℚ X).map (constantPresheafMap X)

theorem augmentation_differential : augmentation X ≫ sheafDifferential X 0 = 0 := by
  rw [augmentation, sheafDifferential, ← Functor.map_comp,
    constantPresheafMap_differential, Functor.map_zero]

instance augmentation_mono : Mono (augmentation X) := by
  apply SheafCohomology.ConstantLift.map_mono
  intro U hU
  let : Nonempty ((Opens.toTopCat X).obj U) := hU.to_subtype
  exact constantCochain_injective _

/-- The augmentation is the shared augmented-complex construction. -/
def comparison : (CochainComplex.single₀ _).obj (constantSheaf X) ⟶ sheafComplex X :=
  SheafCohomology.AugmentedComplex.comparison (constantSheaf X) (sheafComplex X)
    (augmentation X) (by simpa only [sheafComplex_d] using augmentation_differential X)

@[simp]
theorem comparison_zero : (comparison X).f 0 = augmentation X :=
  SheafCohomology.AugmentedComplex.comparison_zero _ _ _ _

variable [StronglyLocallyContractibleSpace X]

theorem augmentation_exact :
    (ShortComplex.mk (augmentation X) (sheafDifferential X 0)
      (augmentation_differential X)).Exact := by
  exact SheafCohomology.LocalExactness.sheafify_exact_of_exists_local_preimage
    (ShortComplex.mk (constantPresheafMap X) (presheafDifferential X 0)
      (constantPresheafMap_differential X))
    (fun U z hz p hp ↦ locally_constant_zero X U z hz p hp)

/-- Every positive-degree window is exact on the original stalks. -/
theorem sheaf_exact_positive (n : ℕ) :
    (ShortComplex.mk (sheafDifferential X n) (sheafDifferential X (n + 1))
      (sheafDifferential_comp X n)).Exact := by
  apply SheafCohomology.LocalExactness.sheafify_exact_of_exists_local_preimage
    (ShortComplex.mk (presheafDifferential X n) (presheafDifferential X (n + 1))
      (presheafDifferential_comp X n))
  intro U z hz p hp
  change (complex ((Opens.toTopCat X).obj U)).d (n + 1) (n + 1 + 1) z = 0 at hz
  rw [complex_d] at hz
  obtain ⟨V, hVU, hpV, b, hb⟩ := locally_exact_positive X n U z hz p hp
  refine ⟨V, hVU, hpV, b, ?_⟩
  change (complex ((Opens.toTopCat X).obj V)).d n (n + 1) b = _
  rw [complex_d]
  exact hb

theorem sheafComplex_exactAt_positive (n : ℕ) : (sheafComplex X).ExactAt (n + 1) := by
  rw [(sheafComplex X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk ((sheafComplex X).d n (n + 1))
    ((sheafComplex X).d (n + 1) (n + 2)) _).Exact
  simpa only [sheafComplex_d] using sheaf_exact_positive X n

/-- The rational constant sheaf and the actual singular cochain sheaves
are quasi-isomorphic in all degrees. -/
theorem comparison_quasiIso : QuasiIso (comparison X) := by
  unfold comparison
  apply SheafCohomology.AugmentedComplex.quasiIso
  · simpa only [sheafComplex_d] using augmentation_exact X
  · exact sheafComplex_exactAt_positive X

end HodgeConjecture.SingularCochains
