module

public import HodgeConjecture.Realization.DeRham.DegreeFiltration
public import HodgeConjecture.Realization.DeRham.TwoTermHypercohomology

@[expose] public section

/-!
# The degree-one filtration piece of an actual two-term complex

When the original terms above degree one are zero objects, the native
degree filtration's level one is the original degree-one term placed in
degree one. The comparison below retains the actual inclusion into the
original complex, rather than choosing an equivalence after cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.DegreeFiltration

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))

/-- Include the original degree-one singleton into the actual native degree-filtered piece. -/
def degreeOneToComplex : TwoTermComplex.degreeOne K ⟶ complex K 1 :=
  HomologicalComplex.mkHomFromSingle (xIso K 1 1 (by decide)).inv
    (fun n hn ↦ by
      change 1 + 1 = n at hn
      subst n
      exact (isZero_X_of_twoTerm K hK 1 2 (by decide)).eq_of_tgt _ _)

/-- The native degree-one piece and original singleton have isomorphic terms in every degree. -/
instance degreeOneToComplex_isIso : IsIso (degreeOneToComplex K hK) := by
  have (n : ℕ) : IsIso ((degreeOneToComplex K hK).f n) := by
    by_cases hn : n = 1
    · subst n
      rw [degreeOneToComplex, HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · have hs := isZero_single_obj_X (.up ℕ) 1 (K.X 1) n hn
      have ht : IsZero ((complex K 1).X n) := by
        by_cases hn0 : n = 0
        · subst n
          exact isZero_X_of_lt K 1 0 (by decide)
        · exact isZero_X_of_twoTerm K hK 1 n (by omega)
      exact hs.isIso ht _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The singleton comparison retains the original actual inclusion into the complex. -/
@[reassoc]
theorem degreeOneToComplex_inclusion :
    degreeOneToComplex K hK ≫ inclusion K 1 = TwoTermComplex.inclusion K hK := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 1
  · subst n
    simp [degreeOneToComplex, TwoTermComplex.inclusion, inclusion_f]
  · exact (isZero_single_obj_X (.up ℕ) 1 (K.X 1) n hn).eq_of_src _ _

/-- The actual level-one filtered piece is the original one-form singleton for two-term complexes. -/
def degreeOneIso : complex K 1 ≅ TwoTermComplex.degreeOne K :=
  (asIso (degreeOneToComplex K hK)).symm

/-- This isomorphism identifies the filtration inclusion with the original degree-one inclusion. -/
@[reassoc]
theorem degreeOneIso_hom_inclusion :
    (degreeOneIso K hK).hom ≫ TwoTermComplex.inclusion K hK = inclusion K 1 := by
  rw [← degreeOneToComplex_inclusion K hK]
  simp [degreeOneIso]

end HodgeConjecture.DegreeFiltration
