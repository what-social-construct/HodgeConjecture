module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

@[expose] public section

/-!
# The actual decreasing degree filtration of a nonnegative cochain complex

The term at level `p` is the native stupid truncation: restrict the
original complex to degrees `p, p+1, …`, then extend by zero. Its retained
objects and arrows are the original ones. The inclusion and decreasing
transition maps below are actual morphisms of complexes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.DegreeFiltration

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The native shape embedding whose image is the retained degree range. -/
def embedding (p : ℕ) : (ComplexShape.up ℕ).Embedding (.up ℕ) :=
  ComplexShape.embeddingUp'Add (1 : ℕ) p

instance (p : ℕ) : (embedding p).IsRelIff := by
  unfold embedding
  infer_instance

/-- Actual brutal degree truncation; no homology kernel or cokernel replaces a retained term. -/
def complex (K : CochainComplex C ℕ) (p : ℕ) : CochainComplex C ℕ :=
  K.stupidTrunc (embedding p)

/-- A retained term is its original term, through the native extension coordinate. -/
def xIso (K : CochainComplex C ℕ) (p n : ℕ) (hn : p ≤ n) :
    (complex K p).X n ≅ K.X n :=
  K.stupidTruncXIso (embedding p) (show (n - p) + p = n from Nat.sub_add_cancel hn)

/-- All terms below the filtration degree are genuinely zero objects. -/
theorem isZero_X_of_lt (K : CochainComplex C ℕ) (p n : ℕ) (hn : n < p) :
    IsZero ((complex K p).X n) :=
  K.isZero_stupidTrunc_X (embedding p) n (by
    intro i
    change i + p ≠ n
    omega)

/-- The retained differential is exactly the original differential under the native coordinates. -/
theorem d_eq (K : CochainComplex C ℕ) (p i j : ℕ) (hi : p ≤ i) (hj : p ≤ j) :
    (complex K p).d i j = (xIso K p i hi).hom ≫ K.d i j ≫ (xIso K p j hj).inv := by
  unfold complex xIso HomologicalComplex.stupidTrunc HomologicalComplex.stupidTruncXIso
  rw [extend_d_eq _ _ (Nat.sub_add_cancel hi) (Nat.sub_add_cancel hj)]
  rw [restriction_d_eq _ _ (Nat.sub_add_cancel hi) (Nat.sub_add_cancel hj)]
  simp [HomologicalComplex.restrictionXIso]

/-- The original-coordinate inclusion in one degree. -/
def inclusionComponent (K : CochainComplex C ℕ) (p n : ℕ) :
    (complex K p).X n ⟶ K.X n :=
  if hn : p ≤ n then (xIso K p n hn).hom else 0

/-- Inclusion of the actual degree-filtered complex into the original complex. -/
def inclusion (K : CochainComplex C ℕ) (p : ℕ) : complex K p ⟶ K where
  f n := inclusionComponent K p n
  comm' i j hij := by
    by_cases hi : p ≤ i
    · have hj : p ≤ j := by change i + 1 = j at hij; omega
      simp only [inclusionComponent, dite_eq_left hi, dite_eq_left hj, d_eq K p i j hi hj,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact (isZero_X_of_lt K p i (by omega)).eq_of_src _ _

@[simp]
theorem inclusion_f (K : CochainComplex C ℕ) (p n : ℕ) (hn : p ≤ n) :
    (inclusion K p).f n = (xIso K p n hn).hom := by
  simp [inclusion, inclusionComponent, hn]

/-- The original-coordinate map from a later filtration term to an earlier one. -/
def transitionComponent (K : CochainComplex C ℕ) (p q : ℕ) (hpq : p ≤ q) (n : ℕ) :
    (complex K q).X n ⟶ (complex K p).X n :=
  if hqn : q ≤ n then (xIso K q n hqn).hom ≫ (xIso K p n (hpq.trans hqn)).inv else 0

/-- The actual decreasing transition between degree-filtered complexes. -/
def transition (K : CochainComplex C ℕ) (p q : ℕ) (hpq : p ≤ q) :
    complex K q ⟶ complex K p where
  f n := transitionComponent K p q hpq n
  comm' i j hij := by
    by_cases hi : q ≤ i
    · have hj : q ≤ j := by change i + 1 = j at hij; omega
      simp only [transitionComponent, dite_eq_left hi, dite_eq_left hj,
        d_eq K q i j hi hj, d_eq K p i j (hpq.trans hi) (hpq.trans hj),
        Category.assoc, Iso.inv_hom_id_assoc]
    · exact (isZero_X_of_lt K q i (by omega)).eq_of_src _ _

/-- The actual transitions preserve the original inclusions. -/
@[reassoc]
theorem transition_inclusion (K : CochainComplex C ℕ) (p q : ℕ) (hpq : p ≤ q) :
    transition K p q hpq ≫ inclusion K p = inclusion K q := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hqn : q ≤ n
  · simp [transition, transitionComponent, hqn, inclusion_f, hpq.trans hqn]
  · exact (isZero_X_of_lt K q n (by omega)).eq_of_src _ _

instance inclusion_zero_isIso (K : CochainComplex C ℕ) : IsIso (inclusion K 0) := by
  have (n : ℕ) : IsIso ((inclusion K 0).f n) := by
    rw [inclusion_f K 0 n (Nat.zero_le n)]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Filtration level zero is the original complex through its original inclusion. -/
def zeroIso (K : CochainComplex C ℕ) : complex K 0 ≅ K := asIso (inclusion K 0)

@[simp]
theorem zeroIso_hom (K : CochainComplex C ℕ) : (zeroIso K).hom = inclusion K 0 := rfl

/-- In a two-term complex, all terms of every filtered piece vanish in degrees at least two. -/
theorem isZero_X_of_twoTerm (K : CochainComplex C ℕ)
    (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n)) (p n : ℕ) (hn : 2 ≤ n) :
    IsZero ((complex K p).X n) := by
  by_cases hpn : p ≤ n
  · exact (hK n hn).of_iso (xIso K p n hpn)
  · exact isZero_X_of_lt K p n (by omega)

/-- Every actual degree-filtered piece starting in degree at least two is zero for a two-term complex. -/
theorem complex_isZero_of_twoTerm (K : CochainComplex C ℕ)
    (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n)) (p : ℕ) (hp : 2 ≤ p) :
    IsZero (complex K p) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hpn : p ≤ n
  · exact (isZero_X_of_twoTerm K hK p n (hp.trans hpn)).eq_of_src _ _
  · exact (isZero_X_of_lt K p n (by omega)).eq_of_src _ _

end HodgeConjecture.DegreeFiltration
