module

public import HodgeConjecture.Realization.Betti.SingularSubdivisionHomology
public import HodgeConjecture.Realization.Betti.SingularSubdivisionLocality

@[expose] public section

/-!
# Subdivision and its homotopy on the actual small-chain complex

The original native simplicial subcomplex inclusion identifies its chains
with the supported range in the whole singular complex. The constructed
subdivision and homotopy preserve that range, so both restrict to actual
small chains. The restricted subdivision is homotopic to the identity and
intertwines with the original inclusion. No open-cover assumption is needed.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory SingularSubcomplexes SubcomplexChainCoordinates
open SingularSubdivisionSmallness

/-- The original native rational chain complex of the small singular subcomplex. -/
abbrev smallComplex (X : TopCat) (U V : Set X) :=
  (smallSingular X U V : SSet).chainComplex (ModuleCat.of ℚ ℚ)

/-- The original native inclusion, with the same literal rational coefficients. -/
abbrev smallInclusion (X : TopCat) (U V : Set X) : smallComplex X U V ⟶ complex X :=
  inclusion (smallSingular X U V)

/-- Restrict an actual supported operator through the proved original inclusion range. -/
def restrictSmallOperator (X : TopCat) (U V : Set X) (i j : ℕ)
    (f : (complex X).X i →ₗ[ℚ] (complex X).X j)
    (hf : ∀ c, c ∈ smallChains X U V i → f c ∈ smallChains X U V j) :
    (smallComplex X U V).X i →ₗ[ℚ] (smallComplex X U V).X j :=
  restrictOperator (smallSingular X U V) (smallSingular X U V) i j f hf

theorem inclusion_restrictSmallOperator (X : TopCat) (U V : Set X) (i j : ℕ)
    (f : (complex X).X i →ₗ[ℚ] (complex X).X j)
    (hf : ∀ c, c ∈ smallChains X U V i → f c ∈ smallChains X U V j)
    (c : (smallComplex X U V).X i) :
    (smallInclusion X U V).f j (restrictSmallOperator X U V i j f hf c) =
      f ((smallInclusion X U V).f i c) :=
  inclusion_restrictOperator (smallSingular X U V) (smallSingular X U V) i j f hf c

theorem smallInclusion_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (smallComplex X U V).X (n + 1)) :
    (smallInclusion X U V).f n ((smallComplex X U V).d (n + 1) n c) =
      (complex X).d (n + 1) n ((smallInclusion X U V).f (n + 1) c) :=
  inclusion_d (smallSingular X U V) (n + 1) n c

def smallSubdivisionComponent (X : TopCat) (U V : Set X) (n : ℕ) :
    (smallComplex X U V).X n →ₗ[ℚ] (smallComplex X U V).X n :=
  restrictSmallOperator X U V n n (subdivisionComponent X n)
    (subdivisionComponent_mem_smallChains X U V n)

theorem inclusion_smallSubdivisionComponent (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (smallComplex X U V).X n) :
    (smallInclusion X U V).f n (smallSubdivisionComponent X U V n c) =
      subdivisionComponent X n ((smallInclusion X U V).f n c) :=
  inclusion_restrictSmallOperator X U V n n _ _ c

/-- The actual subdivision restricted to the original small-chain complex. -/
def smallSubdivision (X : TopCat) (U V : Set X) : smallComplex X U V ⟶ smallComplex X U V :=
  restrictMap (smallSingular X U V) (smallSingular X U V) (subdivision X)
    (fun n c hc ↦ subdivisionComponent_mem_smallChains X U V n c hc)

theorem smallSubdivision_inclusion (X : TopCat) (U V : Set X) :
    smallSubdivision X U V ≫ smallInclusion X U V = smallInclusion X U V ≫ subdivision X :=
  restrictMap_inclusion _ _ _ _

def smallHomotopyComponent (X : TopCat) (U V : Set X) (n : ℕ) :
    (smallComplex X U V).X n →ₗ[ℚ] (smallComplex X U V).X (n + 1) :=
  restrictSmallOperator X U V n (n + 1) (homotopyComponent X n)
    (homotopyComponent_mem_small X U V n)

theorem inclusion_smallHomotopyComponent (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (smallComplex X U V).X n) :
    (smallInclusion X U V).f (n + 1) (smallHomotopyComponent X U V n c) =
      homotopyComponent X n ((smallInclusion X U V).f n c) :=
  inclusion_restrictSmallOperator X U V n (n + 1) _ _ c

theorem smallHomotopyComponent_identity_zero (X : TopCat) (U V : Set X)
    (c : (smallComplex X U V).X 0) :
    (smallComplex X U V).d 1 0 (smallHomotopyComponent X U V 0 c) =
      c - smallSubdivisionComponent X U V 0 c := by
  apply inclusion_injective (smallSingular X U V) 0
  rw [map_sub, smallInclusion_boundary, inclusion_smallHomotopyComponent,
    inclusion_smallSubdivisionComponent, homotopyComponent_identity_zero]

theorem smallHomotopyComponent_identity (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (smallComplex X U V).X (n + 1)) :
    (smallComplex X U V).d (n + 2) (n + 1) (smallHomotopyComponent X U V (n + 1) c) +
      smallHomotopyComponent X U V n ((smallComplex X U V).d (n + 1) n c) =
        c - smallSubdivisionComponent X U V (n + 1) c := by
  apply inclusion_injective (smallSingular X U V) (n + 1)
  rw [map_add, map_sub, smallInclusion_boundary, inclusion_smallHomotopyComponent,
    inclusion_smallHomotopyComponent, smallInclusion_boundary,
    inclusion_smallSubdivisionComponent, homotopyComponent_identity]

def smallHomotopyDegree (X : TopCat) (U V : Set X) (i j : ℕ) :
    (smallComplex X U V).X i ⟶ (smallComplex X U V).X j :=
  if h : i + 1 = j then
    ModuleCat.ofHom (smallHomotopyComponent X U V i) ≫
      eqToHom (congrArg (smallComplex X U V).X h)
  else 0

@[simp]
theorem smallHomotopyDegree_succ (X : TopCat) (U V : Set X) (i : ℕ) :
    smallHomotopyDegree X U V i (i + 1) = ModuleCat.ofHom (smallHomotopyComponent X U V i) := by
  simp [smallHomotopyDegree]

/-- The original explicit singular homotopy restricts to a native small-chain homotopy. -/
def smallSubdivisionHomotopy (X : TopCat) (U V : Set X) :
    Homotopy (𝟙 (smallComplex X U V)) (smallSubdivision X U V) := by
  have h := restrictHomotopy (smallSingular X U V) (smallSingular X U V)
    (f := 𝟙 (complex X)) (g := subdivision X)
    (fun _ _ hc ↦ hc) (fun n c hc ↦ subdivisionComponent_mem_smallChains X U V n c hc)
    (subdivisionHomotopy X) (fun i j c hc ↦ by
      change homotopyDegree X i j c ∈ smallChains X U V j
      by_cases hij : i + 1 = j
      · subst j
        rw [homotopyDegree_succ]
        exact homotopyComponent_mem_small X U V i c hc
      · rw [homotopyDegree, dite_eq_right hij]
        exact (smallChains X U V j).zero_mem)
  rw [restrictMap_id] at h
  exact h

theorem homologyMap_smallSubdivision (X : TopCat) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivision X U V) n =
      𝟙 ((smallComplex X U V).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    ((smallSubdivisionHomotopy X U V).homologyMap_eq n).symm

def smallSubdivisionPower (X : TopCat) (U V : Set X) (k : ℕ) :
    smallComplex X U V ⟶ smallComplex X U V :=
  ((End.of (smallSubdivision X U V)) ^ k).asHom

@[simp]
theorem smallSubdivisionPower_zero (X : TopCat) (U V : Set X) :
    smallSubdivisionPower X U V 0 = 𝟙 (smallComplex X U V) := rfl

@[simp]
theorem smallSubdivisionPower_succ (X : TopCat) (U V : Set X) (k : ℕ) :
    smallSubdivisionPower X U V (k + 1) = smallSubdivision X U V ≫ smallSubdivisionPower X U V k := by
  simp only [smallSubdivisionPower, pow_succ, End.mul_asHom]

theorem smallSubdivisionPower_inclusion (X : TopCat) (U V : Set X) (k : ℕ) :
    smallSubdivisionPower X U V k ≫ smallInclusion X U V =
      smallInclusion X U V ≫ subdivisionPower X k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [smallSubdivisionPower_succ, Category.assoc, ih, ← Category.assoc,
      smallSubdivision_inclusion, Category.assoc, ← subdivisionPower_succ]

theorem homologyMap_smallSubdivision_pow (X : TopCat) (U V : Set X) (k n : ℕ) :
    HomologicalComplex.homologyMap (smallSubdivisionPower X U V k) n =
      𝟙 ((smallComplex X U V).homology n) := by
  induction k with
  | zero => rw [smallSubdivisionPower_zero, HomologicalComplex.homologyMap_id]
  | succ k ih =>
    rw [smallSubdivisionPower_succ, HomologicalComplex.homologyMap_comp,
      homologyMap_smallSubdivision, ih, Category.id_comp]

end HodgeConjecture.SingularSubdivision
