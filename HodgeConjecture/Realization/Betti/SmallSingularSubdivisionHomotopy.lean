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
  (chainSubmoduleEquiv (smallSingular X U V) j).symm.toLinearMap.comp
    ((f.comp ((smallInclusion X U V).f i).hom).codRestrict
      (chainSubmodule (smallSingular X U V) j) (fun c ↦ by
        rw [← smallChains_eq_chainSubmodule]
        apply hf
        rw [smallChains_eq_chainSubmodule, ← chainSubmoduleEquiv_coe]
        exact (chainSubmoduleEquiv (smallSingular X U V) i c).property))

theorem inclusion_restrictSmallOperator (X : TopCat) (U V : Set X) (i j : ℕ)
    (f : (complex X).X i →ₗ[ℚ] (complex X).X j)
    (hf : ∀ c, c ∈ smallChains X U V i → f c ∈ smallChains X U V j)
    (c : (smallComplex X U V).X i) :
    (smallInclusion X U V).f j (restrictSmallOperator X U V i j f hf c) =
      f ((smallInclusion X U V).f i c) := by
  rw [← chainSubmoduleEquiv_coe]
  change ((chainSubmoduleEquiv (smallSingular X U V) j)
    ((chainSubmoduleEquiv (smallSingular X U V) j).symm _) : (complex X).X j) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem smallInclusion_boundary (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (smallComplex X U V).X (n + 1)) :
    (smallInclusion X U V).f n ((smallComplex X U V).d (n + 1) n c) =
      (complex X).d (n + 1) n ((smallInclusion X U V).f (n + 1) c) :=
  (congrArg (fun f : (smallComplex X U V).X (n + 1) ⟶ (complex X).X n ↦ f c)
    ((smallInclusion X U V).comm (n + 1) n)).symm

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
def smallSubdivision (X : TopCat) (U V : Set X) : smallComplex X U V ⟶ smallComplex X U V where
  f n := ModuleCat.ofHom (smallSubdivisionComponent X U V n)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply inclusion_injective (smallSingular X U V) j
    change (smallInclusion X U V).f j
        ((smallComplex X U V).d (j + 1) j (smallSubdivisionComponent X U V (j + 1) c)) =
      (smallInclusion X U V).f j
        (smallSubdivisionComponent X U V j ((smallComplex X U V).d (j + 1) j c))
    rw [smallInclusion_boundary, inclusion_smallSubdivisionComponent,
      inclusion_smallSubdivisionComponent, smallInclusion_boundary, subdivisionComponent_boundary]

theorem smallSubdivision_inclusion (X : TopCat) (U V : Set X) :
    smallSubdivision X U V ≫ smallInclusion X U V = smallInclusion X U V ≫ subdivision X := by
  ext n c
  exact inclusion_smallSubdivisionComponent X U V n c

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
    Homotopy (𝟙 (smallComplex X U V)) (smallSubdivision X U V) where
  hom := smallHomotopyDegree X U V
  zero i j hij := by
    have h : ¬ i + 1 = j := hij
    simp [smallHomotopyDegree, h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        smallHomotopyDegree_succ, zero_add]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change c = (smallComplex X U V).d 1 0 (smallHomotopyComponent X U V 0 c) +
        smallSubdivisionComponent X U V 0 c
      rw [smallHomotopyComponent_identity_zero]
      abel
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        smallHomotopyDegree_succ, smallHomotopyDegree_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change c = smallHomotopyComponent X U V n ((smallComplex X U V).d (n + 1) n c) +
        (smallComplex X U V).d (n + 2) (n + 1) (smallHomotopyComponent X U V (n + 1) c) +
          smallSubdivisionComponent X U V (n + 1) c
      calc
        c = (smallComplex X U V).d (n + 2) (n + 1) (smallHomotopyComponent X U V (n + 1) c) +
            smallHomotopyComponent X U V n ((smallComplex X U V).d (n + 1) n c) +
              smallSubdivisionComponent X U V (n + 1) c := by
          rw [smallHomotopyComponent_identity]
          abel
        _ = _ := by abel

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
