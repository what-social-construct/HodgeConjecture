module

public import HodgeConjecture.Realization.Betti.SingularSubdivisionHomotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

/-!
# The actual singular subdivision acts identically on homology

The explicit realized homotopy is bundled as Mathlib's native chain
homotopy from the identity to the constructed subdivision map. Hence the
original rational singular-homology map of subdivision, and every finite
composition power of it, is the identity in every degree.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory

/-- Put the constructed homotopy component in degree `i → i+1`, and zero elsewhere. -/
def homotopyDegree (X : TopCat) (i j : ℕ) : (complex X).X i ⟶ (complex X).X j :=
  if h : i + 1 = j then
    ModuleCat.ofHom (homotopyComponent X i) ≫ eqToHom (congrArg (complex X).X h)
  else 0

@[simp]
theorem homotopyDegree_succ (X : TopCat) (i : ℕ) :
    homotopyDegree X i (i + 1) = ModuleCat.ofHom (homotopyComponent X i) := by
  simp [homotopyDegree]

/-- The native chain homotopy, with both the positive-degree and degree-zero
identities supplied by the original explicit singular-chain construction. -/
def subdivisionHomotopy (X : TopCat) : Homotopy (𝟙 (complex X)) (subdivision X) where
  hom := homotopyDegree X
  zero i j hij := by
    have h : ¬ i + 1 = j := hij
    simp [homotopyDegree, h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        homotopyDegree_succ, zero_add]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change c = (complex X).d 1 0 (homotopyComponent X 0 c) + subdivisionComponent X 0 c
      rw [homotopyComponent_identity_zero]
      abel
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        homotopyDegree_succ, homotopyDegree_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change c = homotopyComponent X n ((complex X).d (n + 1) n c) +
        (complex X).d (n + 2) (n + 1) (homotopyComponent X (n + 1) c) +
          subdivisionComponent X (n + 1) c
      calc
        c = (complex X).d (n + 2) (n + 1) (homotopyComponent X (n + 1) c) +
            homotopyComponent X n ((complex X).d (n + 1) n c) +
              subdivisionComponent X (n + 1) c := by
          rw [homotopyComponent_identity]
          abel
        _ = _ := by abel

/-- The constructed subdivision induces the identity on actual rational singular homology. -/
theorem homologyMap_subdivision (X : TopCat) (n : ℕ) :
    HomologicalComplex.homologyMap (subdivision X) n = 𝟙 ((complex X).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    ((subdivisionHomotopy X).homologyMap_eq n).symm

/-- A finite composition power of the actual singular chain map. -/
def subdivisionPower (X : TopCat) (k : ℕ) : complex X ⟶ complex X :=
  ((End.of (subdivision X)) ^ k).asHom

@[simp]
theorem subdivisionPower_zero (X : TopCat) : subdivisionPower X 0 = 𝟙 (complex X) := rfl

@[simp]
theorem subdivisionPower_succ (X : TopCat) (k : ℕ) :
    subdivisionPower X (k + 1) = subdivision X ≫ subdivisionPower X k := by
  simp only [subdivisionPower, pow_succ, End.mul_asHom]

/-- Every actual finite composition power of subdivision still induces the identity. -/
theorem homologyMap_subdivision_pow (X : TopCat) (k n : ℕ) :
    HomologicalComplex.homologyMap (subdivisionPower X k) n =
      𝟙 ((complex X).homology n) := by
  induction k with
  | zero => rw [subdivisionPower_zero, HomologicalComplex.homologyMap_id]
  | succ k ih =>
    rw [subdivisionPower_succ, HomologicalComplex.homologyMap_comp,
      homologyMap_subdivision, ih, Category.id_comp]

/-- The chain-map power has the same degree components as ordinary iteration of the
explicit constructed linear operator on the original singular chain module. -/
theorem subdivisionPower_apply (X : TopCat) (k n : ℕ) (c : (complex X).X n) :
    (subdivisionPower X k).f n c =
      ((subdivisionComponent X n : (complex X).X n → (complex X).X n)^[k]) c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [subdivisionPower_succ, HomologicalComplex.comp_f]
    change (subdivisionPower X k).f n (subdivisionComponent X n c) = _
    rw [ih, Function.iterate_succ_apply]

end HodgeConjecture.SingularSubdivision
