module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
public import HodgeConjecture.Realization.Betti.SingularHomotopy
public import HodgeConjecture.Topology.OnePointHomotopy
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Actual affine maps of the projective-line point space

The homeomorphism sends the original scheme point with finite coordinate
`z` to the original point with coordinate `a + u * z`, and fixes infinity.
It is conjugated through the native one-point compactification. An actual
continuous homotopy from the identity proves that its original singular
cohomology pullback is the identity in every degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 20000

noncomputable section

namespace HodgeConjecture.ProjectiveLineAffine

open CategoryTheory ProjectiveLineComplexPoints unitInterval

abbrev space : TopCat := TopCat.of Point

/-- The ordinary complex affine homeomorphism, with nonzero linear coefficient. -/
def complexAffineHomeomorph (a : ℂ) (u : ℂˣ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (u : ℂ) u.ne_zero).trans (Homeomorph.addLeft a)

@[simp]
theorem complexAffineHomeomorph_apply (a : ℂ) (u : ℂˣ) (z : ℂ) :
    complexAffineHomeomorph a u z = a + (u : ℂ) * z := rfl

/-- The actual affine homeomorphism of the original complex scheme-point space. -/
def affineHomeomorph (a : ℂ) (u : ℂˣ) : Point ≃ₜ Point :=
  onePointHomeomorph.trans
    ((complexAffineHomeomorph a u).onePointCongr.trans onePointHomeomorph.symm)

@[simp]
theorem affineHomeomorph_finite (a : ℂ) (u : ℂˣ) (z : ℂ) :
    affineHomeomorph a u (finite z) = finite (a + (u : ℂ) * z) := by
  simp [affineHomeomorph, Homeomorph.onePointCongr]

@[simp]
theorem affineHomeomorph_infinity (a : ℂ) (u : ℂˣ) :
    affineHomeomorph a u infinity = infinity := by
  simp [affineHomeomorph, Homeomorph.onePointCongr]

/-- The continuous map underlying the actual affine homeomorphism. -/
def affineContinuousMap (a : ℂ) (u : ℂˣ) : C(Point, Point) :=
  ⟨affineHomeomorph a u, (affineHomeomorph a u).continuous⟩

/-- The native topological morphism of the actual affine homeomorphism. -/
def affineMap (a : ℂ) (u : ℂˣ) : space ⟶ space :=
  TopCat.ofHom (affineContinuousMap a u)

@[simp]
theorem affineMap_finite (a : ℂ) (u : ℂˣ) (z : ℂ) :
    affineMap a u (finite z) = finite (a + (u : ℂ) * z) :=
  affineHomeomorph_finite a u z

@[simp]
theorem affineMap_infinity (a : ℂ) (u : ℂˣ) : affineMap a u infinity = infinity :=
  affineHomeomorph_infinity a u

/-- A nonvanishing complex-linear coefficient joining one to the given unit. -/
def coefficient (u : ℂˣ) (t : I) : ℂ :=
  Complex.exp ((t : ℝ) * Complex.log (u : ℂ))

theorem coefficient_ne_zero (u : ℂˣ) (t : I) : coefficient u t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem coefficient_zero (u : ℂˣ) : coefficient u 0 = 1 := by simp [coefficient]

@[simp]
theorem coefficient_one (u : ℂˣ) : coefficient u 1 = (u : ℂ) := by
  simp [coefficient, Complex.exp_log u.ne_zero]

def affineFamily (a : ℂ) (u : ℂˣ) (q : I × ℂ) : ℂ :=
  (q.1 : ℝ) * a + coefficient u q.1 * q.2

def inverseFamily (a : ℂ) (u : ℂˣ) (q : I × ℂ) : ℂ :=
  (q.2 - (q.1 : ℝ) * a) / coefficient u q.1

theorem continuous_affineFamily (a : ℂ) (u : ℂˣ) : Continuous (affineFamily a u) := by
  unfold affineFamily coefficient
  fun_prop

theorem continuous_inverseFamily (a : ℂ) (u : ℂˣ) : Continuous (inverseFamily a u) := by
  apply Continuous.div
  · fun_prop
  · unfold coefficient
    fun_prop
  · intro q
    exact coefficient_ne_zero u q.1

theorem inverseFamily_affineFamily (a : ℂ) (u : ℂˣ) (t : I) (z : ℂ) :
    inverseFamily a u (t, affineFamily a u (t, z)) = z := by
  change ((t : ℝ) * a + coefficient u t * z - (t : ℝ) * a) / coefficient u t = z
  rw [add_sub_cancel_left, mul_div_cancel_left₀ z (coefficient_ne_zero u t)]

/-- The literal affine family extended to the point at infinity. -/
def affineHomotopyFun (a : ℂ) (u : ℂˣ) (q : I × Point) : Point :=
  onePointHomeomorph.symm
    (OnePointHomotopy.mapFamily (affineFamily a u) (q.1, onePointHomeomorph q.2))

@[simp]
theorem affineHomotopyFun_finite (a : ℂ) (u : ℂˣ) (t : I) (z : ℂ) :
    affineHomotopyFun a u (t, finite z) =
      finite ((t : ℝ) * a + coefficient u t * z) := by
  simp [affineHomotopyFun, OnePointHomotopy.mapFamily_coe, affineFamily]

@[simp]
theorem affineHomotopyFun_infinity (a : ℂ) (u : ℂˣ) (t : I) :
    affineHomotopyFun a u (t, infinity) = infinity := by
  simp [affineHomotopyFun, OnePointHomotopy.mapFamily_infty]

/-- An actual homotopy through affine homeomorphisms, including at infinity. -/
def affineHomotopy (a : ℂ) (u : ℂˣ) :
    (ContinuousMap.id Point).Homotopy (affineContinuousMap a u) where
  toFun := affineHomotopyFun a u
  continuous_toFun := by
    apply onePointHomeomorph.symm.continuous.comp
    apply (OnePointHomotopy.continuous_map_family_of_leftInverse
      (affineFamily a u) (inverseFamily a u)
      (continuous_affineFamily a u) (continuous_inverseFamily a u)
      (inverseFamily_affineFamily a u)).comp
    exact continuous_fst.prodMk (onePointHomeomorph.continuous.comp continuous_snd)
  map_zero_left p := by
    rcases finite_or_infinity p with ⟨z, rfl⟩ | rfl <;> simp
  map_one_left p := by
    rcases finite_or_infinity p with ⟨z, rfl⟩ | rfl <;> simp [affineContinuousMap]

/-- Actual affine pullback on original singular cohomology is the identity in every degree. -/
theorem cohomologyPullback_affine (a : ℂ) (u : ℂˣ) (n : ℕ) :
    SingularCochains.cohomologyPullback (affineMap a u) n =
      𝟙 (SingularCochains.Cohomology space n) := by
  have h := SingularHomotopy.cohomologyPullback_eq_of_homotopic
    (f := ContinuousMap.id Point) (g := affineContinuousMap a u) ⟨affineHomotopy a u⟩ n
  change SingularCochains.cohomologyPullback (𝟙 space) n =
    SingularCochains.cohomologyPullback (affineMap a u) n at h
  rw [SingularCochains.cohomologyPullback_id] at h
  exact h.symm

theorem cohomologyPullback_affine_apply (a : ℂ) (u : ℂˣ) (n : ℕ)
    (z : SingularCochains.Cohomology space n) :
    SingularCochains.cohomologyPullback (affineMap a u) n z = z := by
  rw [cohomologyPullback_affine]
  rfl

end HodgeConjecture.ProjectiveLineAffine
