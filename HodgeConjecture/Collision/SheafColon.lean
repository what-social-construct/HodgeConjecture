import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.Colon

/-!
# Sheaf-colon ideals

For ideal sheaves `I` and `J` on a scheme `X`, the componentwise family

`U ↦ I(U) : J(U)`

need not be inserted into `IdealSheafData` without checking localization
compatibility.  We therefore define the sheaf-colon as the largest
quasi-coherent ideal-sheaf datum contained in that family.  On an affine
scheme its ideal of global sections is exactly the ordinary ring-theoretic
colon.

This supplies the intrinsic residual operation needed for the global
off-diagonal collision scheme.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace CollisionIdealSheaf

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/--
Extension of ideals along a ring homomorphism sends a colon ideal into the
colon of the extended ideals.
-/
theorem map_colon_le
    (f : R →+* S) (I J : Ideal R) :
    (I.colon J).map f ≤ (I.map f).colon (J.map f) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f x ∈ (I.map f).colon (J.map f)
  rw [Submodule.mem_colon]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      change f x * f j ∈ I.map f
      rw [← map_mul]
      exact
        Ideal.mem_map_of_mem f
          (by
            simpa [smul_eq_mul] using
              Submodule.mem_colon.mp hx j hj)
  | zero =>
      simp
  | add y z _ _ hy hz =>
      simpa [smul_eq_mul, mul_add] using
        Ideal.add_mem (I.map f) hy hz
  | smul c y _ hy =>
      simpa [smul_eq_mul, mul_assoc, mul_left_comm] using
        Ideal.mul_mem_left (I := I.map f) c hy

end Ring

section Scheme

variable {X : Scheme.{u}}

/--
The sheaf-colon `I : J`: the largest quasi-coherent ideal-sheaf datum whose
section ideal on every affine open is contained in the ordinary colon
`I(U) : J(U)`.
-/
def colon
    (I J : X.IdealSheafData) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U =>
    (I.ideal U).colon (J.ideal U)

/-- Every affine-open component of the sheaf-colon lies in the ring colon. -/
theorem colon_ideal_le
    (I J : X.IdealSheafData)
    (U : X.affineOpens) :
    (colon I J).ideal U ≤
      (I.ideal U).colon (J.ideal U) :=
  Scheme.IdealSheafData.ideal_ofIdeals_le _ U

/--
On an affine scheme, the global sections of the sheaf-colon are exactly the
ordinary colon of the global-section ideals.
-/
theorem colon_ideal_top
    [IsAffine X]
    (I J : X.IdealSheafData) :
    (colon I J).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩).colon
        (J.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩) := by
  apply le_antisymm
  · exact colon_ideal_le I J _
  · let K : X.IdealSheafData :=
      Scheme.IdealSheafData.ofIdealTop
        ((I.ideal
            ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩).colon
          (J.ideal
            ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩))
    have hK : K ≤ colon I J := by
      apply
        (Scheme.IdealSheafData.le_ofIdeals_iff
          (I := K)
          (J := fun U => (I.ideal U).colon (J.ideal U))).mpr
      intro U
      dsimp only [K]
      rw [Scheme.IdealSheafData.ofIdealTop_ideal]
      let r :=
        (X.presheaf.map
          (homOfLE
            (le_top : U.1 ≤ (⊤ : X.Opens))).op).hom
      have hI :
          (I.ideal
              ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩).map r =
            I.ideal U := by
        dsimp only [r]
        exact
          I.map_ideal
            (U := U)
            (V := ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩)
            (le_top : U.1 ≤ (⊤ : X.Opens))
      have hJ :
          (J.ideal
              ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩).map r =
            J.ideal U := by
        dsimp only [r]
        exact
          J.map_ideal
            (U := U)
            (V := ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩)
            (le_top : U.1 ≤ (⊤ : X.Opens))
      have hColon :=
        map_colon_le r
          (I.ideal
            ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩)
          (J.ideal
            ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩)
      rw [hI, hJ] at hColon
      simpa only [r] using hColon
    simpa [K] using
      hK ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩

/-- The intrinsic annihilator of an ideal sheaf. -/
def annihilator
    (J : X.IdealSheafData) :
    X.IdealSheafData :=
  colon (⊥ : X.IdealSheafData) J

/--
On an affine scheme, the intrinsic sheaf annihilator has the expected ideal
of global sections.
-/
theorem annihilator_ideal_top
    [IsAffine X]
    (J : X.IdealSheafData) :
    (annihilator J).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩ =
      (J.ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩).annihilator := by
  rw [annihilator, colon_ideal_top]
  exact Submodule.colon_bot

end Scheme

end CollisionIdealSheaf

end

end HodgeConjecture
