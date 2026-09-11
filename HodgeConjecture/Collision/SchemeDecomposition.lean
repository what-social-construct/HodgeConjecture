import HodgeConjecture.Collision.DecompositionDefect
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# From ideal decompositions to affine scheme decompositions

For an ideal `J` in a commutative ring `C`, the diagonal and residual pieces
are cut out by `J` and `J.annihilator`.  If the overlap defect vanishes and
the contact ideal is the unit ideal, the Chinese remainder theorem gives

`C ≃+* (C ⧸ J) × (C ⧸ J.annihilator)`.

On prime spectra this becomes a homeomorphism from `Spec C` to the disjoint
union of the two closed pieces.  This is the affine algebraic form of the
middle implication

`ideal decomposition ⟹ affine-scheme decomposition`.

This module does not turn the resulting components into correspondence
projectors.  That further step requires an ambient proper correspondence,
cycle extraction, and a proof that the extracted classes are idempotent for
correspondence composition rather than merely for coordinate-ring
multiplication.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [CommRing C]

/--
The canonical product decomposition attached to complementary ideal and
annihilator defects.
-/
noncomputable def idealProductDecomposition
    (J : Ideal C)
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤) :
    C ≃+* (C ⧸ J) × (C ⧸ J.annihilator) := by
  have hInf : (⊥ : Ideal C) = J ⊓ J.annihilator := by
    simpa [overlapDefectIdeal] using hOverlap.symm
  have hCoprime : IsCoprime J J.annihilator := by
    rw [Ideal.isCoprime_iff_sup_eq]
    simpa [contactIdeal] using hContact
  exact
    (RingEquiv.quotientBot C).symm |>.trans
      ((Ideal.quotEquivOfEq hInf).trans
        (Ideal.quotientInfEquivQuotientProd J J.annihilator hCoprime))

/--
The first projection of the product decomposition is the quotient map by
`J`.
-/
@[simp]
theorem idealProductDecomposition_fst
    (J : Ideal C)
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤)
    (x : C) :
    (idealProductDecomposition J hOverlap hContact x).1 =
      Ideal.Quotient.mk J x := by
  rfl

/--
The second projection of the product decomposition is the quotient map by
the residual annihilator.
-/
@[simp]
theorem idealProductDecomposition_snd
    (J : Ideal C)
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤)
    (x : C) :
    (idealProductDecomposition J hOverlap hContact x).2 =
      Ideal.Quotient.mk J.annihilator x := by
  rfl

/--
The affine spectrum decomposes topologically as the disjoint union of the
diagonal and residual spectra.
-/
noncomputable def idealSpectrumDecomposition
    (J : Ideal C)
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤) :
    PrimeSpectrum C ≃ₜ
      PrimeSpectrum (C ⧸ J) ⊕ PrimeSpectrum (C ⧸ J.annihilator) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    (idealProductDecomposition J hOverlap hContact)).trans
      PrimeSpectrum.primeSpectrumProdHomeo

/--
The corresponding affine-scheme isomorphism.  Thus the product-ring
decomposition is not only a decomposition of underlying prime spectra: it is
the scheme-theoretic disjoint union of the two quotient schemes.
-/
noncomputable def idealAffineSchemeDecomposition
    (J : Ideal C)
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤) :
    AlgebraicGeometry.Spec (.of C) ≅
      (AlgebraicGeometry.Spec (.of (C ⧸ J)) ⨿
        AlgebraicGeometry.Spec (.of (C ⧸ J.annihilator))) :=
  (AlgebraicGeometry.Scheme.Spec.mapIso
      (idealProductDecomposition J hOverlap hContact).toCommRingCatIso.op).symm ≪≫
    (asIso
      (AlgebraicGeometry.coprodSpec
        (C ⧸ J) (C ⧸ J.annihilator))).symm

/-- Collision-specific product decomposition. -/
noncomputable def collisionProductDecomposition
    (B : Type u) (A : Type u)
    [CommRing B] [CommRing A] [Algebra B A]
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    CollisionAlgebra B A ≃+*
      ((CollisionAlgebra B A ⧸ collisionObstructionIdeal B A) ×
        (CollisionAlgebra B A ⧸ collisionOffDiagonalIdeal B A)) :=
  idealProductDecomposition
    (collisionObstructionIdeal B A) hOverlap hContact

/--
Collision-specific spectrum decomposition into the diagonal quotient and
the residual off-diagonal quotient.
-/
noncomputable def collisionSpectrumDecomposition
    (B : Type u) (A : Type u)
    [CommRing B] [CommRing A] [Algebra B A]
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    PrimeSpectrum (CollisionAlgebra B A) ≃ₜ
      PrimeSpectrum
          (CollisionAlgebra B A ⧸ collisionObstructionIdeal B A) ⊕
        PrimeSpectrum
          (CollisionAlgebra B A ⧸ collisionOffDiagonalIdeal B A) :=
  idealSpectrumDecomposition
    (collisionObstructionIdeal B A) hOverlap hContact

/--
Collision-specific affine-scheme decomposition into the diagonal and
off-diagonal quotient schemes.
-/
noncomputable def collisionAffineSchemeDecomposition
    (B : Type u) (A : Type u)
    [CommRing B] [CommRing A] [Algebra B A]
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    AlgebraicGeometry.Spec (.of (CollisionAlgebra B A)) ≅
      (AlgebraicGeometry.Spec
          (.of
            (CollisionAlgebra B A ⧸ collisionObstructionIdeal B A)) ⨿
        AlgebraicGeometry.Spec
          (.of
            (CollisionAlgebra B A ⧸ collisionOffDiagonalIdeal B A))) :=
  idealAffineSchemeDecomposition
    (collisionObstructionIdeal B A) hOverlap hContact

end

end HodgeConjecture
