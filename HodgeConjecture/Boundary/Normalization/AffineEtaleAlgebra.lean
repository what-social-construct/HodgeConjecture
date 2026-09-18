import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Étale algebras on affine charts

The ring map on an affine source chart over an affine target chart of an
étale scheme morphism is an étale algebra map.  This connects scheme-level
étaleness to the algebra input used by the normalization construction.

The proof passes from locally standard smooth presentations to smooth ring
maps using target-locality, then combines smoothness with formal
unramifiedness.  No auxiliary geometric input is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory RingHom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Scheme smoothness gives algebraic smoothness on any pair of affine
charts for which the coordinate-ring map is defined. -/
theorem affine_appLE_smooth [IsSmooth f]
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (f.appLE U V e).hom.Smooth := by
  have hlocal : Locally IsStandardSmooth (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @IsSmooth) f inferInstance U V e
  have hsmooth : Locally RingHom.Smooth (f.appLE U V e).hom := by
    apply locally_of_locally _ hlocal
    intro R S _ _ g hg
    algebraize [g]
    haveI : Algebra.IsStandardSmooth R S := hg
    exact inferInstanceAs (Algebra.Smooth R S)
  rwa [locally_iff_of_localizationSpanTarget
    RingHom.Smooth.propertyIsLocal.respectsIso
    RingHom.Smooth.ofLocalizationSpanTarget] at hsmooth

/-- The canonical coordinate algebra of an affine source chart of an étale
morphism, over an affine target chart, is étale. -/
theorem affine_appLE_etale [IsEtale f]
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI := (f.appLE U V e).hom.toAlgebra
    Algebra.Etale Γ(Y, U) Γ(X, V) := by
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Y, U) Γ(X, V) := affine_appLE_smooth f U V e
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) :=
    AlgebraicGeometry.FormallyUnramified.formallyUnramified_of_affine_subset
      (f := f) U V e
  exact ⟨Algebra.FormallyEtale.of_unramified_and_smooth, inferInstance⟩

/-- An étale morphism between affine schemes induces an étale algebra map
on global sections. -/
theorem affine_appTop_etale [IsEtale f] [IsAffine X] [IsAffine Y] :
    letI := f.appTop.hom.toAlgebra
    Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact affine_appLE_etale f ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

end HodgeConjecture.CollisionFoundations
