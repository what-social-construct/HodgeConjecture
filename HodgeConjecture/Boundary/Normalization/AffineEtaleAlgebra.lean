module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Smooth

@[expose] public section

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
theorem affine_appLE_smooth [Smooth f]
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (f.appLE U V e).hom.Smooth := by
  exact HasRingHomProperty.appLE (P := @Smooth) f inferInstance U V e

/-- The canonical coordinate algebra of an affine source chart of an étale
morphism, over an affine target chart, is étale. -/
theorem affine_appLE_etale [Etale f]
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI := (f.appLE U V e).hom.toAlgebra
    Algebra.Etale Γ(Y, U) Γ(X, V) := by
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Y, U) Γ(X, V) := affine_appLE_smooth f U V e
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) :=
    f.formallyUnramified_appLE U.property V.property e
  exact ⟨Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth, inferInstance⟩

/-- An étale morphism between affine schemes induces an étale algebra map
on global sections. -/
theorem affine_appTop_etale [Etale f] [IsAffine X] [IsAffine Y] :
    letI := f.appTop.hom.toAlgebra
    Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact affine_appLE_etale f ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

end HodgeConjecture.CollisionFoundations
