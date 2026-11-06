module

public import HodgeConjecture.Boundary.GaloisProjectorExtension
public import HodgeConjecture.Correspondence.ProjectorDefect

@[expose] public section

/-!
# Closure classes and their idempotence defect

A generic correspondence projector may have classes on a chosen
compactification before any argument shows that those classes remain
idempotent for compactified convolution.  This module records that weaker
stage without building idempotence into the data.

For a closure class `Π`, its convolution defect is `Π * Π - Π`.  Because
restriction is an algebra map and the generic projector is idempotent, the
defect restricts to zero.  No conclusion about boundary support or vanishing
of the defect in the compactified algebra is made here.

The zero-defect closure witnesses form a subtype.  Restricting to that
subtype recovers the existing `AlgebraProjectorExtension` interface.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w

/--
Raw closure data for one generic rational correspondence projector.

Unlike `AlgebraProjectorExtension`, a closure class is not assumed to be
idempotent in the compactified algebra.  The only compatibility required is
that it restricts to the prescribed generic projector.
-/
structure AlgebraProjectorClosure
    (genericAlgebra : Type u)
    (compactifiedAlgebra : Type v)
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
    (genericProjector : genericAlgebra) where
  genericProjector_isIdempotent :
    IsIdempotentElem genericProjector
  restriction :
    compactifiedAlgebra →ₐ[ℚ] genericAlgebra
  Closure : Type w
  closureClass : Closure → compactifiedAlgebra
  closureClass_restricts :
    ∀ x, restriction (closureClass x) = genericProjector

namespace AlgebraProjectorClosure

variable
  {genericAlgebra : Type u}
  {compactifiedAlgebra : Type v}
  [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
  [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
  {genericProjector : genericAlgebra}

/-- The failure of a raw closure class to be convolution-idempotent. -/
def convolutionDefect
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector)
    (x : C.Closure) : compactifiedAlgebra :=
  projectorIdempotenceDefect (C.closureClass x)

/-- Restriction to the generic algebra kills every closure defect. -/
@[simp]
theorem restriction_convolutionDefect
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector)
    (x : C.Closure) :
    C.restriction (C.convolutionDefect x) = 0 := by
  change
    C.restriction
        (projectorIdempotenceDefect (C.closureClass x)) = 0
  calc
    C.restriction
          (projectorIdempotenceDefect (C.closureClass x)) =
        projectorIdempotenceDefect
          (C.restriction (C.closureClass x)) := by
      exact
        map_projectorIdempotenceDefect
          C.restriction.toRingHom (C.closureClass x)
    _ = projectorIdempotenceDefect genericProjector := by
      rw [C.closureClass_restricts]
    _ = 0 :=
      projectorIdempotenceDefect_eq_zero
        C.genericProjector_isIdempotent

/-- Vanishing of the convolution defect is exactly idempotence of the class. -/
theorem convolutionDefect_eq_zero_iff
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector)
    (x : C.Closure) :
    C.convolutionDefect x = 0 ↔
      IsIdempotentElem (C.closureClass x) := by
  exact
    projectorIdempotenceDefect_eq_zero_iff
      (C.closureClass x)

/-- Raw closure witnesses whose compactified convolution defect vanishes. -/
def ZeroDefectWitness
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector) :=
  {x : C.Closure // C.convolutionDefect x = 0}

/-- A zero-defect witness supplies an idempotent compactified class. -/
theorem ZeroDefectWitness.closureClass_isIdempotent
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector)
    (x : C.ZeroDefectWitness) :
    IsIdempotentElem (C.closureClass x.1) :=
  (C.convolutionDefect_eq_zero_iff x.1).mp x.2

/--
Discarding raw closures with nonzero defect turns closure data into the
existing algebraic projector-extension package.
-/
def toAlgebraProjectorExtension
    (C :
      AlgebraProjectorClosure
        genericAlgebra compactifiedAlgebra genericProjector) :
    AlgebraProjectorExtension
      genericAlgebra compactifiedAlgebra genericProjector where
  genericProjector_isIdempotent :=
    C.genericProjector_isIdempotent
  restriction := C.restriction
  Extension := C.ZeroDefectWitness
  projector := fun x ↦ C.closureClass x.1
  projector_isIdempotent := fun x ↦
    x.closureClass_isIdempotent C
  projector_restricts := fun x ↦
    C.closureClass_restricts x.1

end AlgebraProjectorClosure

end

end HodgeConjecture
