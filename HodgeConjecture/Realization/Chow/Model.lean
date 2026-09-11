import HodgeConjecture.Correspondence.EtaleClasses
import HodgeConjecture.Correspondence.ProjectorLift

/-!
# Rational Chow-correspondence models

This module records the noncommutative correspondence algebras used by the
realization layer.  Multiplication is convolution and the unit is the
diagonal class.

For a smooth projective `d`-fold, the intended compactified algebra is

`CH^d(X × X)_ℚ`.

Mathlib does not currently construct this algebra with its refined
intersection product.  The algebra, generic restriction map, and
cohomological action therefore remain explicit geometric data rather than
being inferred from the free span algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u w q z

/--
A rational cohomological projector specified independently of any proposed
algebraic lift.

In the Hodge application, `operator` is additionally required to be a
morphism of rational Hodge structures.  That extra predicate is kept outside
this minimal interface until a full Hodge-structure library is available.
Thus this structure alone is not a Hodge projector.  The separately quantified
Hodge-class target and its canonical graph projectors are in
`Realization.HodgeClasses` and `Realization.Chow.TateGraphProjector`.
-/
structure RationalCohomologicalProjector
    (V : Type z) [AddCommGroup V] [Module ℚ V] where
  operator : Module.End ℚ V
  operator_isIdempotent : IsIdempotentElem operator

namespace RationalCohomologicalProjector

variable {V : Type z} [AddCommGroup V] [Module ℚ V]

/-- The complementary cohomological projector. -/
def complement
    (e : RationalCohomologicalProjector V) :
    RationalCohomologicalProjector V where
  operator := 1 - e.operator
  operator_isIdempotent := e.operator_isIdempotent.one_sub

@[simp]
theorem complement_operator
    (e : RationalCohomologicalProjector V) :
    e.complement.operator = 1 - e.operator :=
  rfl

end RationalCohomologicalProjector

namespace SchemeCorrespondence

variable {T X : Scheme.{u}} (pX : X ⟶ T)

/--
The noncommutative rational Chow-correspondence data needed by the
compactification argument.

`genericCycleClass` sends admissible finite-étale spans to their generic
cycle classes.  `restriction` restricts compactified classes to the generic
locus.  `cohomologicalAction` is the cycle-class action on rational
cohomology.  In a concrete model, rational equivalence and compatibility
with refined-intersection convolution must already have been proved in order
to construct these algebra homomorphisms.
-/
structure RationalChowCorrespondenceModel
    (genericAlgebra : Type q)
    (compactifiedAlgebra : Type w)
    (V : Type z)
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
    [AddCommGroup V] [Module ℚ V] where
  genericCycleClass :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ] genericAlgebra
  restriction :
    compactifiedAlgebra →ₐ[ℚ] genericAlgebra
  cohomologicalAction :
    RationalCorrespondenceAction compactifiedAlgebra V

namespace RationalChowCorrespondenceModel

variable {pX : X ⟶ T}
variable {genericAlgebra : Type q}
variable {compactifiedAlgebra : Type w}
variable {V : Type z}
variable [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
variable [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
variable [AddCommGroup V] [Module ℚ V]

/-- The compactified Chow-correspondence action, as the general action API. -/
abbrev action
    (χ :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra V) :
    RationalCorrespondenceAction compactifiedAlgebra V :=
  χ.cohomologicalAction

end RationalChowCorrespondenceModel

end SchemeCorrespondence

end

end HodgeConjecture
