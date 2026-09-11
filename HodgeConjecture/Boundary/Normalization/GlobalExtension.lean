import HodgeConjecture.Boundary.Normalization.InertiaDiagram
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Purity and global normalization inputs

This module retains the two literature-supplied geometric statements that
were previously hard-coded for the affine plane:

* purity promotes absence of codimension-one ramification to étaleness of
  the finite normalization;
* finite-étale rigidity trivializes the selected connected normalization.

They are stated as explicit, base-specific inputs rather than global axioms:
neither assertion is true for an arbitrary base.  A concrete application
should construct `NormalizationLiteratureInputs` from the hypotheses and
citations appropriate to its chosen compactification.

The Ax--Grothendieck and Keller-map statements from the former planar branch
are intentionally absent because they belong to the Jacobian-conjecture
application, not to the collision-projector construction.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace NormalizationInertia

section LiteratureInputs

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}

/--
Purity for the selected finite normalization: absence of ramification at
height-one points promotes the normalization morphism to an étale morphism.

This proposition records the conclusion supplied by the relevant purity
theorem; its geometric hypotheses are verified when the input is constructed.
-/
def NormalizationPurity : Prop :=
  Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N)) →
    NoCodimensionOneRamification (B := B) (N := N) →
    IsEtale
      (normalClosureNormalizationToBase (B := B) (N := N))

/--
Rigidity for the selected connected finite étale normalization: if its
normalization morphism is étale, then the normal-closure extension is trivial.

This is base-specific—for example, it can follow from triviality of the
relevant finite étale fundamental group—and is therefore kept explicit.
-/
def FiniteEtaleNormalizationRigidity
    (D : CollisionFoundations.NormalClosureData K L N) : Prop :=
  Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N)) →
    IsEtale
      (normalClosureNormalizationToBase (B := B) (N := N)) →
    D.ExtensionTrivial

/--
The two literature inputs needed to turn the boundary-inertia calculation
into global triviality of a selected normalization.
-/
structure NormalizationLiteratureInputs
    (C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j) : Prop where
  purity : NormalizationPurity (B := B) (N := N)
  finiteEtaleRigidity :
    FiniteEtaleNormalizationRigidity (B := B) C.normalClosure

end LiteratureInputs

section GlobalTriviality

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
  {C : NormalizedCover
    (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

omit [IsFractionRing B K] in
/--
Purity and finite-étale rigidity turn the boundary-inertia calculation into
triviality of the normal closure.
-/
theorem normalClosureExtensionTrivial
    [PerfectField K]
    (D : Diagram C)
    (G : NormalizationLiteratureInputs C)
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    C.normalClosure.ExtensionTrivial :=
  G.finiteEtaleRigidity C.finiteNormalClosureModel
    (G.purity C.finiteNormalClosureModel
      (D.noCodimensionOneRamification hBoundary hNoHidden))

omit [IsFractionRing B K] in
/--
The same literature inputs trivialize the marked intermediate extension
`L / K`.
-/
theorem intermediateExtensionTrivial
    [PerfectField K]
    (D : Diagram C)
    (G : NormalizationLiteratureInputs C)
    (hBoundary : D.RamifiedConjugateCentersInBoundary)
    (hNoHidden : D.NoHiddenInertia) :
    CollisionFoundations.NormalClosureData.IntermediateExtensionTrivial K L :=
  C.normalClosure.intermediateExtensionTrivial_of_extensionTrivial
    (D.normalClosureExtensionTrivial G hBoundary hNoHidden)

omit [IsFractionRing B K] in
/--
Formal unramifiedness on the visible open produces the boundary condition,
so the literature inputs and no hidden inertia trivialize the normal closure.
-/
theorem normalClosureExtensionTrivial_of_formallyUnramified
    [PerfectField K] [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (G : NormalizationLiteratureInputs C)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia) :
    C.normalClosure.ExtensionTrivial :=
  D.normalClosureExtensionTrivial G
    (D.ramifiedConjugateCentersInBoundary R hFormal)
    hNoHidden

omit [IsFractionRing B K] in
/--
Formal unramifiedness on the visible open likewise trivializes the marked
intermediate extension.
-/
theorem intermediateExtensionTrivial_of_formallyUnramified
    [PerfectField K] [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (G : NormalizationLiteratureInputs C)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia) :
    CollisionFoundations.NormalClosureData.IntermediateExtensionTrivial K L :=
  C.normalClosure.intermediateExtensionTrivial_of_extensionTrivial
    (D.normalClosureExtensionTrivial_of_formallyUnramified
      R G hFormal hNoHidden)

end Diagram

end GlobalTriviality

end NormalizationInertia

end

end HodgeConjecture
