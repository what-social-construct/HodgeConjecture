module

import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP74 regressions for constructing the marked finite normal closure of the
actual generic-stalk extension. Run with
`lake env lean research/FunctionFieldNormalClosureVerification.lean`.

The public boundary umbrella exposes the construction. Finite extensions
construct marked normal closures without separability or perfectness inputs.
Separability of the marked extension makes any such closure Galois. Actual
finite dominant scheme morphisms supply the field data, and formal
unramifiedness or étaleness supplies separability. The marking retains both
the upstairs ambient inclusion and the actual downstairs generic-field map.
Every new declaration has an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles HodgeConjecture.CollisionFoundations

noncomputable section

universe uK uL uN u

section FiniteFields

variable (K : Type uK) (L : Type uL) [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]

example : NormalClosureData K L
    (IntermediateField.normalClosure K L (AlgebraicClosure L)) := by
  fail_if_success have _ : PerfectField K := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact NormalClosureData.ofAlgebraicClosure K L

example : FiniteDimensional K
    (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
  (NormalClosureData.ofAlgebraicClosure K L).finiteNormal

example : IsNormalClosure K L
    (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
  (NormalClosureData.ofAlgebraicClosure K L).normalClosure

example (x : L) :
    ((NormalClosureData.ofAlgebraicClosure K L).embedding x : AlgebraicClosure L) =
      algebraMap L (AlgebraicClosure L) x :=
  NormalClosureData.ofAlgebraicClosure_embedding_apply K L x

example : Function.Injective (NormalClosureData.ofAlgebraicClosure K L).embedding :=
  (NormalClosureData.ofAlgebraicClosure K L).embedding.injective

example (a : K) :
    (NormalClosureData.ofAlgebraicClosure K L).embedding (algebraMap K L a) =
      algebraMap K (IntermediateField.normalClosure K L (AlgebraicClosure L)) a :=
  (NormalClosureData.ofAlgebraicClosure K L).embedding.commutes a

-- Finiteness of the automorphism group does not require separability.
example : Finite (NormalClosureData.ofAlgebraicClosure K L).galoisGroup :=
  (NormalClosureData.ofAlgebraicClosure K L).finiteGaloisGroup

example [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
  (NormalClosureData.ofAlgebraicClosure K L).isSeparable

example [Algebra.IsSeparable K L] :
    IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)) := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact (NormalClosureData.ofAlgebraicClosure K L).isGalois_of_isSeparable

end FiniteFields

section SuppliedMarkedClosure

variable {K : Type uK} {L : Type uL} {N : Type uN}
variable [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable [Algebra.IsSeparable K L] (D : NormalClosureData K L N)

-- The separability theorem works for any existing marked package, not only
-- the newly chosen algebraic-closure model.
example : Algebra.IsSeparable K N := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.isSeparable

example : IsGalois K N := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.isGalois_of_isSeparable

end SuppliedMarkedClosure

-- An arbitrary field, with no perfectness premise, has the expected self-copy.
example (K : Type uK) [Field K] :
    IsGalois K (IntermediateField.normalClosure K K (AlgebraicClosure K)) :=
  (NormalClosureData.ofAlgebraicClosure K K).isGalois_of_isSeparable

section ActualSchemes

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    NormalClosureData X.functionField Y.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  exact functionFieldNormalClosureData p

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    FiniteDimensional X.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldNormalClosureData p).finiteNormal

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IsNormalClosure X.functionField Y.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldNormalClosureData p).normalClosure

example (x : Y.functionField) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding x : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) x :=
  functionFieldNormalClosureData_embedding_apply p x

-- The distinguished embedding commutes with the actual generic-stalk map.
example (a : X.functionField) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).embedding (functionFieldMapOfDominant p a) =
      algebraMap X.functionField
        (IntermediateField.normalClosure X.functionField Y.functionField
          (AlgebraicClosure Y.functionField)) a := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldNormalClosureData p).embedding.commutes a

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Finite (functionFieldNormalClosureData p).galoisGroup := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldNormalClosureData p).finiteGaloisGroup

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IsGalois X.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) := by
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : CharZero X.functionField := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  exact functionFieldNormalClosure_isGalois p

example [Etale p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IsGalois X.functionField
      (IntermediateField.normalClosure X.functionField Y.functionField
        (AlgebraicClosure Y.functionField)) :=
  functionFieldNormalClosure_isGalois p

-- Construct the marked Galois closure of an actual finite étale composite.
example [Etale p] [IsIntegral Z] (q : Z ⟶ Y)
    [IsDominant q] [IsFinite q] [Etale q] :
    letI := (functionFieldMapOfDominant (q ≫ p)).hom.toAlgebra
    IsGalois X.functionField
      (IntermediateField.normalClosure X.functionField Z.functionField
        (AlgebraicClosure Z.functionField)) :=
  functionFieldNormalClosure_isGalois (q ≫ p)

end ActualSchemes

example (X : Scheme.{u}) [IsIntegral X] :
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    IsGalois X.functionField
      (IntermediateField.normalClosure X.functionField X.functionField
        (AlgebraicClosure X.functionField)) :=
  functionFieldNormalClosure_isGalois (𝟙 X)

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.NormalClosureData.ofAlgebraicClosure,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.ofAlgebraicClosure_embedding_apply,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.isSeparable,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.isGalois_of_isSeparable,
      `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureData,
      `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureData_embedding_apply,
      `HodgeConjecture.CollisionFoundations.functionFieldNormalClosure_isGalois] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
