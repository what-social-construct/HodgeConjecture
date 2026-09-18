import HodgeConjecture.Boundary
import HodgeConjecture.Correspondence
import Lean.Util.CollectAxioms

/-!
SP72 regressions for the actual function fields of dominant finite morphisms.
Run with `lake env lean research/FiniteFunctionFieldVerification.lean`.

The public umbrellas expose the generic-stalk map, its chart square and the
finite-extension result. Dominance alone supplies neither finiteness nor
étaleness. Finite-dimensionality uses no normality, Noetherianity, projectivity
or étale premise. Every new declaration has an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles HodgeConjecture.CollisionFoundations

noncomputable section

universe u

section Dominance

variable {X Y : Scheme.{u}} (p : Y ⟶ X) [IsDominant p]

-- Nonempty preimages need neither integral schemes nor a finite morphism.
example (U : X.Opens) [Nonempty U] : Nonempty (p ⁻¹ᵁ U) := by
  fail_if_success have _ : IsFinite p := inferInstance
  exact nonempty_preimage_of_isDominant p U

-- Generic-point preservation needs irreducibility, not reducedness.
example [IrreducibleSpace X] [IrreducibleSpace Y] :
    p.base (genericPoint Y) = genericPoint X :=
  genericPoint_eq_of_isDominant p

end Dominance

section ActualFields

variable {W X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p]

example : Function.Injective (functionFieldMapOfDominant p) := by
  fail_if_success have _ : IsFinite p := inferInstance
  fail_if_success have _ : IsEtale p := inferInstance
  exact functionFieldMapOfDominant_injective p

example (a : X.functionField) (ha : a ≠ 0) :
    functionFieldMapOfDominant p a ≠ 0 := by
  intro h
  apply ha
  apply functionFieldMapOfDominant_injective p
  simpa using h

example (U : X.Opens) [Nonempty U] :
    letI := nonempty_preimage_of_isDominant p U
    X.germToFunctionField U ≫ functionFieldMapOfDominant p =
      p.app U ≫ Y.germToFunctionField (p ⁻¹ᵁ U) :=
  functionFieldMapOfDominant_germ p U

-- The categorical square has the expected literal section-evaluation formula.
example (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    letI := nonempty_preimage_of_isDominant p U
    functionFieldMapOfDominant p ((X.germToFunctionField U) a) =
      Y.germToFunctionField (p ⁻¹ᵁ U) ((p.app U) a) := by
  letI := nonempty_preimage_of_isDominant p U
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (functionFieldMapOfDominant_germ p U)) a

example : functionFieldMapOfDominant (𝟙 X) = 𝟙 X.functionField :=
  functionFieldMapOfDominant_id

example (a : X.functionField) : functionFieldMapOfDominant (𝟙 X) a = a := by
  rw [functionFieldMapOfDominant_id]
  rfl

example [IsIntegral Z] (q : Z ⟶ Y) [IsDominant q] :
    functionFieldMapOfDominant (q ≫ p) =
      functionFieldMapOfDominant p ≫ functionFieldMapOfDominant q :=
  functionFieldMapOfDominant_comp p q

-- Three actual morphisms retain contravariant order under composition.
example [IsIntegral Z] [IsIntegral W] (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsDominant q] [IsDominant r] :
    functionFieldMapOfDominant ((r ≫ q) ≫ p) =
      functionFieldMapOfDominant p ≫ functionFieldMapOfDominant q ≫
        functionFieldMapOfDominant r := by
  rw [functionFieldMapOfDominant_comp, functionFieldMapOfDominant_comp]

example [IsOpenImmersion p] :
    functionFieldMapOfDominant p = (functionFieldIsoOfOpenImmersion p).hom :=
  functionFieldMapOfDominant_eq_openImmersion p

example [IsOpenImmersion p] (a : X.functionField) :
    functionFieldMapOfDominant p a = functionFieldEquivOfOpenImmersion p a := by
  rw [functionFieldMapOfDominant_eq_openImmersion]
  rfl

end ActualFields

section FiniteExtensions

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p]

example (U : X.Opens) [Nonempty U] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    IsScalarTower Γ(X, U) X.functionField Y.functionField :=
  functionFieldMapOfDominant_sectionScalarTower p U

example [IsFinite p] (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    FiniteDimensional X.functionField Y.functionField := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact functionFieldMapOfDominant_finiteDimensional_of_affine p U hU

-- The global theorem chooses an actual nonempty affine chart internally.
example [IsFinite p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    FiniteDimensional X.functionField Y.functionField :=
  functionFieldMapOfDominant_finiteDimensional p

-- Finiteness of an actual composite supplies the extension under its actual map.
example [IsFinite p] [IsIntegral Z] (q : Z ⟶ Y) [IsDominant q] [IsFinite q] :
    letI := (functionFieldMapOfDominant (q ≫ p)).hom.toAlgebra
    FiniteDimensional X.functionField Z.functionField :=
  functionFieldMapOfDominant_finiteDimensional (q ≫ p)

end FiniteExtensions

-- Identity morphisms are genuine scheme-level finite-extension smoke tests.
example (X : Scheme.{u}) [IsIntegral X] :
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    letI : Module X.functionField X.functionField := Algebra.toModule
    FiniteDimensional X.functionField X.functionField :=
  functionFieldMapOfDominant_finiteDimensional (𝟙 X)

example :
    let X := Spec (CommRingCat.of ℚ)
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    letI : Module X.functionField X.functionField := Algebra.toModule
    FiniteDimensional X.functionField X.functionField :=
  functionFieldMapOfDominant_finiteDimensional (𝟙 (Spec (CommRingCat.of ℚ)))

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SchemeCycles.nonempty_preimage_of_isDominant,
      `HodgeConjecture.SchemeCycles.genericPoint_eq_of_isDominant,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_injective,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_germ,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_eq_openImmersion,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_id,
      `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_comp,
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_sectionScalarTower,
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_finiteDimensional_of_affine,
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_finiteDimensional] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
