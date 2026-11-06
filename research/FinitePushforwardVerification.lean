module

import HodgeConjecture.Cycles.GradedFinitePushforward
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP101 focused checks for degree-weighted finite pushforward on the existing
raw and homogeneous cycle modules. Run with
`lake env lean research/FinitePushforwardVerification.lean`.

Images use the original mapped ideal sheaves. Degrees use the actual
support-to-image function-field map and are positive under supportwise
finiteness. The raw map preserves arbitrary semiring coefficients, including
signed integral/rational coefficients and merging image supports. Grading
uses the explicit compatibility of the supplied dimension functions, not a
new structural dimension-preservation claim or Chow-descent assumption.
The exact public registry includes definitions and checks the standard-three
Lean axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles

noncomputable section

universe u v

#check imageSubscheme
#check imageSubscheme_val
#check imageSubscheme_eq_closedImageSubscheme
#check ambientGenericPoint_imageSubscheme
#check finiteImage_toImage_isFinite
#check finitePushforwardDegree
#check finitePushforwardDegree_pos
#check finitePushforwardDegree_of_isClosedImmersion
#check finitePushforward
#check finitePushforward_single
#check finitePushforward_fundamentalCycle
#check finitePushforward_eq_closedImmersionPushforward
#check finitePushforward_id
#check supportDegree_imageSubscheme
#check finitePushforward_mem_cyclesOfDegree
#check gradedFinitePushforward
#check gradedFinitePushforward_val
#check gradedFinitePushforward_eq_closedImmersionPushforward
#check finitePushforward_rationalize
#check gradedFinitePushforward_rationalize

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Images

example (Z : IntegralClosedSubscheme X) : (imageSubscheme f Z).val = Z.val.map f :=
  imageSubscheme_val f Z

example (Z : IntegralClosedSubscheme X) : IsIntegral (imageSubscheme f Z).val.subscheme := by
  fail_if_success have _ : IsFinite f := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  exact (imageSubscheme f Z).property

example (Z : IntegralClosedSubscheme X) :
    ambientGenericPoint (imageSubscheme f Z) = f.base (ambientGenericPoint Z) :=
  ambientGenericPoint_imageSubscheme f Z

example (x : X) : imageSubscheme f (pointSupport X x) = pointSupport Y (f.base x) := by
  rw [← pointSupport_ambientGenericPoint (imageSubscheme f (pointSupport X x)),
    ambientGenericPoint_imageSubscheme, ambientGenericPoint_pointSupport]

example (Z : IntegralClosedSubscheme X) [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    imageSubscheme f Z = closedImageSubscheme f Z := by
  fail_if_success have _ : IsFinite f := inferInstance
  exact imageSubscheme_eq_closedImageSubscheme f Z

end Images

section SupportwiseDegree

example (Z : IntegralClosedSubscheme X) [IsFinite (Z.val.subschemeι ≫ f)] :
    IsFinite (Z.val.subschemeι ≫ f).toImage := by
  fail_if_success have _ : IsFinite f := inferInstance
  fail_if_success have _ : IsDominant f := inferInstance
  fail_if_success have _ : Etale f := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  exact finiteImage_toImage_isFinite f Z

example (Z : IntegralClosedSubscheme X) [IsFinite (Z.val.subschemeι ≫ f)] :
    letI := Z.property
    letI := (imageSubscheme f Z).property
    letI : IsIntegral (Z.val.subschemeι ≫ f).image := (imageSubscheme f Z).property
    letI : Algebra (imageSubscheme f Z).val.subscheme.functionField
        Z.val.subscheme.functionField :=
      (functionFieldMapOfDominant (Z.val.subschemeι ≫ f).toImage).hom.toAlgebra
    finitePushforwardDegree f Z =
      Module.finrank (imageSubscheme f Z).val.subscheme.functionField
        Z.val.subscheme.functionField := rfl

example (Z : IntegralClosedSubscheme X) [IsFinite (Z.val.subschemeι ≫ f)] :
    0 < finitePushforwardDegree f Z ∧ finitePushforwardDegree f Z ≠ 0 :=
  ⟨finitePushforwardDegree_pos f Z, Nat.ne_of_gt (finitePushforwardDegree_pos f Z)⟩

example (Z : IntegralClosedSubscheme X) [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    finitePushforwardDegree f Z = 1 :=
  finitePushforwardDegree_of_isClosedImmersion f Z

end SupportwiseDegree

section Raw

variable [IsFinite f]

example (R : Type v) [Semiring R] (Z : IntegralClosedSubscheme X) :
    finitePushforward R f (fundamentalCycle R Z) =
      finitePushforwardDegree f Z • fundamentalCycle R (imageSubscheme f Z) := by
  fail_if_success have _ : IsDominant f := inferInstance
  fail_if_success have _ : Etale f := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : Nontrivial R := inferInstance
  exact finitePushforward_fundamentalCycle f R Z

example (Z : IntegralClosedSubscheme X) :
    finitePushforward ℚ f (Finsupp.single Z (-3 / 2 : ℚ)) =
      (-3 / 2 : ℚ) •
        (finitePushforwardDegree f Z • fundamentalCycle ℚ (imageSubscheme f Z)) :=
  finitePushforward_single f ℚ Z (-3 / 2)

example (Z : IntegralClosedSubscheme X) :
    finitePushforward ℤ f (fundamentalCycle ℤ Z) (imageSubscheme f Z) =
      (finitePushforwardDegree f Z : ℤ) := by
  simp [fundamentalCycle]

example (Z : IntegralClosedSubscheme X) :
    finitePushforward ℤ f (fundamentalCycle ℤ Z) ≠ 0 := by
  intro h
  have hcoef := congrArg (fun c : Cycles Y ℤ => c (imageSubscheme f Z)) h
  have hpos := finitePushforwardDegree_pos f Z
  simp [fundamentalCycle] at hcoef
  omega

example (Z₁ Z₂ : IntegralClosedSubscheme X)
    (h : imageSubscheme f Z₁ = imageSubscheme f Z₂) :
    finitePushforward ℤ f (fundamentalCycle ℤ Z₁ + fundamentalCycle ℤ Z₂)
        (imageSubscheme f Z₁) =
      (finitePushforwardDegree f Z₁ : ℤ) + (finitePushforwardDegree f Z₂ : ℤ) := by
  rw [map_add]
  simp [fundamentalCycle, h]

example (R : Type v) [Semiring R] (r : R) (c d : Cycles X R) :
    finitePushforward R f 0 = 0 ∧
      finitePushforward R f (c + d) = finitePushforward R f c + finitePushforward R f d ∧
      finitePushforward R f (r • c) = r • finitePushforward R f c :=
  ⟨map_zero _, map_add _ _ _, map_smul _ _ _⟩

end Raw

example (R : Type v) [Semiring R] [IsClosedImmersion f] :
    finitePushforward R f = closedImmersionPushforward R f :=
  finitePushforward_eq_closedImmersionPushforward f R

example (R : Type v) [Semiring R] (c : Cycles X R) :
    finitePushforward R (𝟙 X) c = c := by
  rw [finitePushforward_id, LinearMap.id_apply]

example (R : Type v) [Semiring R] {T : Scheme.{u}}
    [IsClosedImmersion f] (g : Y ⟶ T) [IsClosedImmersion g] (c : Cycles X R) :
    finitePushforward R (f ≫ g) c = finitePushforward R g (finitePushforward R f c) := by
  simp only [finitePushforward_eq_closedImmersionPushforward]
  exact (LinearMap.congr_fun (closedImmersionPushforward_comp f R g) c).symm

section Graded

variable (δX : DimensionFunction X) (δY : DimensionFunction Y)

example (W : IntegralClosedSubscheme X) :
    supportDegree δY (imageSubscheme f W) = δY (f.base (ambientGenericPoint W)) := by
  fail_if_success have _ : IsFinite f := inferInstance
  exact supportDegree_imageSubscheme δY f W

variable [IsFinite f]
variable (hdeg : ∀ W : IntegralClosedSubscheme X,
  supportDegree δY (imageSubscheme f W) = supportDegree δX W)

example (R : Type v) [Semiring R] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R δX n) :
    finitePushforward R f c ∈ cyclesOfDegree R δY n :=
  finitePushforward_mem_cyclesOfDegree R δX δY f n c hc hdeg

example (R : Type v) [Semiring R] (n : ℤ) (c : cyclesOfDegree R δX n) :
    (gradedFinitePushforward R δX δY f hdeg n c).val =
      finitePushforward R f c.val := by
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : Etale f := inferInstance
  fail_if_success have _ : Nontrivial R := inferInstance
  exact gradedFinitePushforward_val R δX δY f hdeg n c

example (R : Type v) [Semiring R] (n : ℤ) (W : IntegralClosedSubscheme X)
    (r : R) (hW : supportDegree δX W = n) :
    (gradedFinitePushforward R δX δY f hdeg n
      ⟨Finsupp.single W r, single_mem_cyclesOfDegree R δX n W r hW⟩).val =
      r • (finitePushforwardDegree f W • fundamentalCycle R (imageSubscheme f W)) :=
  finitePushforward_single f R W r

example (R : Type v) [Semiring R] (n : ℤ) (W : IntegralClosedSubscheme X)
    (hW : supportDegree δX W = n) :
    (gradedFinitePushforward R δX δY f hdeg n
      ⟨fundamentalCycle R W, fundamentalCycle_mem_cyclesOfDegree R δX n W hW⟩).val =
      finitePushforwardDegree f W • fundamentalCycle R (imageSubscheme f W) :=
  finitePushforward_fundamentalCycle f R W

example (R : Type v) [Semiring R] (n : ℤ)
    (hdeg' : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W) :
    gradedFinitePushforward R δX δY f hdeg n =
      gradedFinitePushforward R δX δY f hdeg' n := rfl

example (n : ℤ) (c : cyclesOfDegree (PUnit : Type) δX n) :
    gradedFinitePushforward (PUnit : Type) δX δY f hdeg n c = 0 :=
  Subsingleton.elim _ _

example [IsClosedImmersion f] (R : Type v) [Semiring R] (n : ℤ)
    (hclosed : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme f W) = supportDegree δX W) :
    gradedFinitePushforward R δX δY f hdeg n =
      gradedClosedImmersionPushforwardWithCoefficients R δX δY f hclosed n :=
  gradedFinitePushforward_eq_closedImmersionPushforward R δX δY f hdeg n

example (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    gradedFinitePushforward ℚ δX δY f hdeg n (cyclesOfDegreeRationalize δX n c) =
      cyclesOfDegreeRationalize δY n (gradedFinitePushforward ℤ δX δY f hdeg n c) :=
  gradedFinitePushforward_rationalize δX δY f hdeg n c

example (n : ℤ) (W : IntegralClosedSubscheme X) (hW : supportDegree δX W = n) :
    (gradedFinitePushforward ℚ δX δY f hdeg n
      (cyclesOfDegreeRationalize δX n
        ⟨Finsupp.single W (-3 : ℤ), single_mem_cyclesOfDegree ℤ δX n W (-3) hW⟩)).val =
      (-3 : ℚ) • (finitePushforwardDegree f W • fundamentalCycle ℚ (imageSubscheme f W)) := by
  rw [cyclesOfDegreeRationalize_single δX n W (-3) hW]
  exact finitePushforward_single f ℚ W (-3)

end Graded

example [IsFinite f] (c : Cycles X ℤ) :
    finitePushforward ℚ f (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) (finitePushforward ℤ f c) :=
  finitePushforward_rationalize f c

example (R : Type v) [Semiring R] (δ : DimensionFunction X) (n : ℤ)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (imageSubscheme (𝟙 X) W) = supportDegree δ W)
    (c : cyclesOfDegree R δ n) :
    gradedFinitePushforward R δ δ (𝟙 X) hdeg n c = c := by
  apply Subtype.ext
  rw [gradedFinitePushforward_val, finitePushforward_id, LinearMap.id_apply]

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.imageSubscheme,
    `HodgeConjecture.SchemeCycles.imageSubscheme_val,
    `HodgeConjecture.SchemeCycles.imageSubscheme_eq_closedImageSubscheme,
    `HodgeConjecture.SchemeCycles.ambientGenericPoint_imageSubscheme,
    `HodgeConjecture.SchemeCycles.finiteImage_toImage_isFinite,
    `HodgeConjecture.SchemeCycles.finitePushforwardDegree,
    `HodgeConjecture.SchemeCycles.finitePushforwardDegree_pos,
    `HodgeConjecture.SchemeCycles.finitePushforwardDegree_of_isClosedImmersion,
    `HodgeConjecture.SchemeCycles.finitePushforward,
    `HodgeConjecture.SchemeCycles.finitePushforward_single,
    `HodgeConjecture.SchemeCycles.finitePushforward_fundamentalCycle,
    `HodgeConjecture.SchemeCycles.finitePushforward_eq_closedImmersionPushforward,
    `HodgeConjecture.SchemeCycles.finitePushforward_id,
    `HodgeConjecture.SchemeCycles.supportDegree_imageSubscheme,
    `HodgeConjecture.SchemeCycles.finitePushforward_mem_cyclesOfDegree,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_val,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_eq_closedImmersionPushforward,
    `HodgeConjecture.SchemeCycles.finitePushforward_rationalize,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_rationalize]
  unless declarations.length == 20 && declarations.eraseDups.length == 20 do
    throwError "Expected exactly twenty distinct SP101 public declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP101 audit registry: twenty distinct public declarations"
