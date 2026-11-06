module

import HodgeConjecture
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP113 checks for composition of the existing finite cycle and Chow maps.
Run with `lake env lean research/FinitePushforwardCompositionVerification.lean`.

Regressions retain signed rational coefficients, merging image supports,
positive degree weights, three successive maps, coefficient extension and
the actual Chow quotient representatives. Every new public declaration is
audited against the standard three logical axioms through the root import.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory HodgeConjecture HodgeConjecture.SchemeCycles

noncomputable section

universe u v

section Cycles

variable {X Y Z T : Scheme.{u}}
variable (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g]

-- The law requires neither normal/integral ambient schemes nor an étale map.
example (R : Type v) [Semiring R] (c : Cycles X R) :
    finitePushforward R g (finitePushforward R f c) =
      finitePushforward R (f ≫ g) c := by
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : Etale f := inferInstance
  fail_if_success have _ : Nontrivial R := inferInstance
  exact LinearMap.congr_fun (finitePushforward_comp R f g) c

-- Three maps retain their order, on an arbitrary cycle rather than one generator.
example (R : Type v) [Semiring R] (h : Z ⟶ T) [IsFinite h] (c : Cycles X R) :
    finitePushforward R h (finitePushforward R g (finitePushforward R f c)) =
      finitePushforward R ((f ≫ g) ≫ h) c := by
  have hfg := LinearMap.congr_fun (finitePushforward_comp R f g) c
  change finitePushforward R g (finitePushforward R f c) = _ at hfg
  rw [hfg]
  exact LinearMap.congr_fun (finitePushforward_comp R (f ≫ g) h) c

-- Degree multiplication cannot silently replace the weight by one.
example (W : IntegralClosedSubscheme X) :
    0 < finitePushforwardDegree f W * finitePushforwardDegree g (imageSubscheme f W) :=
  Nat.mul_pos (finitePushforwardDegree_pos f W)
    (finitePushforwardDegree_pos g (imageSubscheme f W))

-- A negative rational coefficient survives the composite with both field degrees.
example (W : IntegralClosedSubscheme X) :
    (finitePushforward ℚ g (finitePushforward ℚ f (Finsupp.single W (-3 / 2 : ℚ))))
        (imageSubscheme (f ≫ g) W) =
      (-3 / 2 : ℚ) *
        (finitePushforwardDegree f W * finitePushforwardDegree g (imageSubscheme f W)) := by
  rw [← LinearMap.comp_apply, finitePushforward_comp, finitePushforward_single,
    finitePushforwardDegree_comp]
  simp [fundamentalCycle, Finsupp.smul_single, nsmul_eq_mul]

-- Distinct supports may merge; their weighted coefficients must add, not overwrite.
example (W₁ W₂ : IntegralClosedSubscheme X)
    (h : imageSubscheme (f ≫ g) W₁ = imageSubscheme (f ≫ g) W₂) :
    (finitePushforward ℚ g (finitePushforward ℚ f
        (Finsupp.single W₁ (-3 / 2 : ℚ) + Finsupp.single W₂ (5 / 2 : ℚ))))
        (imageSubscheme (f ≫ g) W₂) =
      (-3 / 2 : ℚ) * finitePushforwardDegree (f ≫ g) W₁ +
        (5 / 2 : ℚ) * finitePushforwardDegree (f ≫ g) W₂ := by
  rw [← LinearMap.comp_apply, finitePushforward_comp, map_add]
  simp [finitePushforward_single, fundamentalCycle, Finsupp.smul_single, h, nsmul_eq_mul]

-- Composition and integer-to-rational coefficient extension agree on every cycle.
example (c : Cycles X ℤ) :
    finitePushforward ℚ g (finitePushforward ℚ f
        (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c)) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _)
        (finitePushforward ℤ (f ≫ g) c) := by
  rw [← LinearMap.comp_apply, finitePushforward_comp, finitePushforward_rationalize]

end Cycles

section Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
variable [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
variable (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
variable (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g] (n : ℤ)

-- The theorem applies to genuine quotient classes with the original structural maps.
example (c : ChowGroup
    (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ (g ≫ p))) n) :
    chowFinitePushforward k p g n (chowFinitePushforward k (g ≫ p) f n c) =
      chowFinitePushforward k p (f ≫ g) n c :=
  LinearMap.congr_fun (chowFinitePushforward_comp k p f g n) c

-- Both routes preserve the same rationalized Chow class, including its relations.
example (c : ChowGroup
    (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ (g ≫ p))) n) :
    rationalChowFinitePushforward k p g n
        (rationalChowFinitePushforward k (g ≫ p) f n
          (chowRationalize _ n c)) =
      chowRationalize _ n (chowFinitePushforward k p (f ≫ g) n c) := by
  rw [← LinearMap.comp_apply, rationalChowFinitePushforward_comp]
  exact rationalChowFinitePushforward_rationalize k p (f ≫ g) n c

-- Identity laws are available on the existing integral and rational quotients.
example (c : ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Z p) n) :
    chowFinitePushforward k p (𝟙 Z) n c = c := by
  rw [chowFinitePushforward_id]
  rfl

example (c : RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Z p) n) :
    rationalChowFinitePushforward k p (𝟙 Z) n c = c := by
  rw [rationalChowFinitePushforward_id]
  rfl

end Chow

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.residueFieldDegree_comp,
    `HodgeConjecture.SchemeCycles.imageSubscheme_comp,
    `HodgeConjecture.SchemeCycles.finitePushforwardDegree_comp,
    `HodgeConjecture.SchemeCycles.finitePushforward_comp,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_id,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_comp,
    `HodgeConjecture.SchemeCycles.chowFinitePushforward_id,
    `HodgeConjecture.SchemeCycles.chowFinitePushforward_comp,
    `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward_id,
    `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward_comp]
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}"
