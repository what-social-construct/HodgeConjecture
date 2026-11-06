module

import HodgeConjecture.Realization.Chow.SupportedClass
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!+SP111: conditional extraction from supported cohomology into actual cycles.
Run with `lake env lean research/SupportedClassVerification.lean`.

The fixtures check finite expansion with an infinite index type, negative
rational multiplicities under actual closed pushforward, empty component
data, and the existing Hodge target with the constructed reduced boundary.
They do not instantiate general Betti localization or purity.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module HodgeConjecture HodgeConjecture.SchemeCycles
open HodgeConjecture.SupportedClass

noncomputable section

universe u v w

variable {X Z : Scheme.{u}} [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
variable (i : Z ⟶ X) [IsClosedImmersion i]

-- Finitely supported expansion works without a finite component index.
example (W : ℕ → IntegralClosedSubscheme Z)
    (hW : ∀ k, supportDegree (δ.comapClosedImmersion i) (W k) = n) :
    let C : ℕ → cyclesOfDegree ℚ (δ.comapClosedImmersion i) n := fun k ↦
      ⟨fundamentalCycle ℚ (W k), fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩
    (Finsupp.basisSingleOne.constr ℚ C)
        (Finsupp.single 2 (-(3 / 2 : ℚ)) + Finsupp.single 5 (7 / 3 : ℚ)) =
      -(3 / 2 : ℚ) • C 2 + (7 / 3 : ℚ) • C 5 := by
  dsimp only
  have hs (k : ℕ) (q : ℚ) : Finsupp.single k q =
      q • (Finsupp.basisSingleOne : Basis ℕ ℚ (ℕ →₀ ℚ)) k := by
    simp [Finsupp.basisSingleOne, Finsupp.smul_single]
  rw [hs 2, hs 5, map_add, map_smul, map_smul]
  simp only [Basis.constr_basis]

-- The closed image retains the actual negative rational coefficient.
example (V : IntegralClosedSubscheme Z)
    (hV : supportDegree (δ.comapClosedImmersion i) V = n) :
    let c : cyclesOfDegree ℚ (δ.comapClosedImmersion i) n :=
      -(3 / 2 : ℚ) • ⟨fundamentalCycle ℚ V,
        fundamentalCycle_mem_cyclesOfDegree ℚ _ n V hV⟩
    (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n c).val
        (closedImageSubscheme i V) = -(3 / 2 : ℚ) := by
  dsimp only
  rw [gradedClosedImmersionPushforwardWithCoefficients_val,
    closedImmersionPushforward_apply_image]
  simp

-- No components: the comparison forces every supported image to be zero.
-- In particular an empty component basis cannot manufacture a nonzero class.
example {HZ HX : Type v} [AddCommGroup HZ] [Module ℚ HZ]
    [AddCommGroup HX] [Module ℚ HX]
    (b : Basis PEmpty ℚ HZ) (cl : RationalChowGroup δ n →ₗ[ℚ] HX)
    (forgetSupport : HZ →ₗ[ℚ] HX) (γ : HZ) : forgetSupport γ = 0 := by
  let W : PEmpty → IntegralClosedSubscheme Z := PEmpty.elim
  have hW : ∀ k, supportDegree (δ.comapClosedImmersion i) (W k) = n :=
    fun k ↦ k.elim
  have h := cycleClass_componentExpansion δ n i W hW b cl forgetSupport
    (fun k ↦ k.elim) γ
  have hc : b.constr ℚ (fun k ↦
      (⟨fundamentalCycle ℚ (W k), fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩ :
        cyclesOfDegree ℚ (δ.comapClosedImmersion i) n)) = 0 := by
    apply b.ext
    intro k
    exact k.elim
  simpa only [hc, LinearMap.zero_apply, map_zero] using h.symm

-- The actual reduced boundary supplies complementarity automatically.
-- The output is a class in the existing target Chow quotient, with the
-- independently specified Hodge model and no boundary Hodge conjecture.
example {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type v} {HZ HX HU : Type w}
    [AddCommGroup HZ] [Module ℚ HZ] [AddCommGroup HX] [Module ℚ HX]
    [AddCommGroup HU] [Module ℚ HU]
    (W : ι → IntegralClosedSubscheme (openComplementIdeal j).subscheme)
    (hW : ∀ k, supportDegree
      (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) (W k) = n)
    (b : Basis ι ℚ HZ) (M : RationalHodgeCycleClassModel (RationalChowGroup δ n) HX)
    (forgetSupport : HZ →ₗ[ℚ] HX) (restrictH : HX →ₗ[ℚ] HU)
    (hExact : LinearMap.range forgetSupport = LinearMap.ker restrictH)
    (hBasis : ∀ k, M.cycleClass (rationalClassMap δ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
        (openComplementIdeal j).subschemeι
        (fun V ↦ (supportDegree_comapClosedImmersion δ _ V).symm) n
        ⟨fundamentalCycle ℚ (W k),
          fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩)) =
        forgetSupport (b k))
    (α : HX) (hα : restrictH α = 0) : IsAlgebraicHodgeClass M α := by
  obtain ⟨c, hc, _⟩ := exists_supported_cycle_of_vanishing δ n
    (openComplementIdeal j).subschemeι W hW b j (range_openComplement j)
    M.cycleClass forgetSupport restrictH hExact hBasis α hα
  exact ⟨rationalClassMap δ n (gradedClosedImmersionPushforwardWithCoefficients ℚ
    (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
    (openComplementIdeal j).subschemeι
    (fun V ↦ (supportDegree_comapClosedImmersion δ _ V).symm) n c), hc⟩

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SupportedClass.cycleClass_componentExpansion,
    `HodgeConjecture.SupportedClass.exists_supported_cycle_of_vanishing,
    `HodgeConjecture.SupportedClass.vanishing_iff_supported_cycle]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}"
