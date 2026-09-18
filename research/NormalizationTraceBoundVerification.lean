import HodgeConjecture.Boundary.Normalization.NormalizationTraceBound
import Lean.Util.CollectAxioms

/-!
Focused SP66 regressions. Run with
`lake env lean research/NormalizationTraceBoundVerification.lean`.
The generic trace-dual denominator is tested without Noetherianity or
module-finiteness of the normalization. Boundary landing and properness
remain explicit hypotheses in their respective tests. All eleven new
public declarations have an enforced standard-axiom allowlist.
The SP75 boundary tests use separability of the marked extension directly.
-/

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.NormalizationInertia

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

section Generic

variable (B K T N : Type*)
variable [CommRing B] [Field K] [CommRing T] [Field N]
variable [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
variable [IsScalarTower B K N] [IsScalarTower B T N]

example (z : N) : z ∈ Submodule.traceDual B K (1 : Submodule T N) ↔
    ∀ t : T, Algebra.trace K N (z * algebraMap T N t) ∈
      (algebraMap B K).range :=
  mem_traceDual_unit_iff B K T N z

-- The existing carrier is genuinely a T-submodule, not merely a predicate.
example (a : T) (x y : N)
    (hx : x ∈ Submodule.traceDual B K (1 : Submodule T N))
    (hy : y ∈ Submodule.traceDual B K (1 : Submodule T N)) :
    algebraMap T N a * x + y ∈ Submodule.traceDual B K (1 : Submodule T N) := by
  simpa only [Algebra.smul_def] using
    (Submodule.traceDual B K (1 : Submodule T N)).add_mem
      ((Submodule.traceDual B K (1 : Submodule T N)).smul_mem a hx) hy

variable [IsIntegralClosure T B N]
variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K N) (hb : ∀ i, IsIntegral B (b i))
    (z : N) (hz : z ∈ Submodule.traceDual B K (1 : Submodule T N)) :
    z ∈ Submodule.span T (Set.range
      ((Algebra.traceForm K N).dualBasis (traceForm_nondegenerate K N) b)) :=
  traceDual_unit_le_span_traceDual B K T N b hb hz

variable [IsDomain B] [IsDomain T]
variable [IsFractionRing B K] [IsFractionRing T N]

-- The one denominator quantifies over the entire dual, not a finite test set.
example : ∃ d : T, d ≠ 0 ∧
    ∀ z ∈ Submodule.traceDual B K (1 : Submodule T N),
      algebraMap T N d * z ∈ (algebraMap T N).range := by
  fail_if_success have _ : IsNoetherianRing T := inferInstance
  fail_if_success have _ : Module.Finite B T := inferInstance
  exact exists_nonzero_traceDual_unit_denominator B K T N

-- B0 consumes the proved denominator; only its overring conclusion needs normality.
example [IsNoetherianRing T] [IsIntegrallyClosed T]
    (R : Subalgebra T N) (s : T) (hs : s ≠ 0)
    (hLanding : s ∈ (Submodule.traceDual B K (1 : Submodule T N)).colon
      R.toSubmodule) : R = ⊥ := by
  obtain ⟨d, hd, hdz⟩ := exists_nonzero_traceDual_unit_denominator B K T N
  exact subalgebra_eq_bot_of_mem_colon T N R
    (Submodule.traceDual B K (1 : Submodule T N)) d hd hdz s hs hLanding

end Generic

-- In the trivial field extension the trace dual is the entire field.
example : Submodule.traceDual ℚ ℚ (1 : Submodule ℚ ℚ) = ⊤ := by
  apply top_unique
  intro z _
  rw [mem_traceDual_unit_iff ℚ ℚ ℚ ℚ]
  intro t
  exact ⟨_, rfl⟩

example : ∃ d : ℚ, d ≠ 0 ∧
    ∀ z ∈ Submodule.traceDual ℚ ℚ (1 : Submodule ℚ ℚ),
      algebraMap ℚ ℚ d * z ∈ (algebraMap ℚ ℚ).range := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro z _
  exact ⟨_, rfl⟩

section Boundary

universe u

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

example (z : N) : z ∈ normalizationTraceDual C ↔
    ∀ t : T₀, Algebra.trace K N (z * (t : N)) ∈
      Set.range (algebraMap B K) :=
  mem_normalizationTraceDual_iff C z

example [IsNoetherianRing B] : IsNoetherianRing T₀ :=
  normalization_isNoetherianRing C

-- No normality of B, Noetherianity, or perfectness is needed for normality of T₀.
example : IsIntegrallyClosed T₀ := normalization_isIntegrallyClosed C

example [Algebra.IsSeparable K L] : ∃ d : T₀, d ≠ 0 ∧
    ∀ z ∈ normalizationTraceDual C,
      (d : N) * z ∈ Set.range (algebraMap T₀ N) :=
  exists_nonzero_normalizationTraceDual_denominator C

variable [Algebra.IsSeparable K L] [IsNoetherianRing B]
variable (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)

example (s : T₀) (hs : s ≠ 0)
    (hLanding : s ∈ (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule) :
    boundarySectionSubalgebra C I hI = ⊥ :=
  boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon C I hI s hs hLanding

-- Landing quantifies over actual regular sections before passage to their image.
example (s : T₀) (hs : s ≠ 0)
    (hLanding : ∀ z : BoundarySectionRing C I,
      (s : N) * boundarySectionsToNormalClosure C I hI z ∈
        normalizationTraceDual C) :
    boundarySectionSubalgebra C I hI = ⊥ :=
  boundarySectionSubalgebra_eq_bot_of_trace_landing C I hI s hs hLanding

example (hProper : boundarySectionSubalgebra C I hI ≠ ⊥) :
    (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule = ⊥ :=
  normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot C I hI hProper

end Boundary

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.NormalizationInertia.mem_traceDual_unit_iff,
      `HodgeConjecture.NormalizationInertia.traceDual_unit_le_span_traceDual,
      `HodgeConjecture.NormalizationInertia.exists_nonzero_traceDual_unit_denominator,
      `HodgeConjecture.NormalizationInertia.normalizationTraceDual,
      `HodgeConjecture.NormalizationInertia.mem_normalizationTraceDual_iff,
      `HodgeConjecture.NormalizationInertia.normalization_isNoetherianRing,
      `HodgeConjecture.NormalizationInertia.normalization_isIntegrallyClosed,
      `HodgeConjecture.NormalizationInertia.exists_nonzero_normalizationTraceDual_denominator,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra_eq_bot_of_trace_landing,
      `HodgeConjecture.NormalizationInertia.normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
