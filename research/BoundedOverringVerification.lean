import HodgeConjecture.Boundary.Normalization.BoundedOverring
import Lean.Util.CollectAxioms

/-!
Focused SP64 regressions. Run with
`lake env lean research/BoundedOverringVerification.lean`.
The algebraic bound is uniform on a subalgebra; no boundary-section or
trace-dual realization is assumed by these tests.
-/

open HodgeConjecture.NormalizationInertia

section

variable (T N : Type*) [CommRing T] [IsNoetherianRing T] [IsIntegrallyClosed T]
variable [Field N] [Algebra T N] [IsFractionRing T N]

example (R : Subalgebra T N) (a : T) (ha : a ≠ 0)
    (h : ∀ r : R, algebraMap T N a * (r : N) ∈ Set.range (algebraMap T N)) :
    R = ⊥ :=
  subalgebra_eq_bot_of_nonzero_mul_mem_base T N R a ha h

example (R : Subalgebra T N) (M : Submodule T N) (d s : T)
    (hd : d ≠ 0) (hs : s ≠ 0)
    (hM : ∀ z ∈ M, algebraMap T N d * z ∈ Set.range (algebraMap T N))
    (hR : ∀ r ∈ R, s • r ∈ M) : R = ⊥ :=
  subalgebra_eq_bot_of_mem_colon T N R M d hd hM s hs
    (Submodule.mem_colon.mpr hR)

example (R : Subalgebra T N) (hR : R ≠ ⊥) (M : Submodule T N)
    (d : T) (hd : d ≠ 0)
    (hM : ∀ z ∈ M, algebraMap T N d * z ∈ Set.range (algebraMap T N)) :
    M.colon R.toSubmodule = ⊥ :=
  colon_eq_bot_of_subalgebra_ne_bot T N R hR M d hd hM

-- A proper overring supplies a failing section for each nonzero multiplier.
example (R : Subalgebra T N) (hR : R ≠ ⊥) (M : Submodule T N)
    (d : T) (hd : d ≠ 0)
    (hM : ∀ z ∈ M, algebraMap T N d * z ∈ Set.range (algebraMap T N))
    (s : T) (hs : s ≠ 0) : ∃ r ∈ R, s • r ∉ M := by
  classical
  by_contra h
  push_neg at h
  exact hR (subalgebra_eq_bot_of_mem_colon T N R M d hd hM s hs
    (Submodule.mem_colon.mpr h))

-- Zero clears every algebra vacuously; it is deliberately excluded above.
example (R : Subalgebra T N) :
    ∀ r : R, algebraMap T N 0 * (r : N) ∈ Set.range (algebraMap T N) := by
  intro r
  exact ⟨0, by simp⟩

-- The base subalgebra has the expected nonzero denominator 1.
example : ∃ a : T, a ≠ 0 ∧
    ∀ r : (⊥ : Subalgebra T N),
      algebraMap T N a * (r : N) ∈ Set.range (algebraMap T N) := by
  letI : IsDomain T := (IsFractionRing.injective T N).isDomain
  refine ⟨1, one_ne_zero, ?_⟩
  intro r
  simpa only [map_one, one_mul] using (Algebra.mem_bot.mp r.property)

end

#print axioms HodgeConjecture.NormalizationInertia.subalgebra_eq_bot_of_nonzero_mul_mem_base
#print axioms HodgeConjecture.NormalizationInertia.subalgebra_eq_bot_of_mem_colon
#print axioms HodgeConjecture.NormalizationInertia.colon_eq_bot_of_subalgebra_ne_bot

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.NormalizationInertia.subalgebra_eq_bot_of_nonzero_mul_mem_base,
      `HodgeConjecture.NormalizationInertia.subalgebra_eq_bot_of_mem_colon,
      `HodgeConjecture.NormalizationInertia.colon_eq_bot_of_subalgebra_ne_bot] do
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}"
