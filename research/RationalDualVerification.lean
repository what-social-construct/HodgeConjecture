module

public import HodgeConjecture.Realization.Betti.RationalDual
public import HodgeConjecture.Realization.Betti.SingularSubdivisionHomology
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Unrestricted rational duals retain infinite-dimensional functionals, exact
split sequences, actual differential transposes and subdivision quasi-isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RationalDualVerification

open CategoryTheory Opposite HomologicalComplex HodgeConjecture.RationalDual

noncomputable section

/-- Sum all finitely many input coefficients; its values on basis vectors have infinite support. -/
def allCoefficients : Module.Dual ℚ (ℕ →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun _ : ℕ ↦ (1 : ℚ))

example (n : ℕ) : allCoefficients (Finsupp.single n 1) = 1 := by
  simp [allCoefficients]

theorem allCoefficients_basis_not_finitely_supported :
    ¬ (Function.support (fun n : ℕ ↦ allCoefficients (Finsupp.single n 1))).Finite := by
  have hs : Function.support (fun n : ℕ ↦ allCoefficients (Finsupp.single n 1)) = Set.univ := by
    ext n
    simp [Function.mem_support, allCoefficients]
  rw [hs]
  exact Set.infinite_univ

/-- A split exact sequence with an infinite-dimensional final term. -/
def splitSequence : ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.moduleCatMk
    (LinearMap.inl ℚ ℚ (ℕ →₀ ℚ)) (LinearMap.snd ℚ ℚ (ℕ →₀ ℚ)) (by ext x; rfl)

theorem splitSequence_exact : splitSequence.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  rintro ⟨a, v⟩ hv
  exact ⟨a, Prod.ext rfl hv.symm⟩

-- Exactness after unrestricted dualization needs no dimension assumption on the infinite term.
example : (splitSequence.op.map functor).Exact :=
  map_exact splitSequence.op splitSequence_exact.op

example (M N : ModuleCat.{0} ℚ) (f : M ⟶ N) (φ : Module.Dual ℚ N) (x : M) :
    (show Module.Dual ℚ M from functor.map f.op φ).toFun x = φ (f x) :=
  functor_map_apply f.op φ x

example (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (φ : Module.Dual ℚ (K.X 2)) (x : K.X 3) :
    (show Module.Dual ℚ (K.X 3) from (dualComplex K).d 2 3 φ).toFun x = φ (K.d 3 2 x) :=
  dualComplex_d_apply K 2 3 φ x

example {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (φ : Module.Dual ℚ (L.X n)) (x : K.X n) :
    (show Module.Dual ℚ (K.X n) from (dualMap f).f n φ).toFun x = φ (f.f n x) :=
  dualMap_f_apply f n φ x

example (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) : QuasiIso (dualMap (𝟙 K)) :=
  dualMap_quasiIso _

-- A genuine unbounded singular chain operation, not just an identity chain map.
example (X : TopCat.{0}) : QuasiIso (dualMap (HodgeConjecture.SingularSubdivision.subdivision X)) := by
  have : QuasiIso (HodgeConjecture.SingularSubdivision.subdivision X) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap,
      HodgeConjecture.SingularSubdivision.homologyMap_subdivision]
    infer_instance
  exact dualMap_quasiIso _

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.RationalDual.functor,
      `HodgeConjecture.RationalDual.functor_map_apply,
      `HodgeConjecture.RationalDual.map_exact,
      `HodgeConjecture.RationalDual.chainFunctor,
      `HodgeConjecture.RationalDual.dualComplex,
      `HodgeConjecture.RationalDual.dualMap,
      `HodgeConjecture.RationalDual.dualComplex_X,
      `HodgeConjecture.RationalDual.dualComplex_d,
      `HodgeConjecture.RationalDual.dualComplex_d_apply,
      `HodgeConjecture.RationalDual.dualMap_f_apply,
      `HodgeConjecture.RationalDual.dualMap_quasiIso,
      `RationalDualVerification.allCoefficients_basis_not_finitely_supported,
      `RationalDualVerification.splitSequence_exact] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"

end

end RationalDualVerification
