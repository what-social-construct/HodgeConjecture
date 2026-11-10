module

public import HodgeConjecture.Realization.Betti.RelativeCochains
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Actual full and empty subcomplexes test the relative kernel definition.
The original point pair with empty subcomplex retains a nonzero actual
degree-zero class; the full pair has zero cohomology in all degrees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial
open HodgeConjecture

namespace RelativeCochainsVerification

theorem fullPair_cochain_zero (S : SSet.{0}) (n : ℕ)
    (φ : RelativeCochains.Cochain (⊤ : S.Subcomplex) n) : φ = 0 := by
  apply Subtype.ext
  funext σ
  exact RelativeCochains.cochain_vanish _ n φ ⟨σ, by trivial⟩

theorem fullPair_complex_isZero (S : SSet.{0}) :
    IsZero (RelativeCochains.complex (⊤ : S.Subcomplex)) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact fullPair_cochain_zero S n φ

theorem fullPair_cohomology_isZero (S : SSet.{0}) (n : ℕ) :
    IsZero (RelativeCochains.Cohomology (⊤ : S.Subcomplex) n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (.up ℕ) n).map_isZero
    (fullPair_complex_isZero S)

def emptyPair_cochain (S : SSet.{0}) (n : ℕ) (φ : SubcomplexCochains.Cochain S n) :
    RelativeCochains.Cochain (⊥ : S.Subcomplex) n :=
  ⟨φ, by funext σ; exact σ.property.elim⟩

example (S : SSet.{0}) (n : ℕ) (φ : SubcomplexCochains.Cochain S n)
    (σ : S.obj (op ⦋n⦌)) : (emptyPair_cochain S n φ).val σ = φ σ := rfl

example (S : SSet.{0}) (n : ℕ) (φ : SubcomplexCochains.Cochain S n) :
    (RelativeCochains.differential _ n (emptyPair_cochain S n φ)).val =
      SubcomplexCochains.differential S n φ := rfl

example (S : SSet.{0}) (B : S.Subcomplex) (n : ℕ)
    (φ : SubcomplexCochains.Cochain B.toSSet n) :
    RelativeCochains.restrictionLinear B n (RelativeCochains.extension B n φ) = φ :=
  RelativeCochains.restriction_extension B n φ

example (S : SSet.{0}) (B : S.Subcomplex) (n : ℕ) :
    (RelativeCochains.intersectionSequence B n).Exact :=
  RelativeCochains.intersectionSequence_exact B n

example (S : SSet.{0}) (B : S.Subcomplex) (n : ℕ) :
    (RelativeCochains.unionSequence B n).Exact :=
  RelativeCochains.unionSequence_exact B n

example (S : SSet.{0}) (B : S.Subcomplex) (n : ℕ) :
    (RelativeCochains.pairSequence B n).Exact := RelativeCochains.pairSequence_exact B n

abbrev pointSpace : TopCat := TopCat.of Unit
abbrev pointSingular : SSet := TopCat.toSSet.obj pointSpace
abbrev pointEmpty : pointSingular.Subcomplex := ⊥

def pointRelativeCocycle : RelativeCochains.Cocycle pointEmpty 0 :=
  ⟨emptyPair_cochain pointSingular 0 (fun _ ↦ 1), by
    apply Subtype.ext
    change SingularCochains.differential pointSpace 0 (fun _ ↦ 1) = 0
    funext σ
    rw [SingularCochains.differential_apply, Fin.sum_univ_two]
    norm_num⟩

theorem pointRelativeCocycle_ne_zero : pointRelativeCocycle ≠ 0 := by
  intro h
  have he := congrArg (fun φ : RelativeCochains.Cocycle pointEmpty 0 ↦
    φ.val.val (SingularDegreeZero.simplexEquivSingularSet Unit 0
      (SingularDegreeZero.pointSimplex Unit ()))) h
  exact one_ne_zero he

/-- The actual point pair with empty subcomplex has a nonzero original relative H⁰ class. -/
theorem pointRelativeClass_ne_zero :
    RelativeCochains.cocycleClass pointEmpty 0 pointRelativeCocycle ≠ 0 := by
  intro h
  let K := RelativeCochains.complex pointEmpty
  let c := K.cyclesMk pointRelativeCocycle.val 1 (by simp) (by
    rw [RelativeCochains.complex_d]
    exact pointRelativeCocycle.property)
  have hc : c = 0 := by
    apply (CochainComplex.isoHomologyπ₀ K).toLinearEquiv.injective
    change RelativeCochains.cocycleClass pointEmpty 0 pointRelativeCocycle = _
    simpa using h
  have hv := congrArg (fun z ↦ K.iCycles 0 z) hc
  have hi : K.iCycles 0 c = pointRelativeCocycle.val :=
    K.i_cyclesMk (i := 0) pointRelativeCocycle.val 1 (by simp) _
  have hz : pointRelativeCocycle.val = 0 :=
    hi.symm.trans (hv.trans (map_zero (K.iCycles 0).hom))
  exact pointRelativeCocycle_ne_zero (Subtype.ext hz)

end RelativeCochainsVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.RelativeCochains.restriction,
      `HodgeConjecture.RelativeCochains.restrictionLinear,
      `HodgeConjecture.RelativeCochains.cochain_vanish,
      `HodgeConjecture.RelativeCochains.restriction_differential,
      `HodgeConjecture.RelativeCochains.differential,
      `HodgeConjecture.RelativeCochains.differential_squared,
      `HodgeConjecture.RelativeCochains.complex,
      `HodgeConjecture.RelativeCochains.inclusion,
      `HodgeConjecture.RelativeCochains.inclusion_comp_restriction,
      `HodgeConjecture.RelativeCochains.extension,
      `HodgeConjecture.RelativeCochains.restriction_extension,
      `HodgeConjecture.RelativeCochains.restrictionLinear_surjective,
      `HodgeConjecture.RelativeCochains.shortComplex,
      `HodgeConjecture.RelativeCochains.shortComplex_degreewise_shortExact,
      `HodgeConjecture.RelativeCochains.shortComplex_shortExact,
      `HodgeConjecture.RelativeCochains.forget,
      `HodgeConjecture.RelativeCochains.restrictCohomology,
      `HodgeConjecture.RelativeCochains.connecting,
      `HodgeConjecture.RelativeCochains.intersectionSequence_exact,
      `HodgeConjecture.RelativeCochains.unionSequence_exact,
      `HodgeConjecture.RelativeCochains.pairSequence_exact,
      `HodgeConjecture.RelativeCochains.cocycleClass,
      `HodgeConjecture.RelativeCochains.cocycleClass_surjective,
      `HodgeConjecture.RelativeCochains.connecting_cocycleClass,
      `HodgeConjecture.RelativeCochains.exists_connecting_representative,
      `HodgeConjecture.RelativeCochains.pullbackLinear,
      `HodgeConjecture.RelativeCochains.pullback,
      `HodgeConjecture.RelativeCochains.pullback_inclusion,
      `HodgeConjecture.RelativeCochains.subcomplexMap,
      `HodgeConjecture.RelativeCochains.pullback_restriction,
      `HodgeConjecture.RelativeCochains.shortComplexMap,
      `HodgeConjecture.RelativeCochains.connecting_naturality,
      `HodgeConjecture.RelativeCochains.pullbackIsoOfLE,
      `HodgeConjecture.RelativeCochains.pullbackIso,
      `HodgeConjecture.RelativeCochains.pullbackIso_hom,
      `RelativeCochainsVerification.fullPair_cochain_zero,
      `RelativeCochainsVerification.fullPair_complex_isZero,
      `RelativeCochainsVerification.fullPair_cohomology_isZero,
      `RelativeCochainsVerification.emptyPair_cochain,
      `RelativeCochainsVerification.pointRelativeCocycle,
      `RelativeCochainsVerification.pointRelativeCocycle_ne_zero,
      `RelativeCochainsVerification.pointRelativeClass_ne_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
