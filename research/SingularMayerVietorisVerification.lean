module

public import HodgeConjecture.Realization.Betti.SingularMayerVietoris
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The actual pair projections and inclusions normalize its cohomology product.
All three positions of the full singular Mayer–Vietoris sequence are tested,
including empty cover members and the original complex P¹ affine chart cover.
No calculation of a positive-degree singular group is assumed or asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SingularMayerVietorisVerification

open CategoryTheory HomologicalComplex HodgeConjecture

noncomputable section

section PairNormalization

variable {S : SSet.{0}} (A B : S.Subcomplex) (n : ℕ)

example (z : (SubcomplexCochains.pairComplex A B).homology n) :
    (CochainPair.cohomologyEquiv A B n z).1 = homologyMap (CochainPair.fst A B) n z := rfl

example (z : (SubcomplexCochains.pairComplex A B).homology n) :
    (CochainPair.cohomologyEquiv A B n z).2 = homologyMap (CochainPair.snd A B) n z := rfl

example (a : (SubcomplexCochains.complex (A : SSet)).homology n) :
    CochainPair.cohomologyEquiv A B n (homologyMap (CochainPair.inl A B) n a) = (a, 0) := by
  apply Prod.ext
  · change homologyMap (CochainPair.fst A B) n (homologyMap (CochainPair.inl A B) n a) = a
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, CochainPair.inl_fst, homologyMap_id]
    rfl
  · change homologyMap (CochainPair.snd A B) n (homologyMap (CochainPair.inl A B) n a) = 0
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, CochainPair.inl_snd, homologyMap_zero]
    rfl

example (b : (SubcomplexCochains.complex (B : SSet)).homology n) :
    CochainPair.cohomologyEquiv A B n (homologyMap (CochainPair.inr A B) n b) = (0, b) := by
  apply Prod.ext
  · change homologyMap (CochainPair.fst A B) n (homologyMap (CochainPair.inr A B) n b) = 0
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, CochainPair.inr_fst, homologyMap_zero]
    rfl
  · change homologyMap (CochainPair.snd A B) n (homologyMap (CochainPair.inr A B) n b) = b
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, CochainPair.inr_snd, homologyMap_id]
    rfl

example (a : (SubcomplexCochains.complex (A : SSet)).homology n)
    (b : (SubcomplexCochains.complex (B : SSet)).homology n) :
    (CochainPair.cohomologyEquiv A B n).symm (a, b) =
      homologyMap (CochainPair.inl A B) n a + homologyMap (CochainPair.inr A B) n b := rfl

end PairNormalization

section FullSequence

variable (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ) (n : ℕ)

example : (SingularMayerVietoris.pairSequence X U V hU hV hcover n).Exact :=
  SingularMayerVietoris.pairSequence_exact X U V hU hV hcover n

example : (SingularMayerVietoris.intersectionSequence X U V hU hV hcover n).Exact :=
  SingularMayerVietoris.intersectionSequence_exact X U V hU hV hcover n

example : (SingularMayerVietoris.unionSequence X U V hU hV hcover n).Exact :=
  SingularMayerVietoris.unionSequence_exact X U V hU hV hcover n

example : Mono (SingularMayerVietoris.restriction X U V 0) :=
  SingularMayerVietoris.mono_restriction_zero X U V hU hV hcover

end FullSequence

-- The genuine boundary case includes empty cover members and the empty space.
example (X : TopCat.{0}) :
    (SingularMayerVietoris.pairSequence X Set.univ ∅ isOpen_univ isOpen_empty (by simp) 0).Exact :=
  SingularMayerVietoris.pairSequence_exact X Set.univ ∅ isOpen_univ isOpen_empty (by simp) 0

example (X : TopCat.{0}) :
    (SingularMayerVietoris.intersectionSequence X ∅ Set.univ isOpen_empty isOpen_univ (by simp) 1).Exact :=
  SingularMayerVietoris.intersectionSequence_exact X ∅ Set.univ isOpen_empty isOpen_univ (by simp) 1

example : (SingularMayerVietoris.unionSequence (TopCat.of Empty) ∅ ∅ isOpen_empty isOpen_empty
    (by ext x; exact x.elim) 2).Exact :=
  SingularMayerVietoris.unionSequence_exact (TopCat.of Empty) ∅ ∅ isOpen_empty isOpen_empty
    (by ext x; exact x.elim) 2

-- The cover consists of the original affine evaluation charts of actual scheme-valued points.
example : (SingularMayerVietoris.pairSequence (TopCat.of ProjectiveLineComplexPoints.Point)
    (Set.range ProjectiveLineComplexPoints.finite) (Set.range ProjectiveLineComplexPoints.reciprocal)
    ProjectiveLineComplexPoints.isOpenEmbedding_finite.isOpen_range
    ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal.isOpen_range
    ProjectiveLineComplexPoints.range_finite_union_reciprocal 0).Exact :=
  SingularMayerVietoris.pairSequence_exact _ _ _
    ProjectiveLineComplexPoints.isOpenEmbedding_finite.isOpen_range
    ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal.isOpen_range
    ProjectiveLineComplexPoints.range_finite_union_reciprocal 0

example : (SingularMayerVietoris.pairSequence (TopCat.of ProjectiveLineComplexPoints.Point)
    (Set.range ProjectiveLineComplexPoints.finite) (Set.range ProjectiveLineComplexPoints.reciprocal)
    ProjectiveLineComplexPoints.isOpenEmbedding_finite.isOpen_range
    ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal.isOpen_range
    ProjectiveLineComplexPoints.range_finite_union_reciprocal 1).Exact :=
  SingularMayerVietoris.pairSequence_exact _ _ _
    ProjectiveLineComplexPoints.isOpenEmbedding_finite.isOpen_range
    ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal.isOpen_range
    ProjectiveLineComplexPoints.range_finite_union_reciprocal 1

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CochainPair.fst,
      `HodgeConjecture.CochainPair.snd,
      `HodgeConjecture.CochainPair.inl,
      `HodgeConjecture.CochainPair.inr,
      `HodgeConjecture.CochainPair.inl_fst,
      `HodgeConjecture.CochainPair.inl_snd,
      `HodgeConjecture.CochainPair.inr_fst,
      `HodgeConjecture.CochainPair.inr_snd,
      `HodgeConjecture.CochainPair.total,
      `HodgeConjecture.CochainPair.cohomologyEquiv,
      `HodgeConjecture.CochainPair.cohomologyIso,
      `HodgeConjecture.SingularMayerVietoris.pullbackIso,
      `HodgeConjecture.SingularMayerVietoris.chartCohomologyIso,
      `HodgeConjecture.SingularMayerVietoris.pairCohomologyIso,
      `HodgeConjecture.SingularMayerVietoris.intersectionCohomologyIso,
      `HodgeConjecture.SingularMayerVietoris.transport,
      `HodgeConjecture.SingularMayerVietoris.transportIso,
      `HodgeConjecture.SingularMayerVietoris.transport_exact,
      `HodgeConjecture.SingularMayerVietoris.restriction,
      `HodgeConjecture.SingularMayerVietoris.difference,
      `HodgeConjecture.SingularMayerVietoris.connecting,
      `HodgeConjecture.SingularMayerVietoris.pairSequence,
      `HodgeConjecture.SingularMayerVietoris.pairSequence_f,
      `HodgeConjecture.SingularMayerVietoris.pairSequence_g,
      `HodgeConjecture.SingularMayerVietoris.pairSequence_exact,
      `HodgeConjecture.SingularMayerVietoris.intersectionSequence,
      `HodgeConjecture.SingularMayerVietoris.intersectionSequence_f,
      `HodgeConjecture.SingularMayerVietoris.intersectionSequence_g,
      `HodgeConjecture.SingularMayerVietoris.intersectionSequence_exact,
      `HodgeConjecture.SingularMayerVietoris.unionSequence,
      `HodgeConjecture.SingularMayerVietoris.unionSequence_f,
      `HodgeConjecture.SingularMayerVietoris.unionSequence_g,
      `HodgeConjecture.SingularMayerVietoris.unionSequence_exact,
      `HodgeConjecture.SingularMayerVietoris.restriction_comp_difference,
      `HodgeConjecture.SingularMayerVietoris.difference_comp_connecting,
      `HodgeConjecture.SingularMayerVietoris.connecting_comp_restriction,
      `HodgeConjecture.SingularMayerVietoris.mono_restriction_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"

end

end SingularMayerVietorisVerification
