module

public import HodgeConjecture.Cycles.OpenGrading

@[expose] public section

/-!
# Surjectivity of actual open restriction on finite cycles

Every actual integral closed support in an open scheme extends to its
reduced ambient closure, whose ideal-comap recovers the original support.
Finite linear combinations therefore lift along the existing restriction
map. The same construction preserves degree for the supplied restricted
dimension function. The closure lift is used only on cycles; no operation
on rational-equivalence classes is defined by taking closures.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

private def reducedClosureLift (R : Type v) [Semiring R]
    {U X : Scheme.{u}} (j : U ⟶ X) : Cycles U R →ₗ[R] Cycles X R :=
  Finsupp.linearCombination R (fun W ↦ fundamentalCycle R (openClosureSubscheme j W))

private theorem openRestriction_comp_reducedClosureLift (R : Type v) [Semiring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openRestriction R j).comp (reducedClosureLift R j) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro W a
  change openRestriction R j (reducedClosureLift R j (Finsupp.single W a)) =
    Finsupp.single W a
  rw [reducedClosureLift, Finsupp.linearCombination_single, map_smul,
    openRestriction_fundamentalCycle_of_comap_eq j R (openClosureSubscheme j W) W
      (openClosureSubscheme_comap j W)]
  simp [fundamentalCycle, Finsupp.smul_single]

private theorem reducedClosureLift_mem_cyclesOfDegree (R : Type v) [Semiring R]
    {U X : Scheme.{u}} (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) (c : Cycles U R) (hc : c ∈ cyclesOfDegree R (δ.comapOpenImmersion j) n) :
    reducedClosureLift R j c ∈ cyclesOfDegree R δ n := by
  have hle : cyclesOfDegree R (δ.comapOpenImmersion j) n ≤
      (cyclesOfDegree R δ n).comap (reducedClosureLift R j) := by
    change Finsupp.supported R R
      {W | supportDegree (δ.comapOpenImmersion j) W = n} ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨W, hW, rfl⟩
    change reducedClosureLift R j (Finsupp.single W 1) ∈ cyclesOfDegree R δ n
    rw [reducedClosureLift, Finsupp.linearCombination_single, one_smul]
    exact fundamentalCycle_mem_cyclesOfDegree R δ n (openClosureSubscheme j W)
      ((supportDegree_openClosureSubscheme δ j W).trans hW)
  exact hle hc

/-- Every finite cycle on the open scheme lifts to a finite cycle on the
ambient scheme, over any semiring and without ambient finiteness premises. -/
theorem openRestriction_surjective (R : Type v) [Semiring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Function.Surjective (openRestriction R j) := by
  intro c
  exact ⟨reducedClosureLift R j c,
    LinearMap.congr_fun (openRestriction_comp_reducedClosureLift R j) c⟩

/-- Every homogeneous finite cycle lifts in the same supplied degree,
using the actual composed dimension function on the open scheme. -/
theorem gradedOpenRestriction_surjective (R : Type v) [Semiring R]
    {U X : Scheme.{u}} (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℤ) : Function.Surjective (gradedOpenRestriction R δ j n) := by
  intro c
  refine ⟨⟨reducedClosureLift R j c.val,
    reducedClosureLift_mem_cyclesOfDegree R δ j n c.val c.property⟩, ?_⟩
  apply Subtype.ext
  exact LinearMap.congr_fun (openRestriction_comp_reducedClosureLift R j) c.val

end

end HodgeConjecture.SchemeCycles
