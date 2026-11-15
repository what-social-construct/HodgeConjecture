module

public import HodgeConjecture.Realization.HodgeFiltration
public import HodgeConjecture.Realization.Betti.Scheme
public import HodgeConjecture.Realization.DeRham.SchemeHodgeFiltration

@[expose] public section

/-!
# The rational target of a specified Betti–de Rham comparison

Actual scheme de Rham hypercohomology and its derived degree filtration
are the source. Actual rational singular cohomology and its genuine tensor
complexification are the target. A specified comparison transports the
filtration; its rational diagonal intersection is constructed without cycles.

The original API keeps the topological space and comparison explicit.
The canonical specialization constructs the scheme's analytic complex
point space and singular Betti group; only the period isomorphism remains
an input. This module does not assert that arbitrary linear equivalences
are geometric comparisons, or prove opposedness/degeneration for general
varieties. The P¹ comparison is a concrete specialization of these data.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SchemeDeRham

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (T : TopCat.{0}) (n : ℕ)

/-- The already constructed rational singular group in the chosen degree. -/
abbrev RationalBetti := SingularCochains.Cohomology T n

variable (comparison : hypercohomology ℂ X f n ≃ₗ[ℂ]
  RationalComplexification.Space (RationalBetti T n))

/-- Transport of the actual degree-induced scheme de Rham filtration. -/
def bettiHodgeFiltration (p : ℤ) :
    Submodule ℂ (RationalComplexification.Space (RationalBetti T n)) :=
  (hodgeFiltration ℂ X f n p).map comparison.toLinearMap

theorem bettiHodgeFiltration_antitone : Antitone (bettiHodgeFiltration f T n comparison) := by
  intro p q hpq
  exact Submodule.map_mono ((hodgeFiltration_antitone ℂ X f n) hpq)

/-- Rational classes selected by the actual transported filtration and its conjugate. -/
def rationalBettiHodgeClasses (p : ℤ) : Submodule ℚ (RationalBetti T n) :=
  HodgeFiltration.rationalHodgeClasses (bettiHodgeFiltration f T n comparison) p

/-- A direct membership test through the inverse of the specified comparison. -/
theorem mem_rationalBettiHodgeClasses (p : ℤ) (α : RationalBetti T n) :
    α ∈ rationalBettiHodgeClasses f T n comparison p ↔
      comparison.symm (RationalComplexification.embedding (RationalBetti T n) α) ∈
        hodgeFiltration ℂ X f n p := by
  rw [rationalBettiHodgeClasses, HodgeFiltration.mem_rationalHodgeClasses_iff]
  constructor
  · rintro ⟨z, hz, he⟩
    simpa [← he] using hz
  · intro h
    exact ⟨_, h, comparison.apply_symm_apply _⟩

/-- The existing transported filtration on the canonical scheme complex-point space.
Only the period comparison remains an input; the point space is constructed. -/
abbrev complexPointsHodgeFiltration
    (periodComparison : hypercohomology ℂ X f n ≃ₗ[ℂ]
      RationalComplexification.Space (SchemeBetti.Cohomology f n)) (p : ℤ) :=
  bettiHodgeFiltration f (SchemeBetti.space f) n periodComparison p

/-- The same rational diagonal target, now using the scheme's actual analytic points. -/
abbrev complexPointsRationalHodgeClasses
    (periodComparison : hypercohomology ℂ X f n ≃ₗ[ℂ]
      RationalComplexification.Space (SchemeBetti.Cohomology f n)) (p : ℤ) :=
  rationalBettiHodgeClasses f (SchemeBetti.space f) n periodComparison p

theorem mem_complexPointsRationalHodgeClasses
    (periodComparison : hypercohomology ℂ X f n ≃ₗ[ℂ]
      RationalComplexification.Space (SchemeBetti.Cohomology f n))
    (p : ℤ) (α : SchemeBetti.Cohomology f n) :
    α ∈ complexPointsRationalHodgeClasses f n periodComparison p ↔
      periodComparison.symm (RationalComplexification.embedding _ α) ∈
        hodgeFiltration ℂ X f n p :=
  mem_rationalBettiHodgeClasses f (SchemeBetti.space f) n periodComparison p α

end HodgeConjecture.SchemeDeRham
