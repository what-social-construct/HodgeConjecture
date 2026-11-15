module

public import HodgeConjecture.Realization.HodgeFiltration
public import HodgeConjecture.Realization.HodgeClasses

@[expose] public section

/-!
# The cycle target attached to an independently constructed Hodge filtration

The target subspace is computed from the complex filtration and canonical
rational conjugation. A cycle map and its type theorem can then instantiate
the existing cycle-class model. Neither the filtration nor the target is
defined from the image of that map. The pure-structure specialization has
the actual rational type-(p,p) space as its target.

The existing graph-projector equivalences consume exactly these original
`RationalHodgeCycleClassModel` objects. Their Chow construction and detection
inputs remain separate from the construction of the Hodge space.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HodgeFiltration

universe u v

variable {H : Type u} [AddCommGroup H] [Module ℚ H]
variable {Chow : Type v} [AddCommGroup Chow] [Module ℚ Chow]

/-- Attach a cycle map only after the rational filtration target is fixed. -/
def cycleClassModel
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ)
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ rationalHodgeClasses F p) :
    RationalHodgeCycleClassModel Chow H where
  hodgeClasses := rationalHodgeClasses F p
  cycleClass := cl
  cycleClass_lands := hType

/-- The conjecture for this model has the actual filtration-membership premise. -/
theorem target_iff
    (F : ℤ → Submodule ℂ (RationalComplexification.Space H)) (p : ℤ)
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ rationalHodgeClasses F p) :
    RationalHodgeConjectureAt (cycleClassModel F p cl hType) ↔
      ∀ α : H, RationalComplexification.embedding H α ∈ F p →
        ∃ z : Chow, cl z = α := by
  change (rationalHodgeClasses F p ≤ LinearMap.range cl) ↔ _
  simp only [IsConcreteLE.le_iff, mem_rationalHodgeClasses_iff, LinearMap.mem_range]

end HodgeConjecture.HodgeFiltration

namespace HodgeConjecture.PureRationalHodgeStructure

universe u v

variable {H : Type u} [AddCommGroup H] [Module ℚ H]
variable {Chow : Type v} [AddCommGroup Chow] [Module ℚ Chow]

/-- The original fixed-codimension target for a genuine pure Hodge structure. -/
def cycleClassModel (p : ℤ) (S : PureRationalHodgeStructure H (2 * p))
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ S.rationalHodgeClasses p) :
    RationalHodgeCycleClassModel Chow H :=
  HodgeFiltration.cycleClassModel S.filtration p cl hType

theorem model_hodgeClasses (p : ℤ) (S : PureRationalHodgeStructure H (2 * p))
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ S.rationalHodgeClasses p) :
    (cycleClassModel p S cl hType).hodgeClasses = S.rationalHodgeClasses p := rfl

end HodgeConjecture.PureRationalHodgeStructure
