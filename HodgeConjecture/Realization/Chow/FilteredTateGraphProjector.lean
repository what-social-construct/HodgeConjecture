module

public import HodgeConjecture.Realization.TateHodgeStructure
public import HodgeConjecture.Realization.FilteredHodgeTarget
public import HodgeConjecture.Realization.Chow.TateGraphProjector

@[expose] public section

/-!
# The existing graph-projector equivalence for the filtration-derived target

The Tate-block Hodge compatibility input is now proved from the actual
complex filtration and its rational real structure. The graph operator,
cycle-class model and equivalence theorem are the existing ones.

Chow graph construction, lower-left detection, the correspondence action
and the type of the cycle map remain explicit inputs. No geometric
comparison, general cycle-class map or coverage theorem is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.PureRationalHodgeStructure

universe u v w

variable {H : Type u} [AddCommGroup H] [Module ℚ H]
variable {Chow : Type v} [AddCommGroup Chow] [Module ℚ Chow]

/-- The former Hodge-compatibility hypothesis is a theorem for the independently defined target. -/
theorem classGraphHodgeCompatibility (p : ℤ) (S : PureRationalHodgeStructure H (2 * p))
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ S.rationalHodgeClasses p) :
    ClassGraphProjectorHodgeCompatibility (cycleClassModel p S cl hType)
      (IsHodgeMorphism (tateBlock p S) (tateBlock p S)) where
  graph_isHodge_iff α := graph_isHodge_iff p S α

/-- Instantiate the original equivalence with proved Hodge compatibility.
The independent Chow construction and detection hypotheses are retained. -/
theorem rationalHodgeConjectureAt_iff_hodgeGraphLifts
    (p : ℤ) (S : PureRationalHodgeStructure H (2 * p))
    (cl : Chow →ₗ[ℚ] H) (hType : LinearMap.range cl ≤ S.rationalHodgeClasses p)
    {Γ : Type w} [Ring Γ] [Algebra ℚ Γ]
    (ρ : RationalCorrespondenceAction Γ (ℚ × H))
    (C : ClassGraphProjectorConstruction (cycleClassModel p S cl hType) ρ)
    (D : ClassGraphProjectorDetection (cycleClassModel p S cl hType) ρ) :
    RationalHodgeConjectureAt (cycleClassModel p S cl hType) ↔
      EveryClassGraphHodgeMorphismHasAlgebraicLift ρ
        (IsHodgeMorphism (tateBlock p S) (tateBlock p S)) :=
  rationalHodgeConjectureAt_iff_everyClassGraphHodgeMorphismHasAlgebraicLift C D
    (classGraphHodgeCompatibility p S cl hType)

end HodgeConjecture.PureRationalHodgeStructure
