import HodgeConjecture.Realization.Chow.MarkedAugmentedRealization

/-!
# Auxiliary reconstruction of a graph projector

This bench preserves the former core reconstruction helper and its three
regressions. Its namespace and definition are unchanged. It is not imported
by the active library or its verification spine.

The reconstructed correspondence is `encode (decode projector)`. No equality
with the chosen correspondence `projector` is proved. The active proof keeps
the supplied projector and, when applicable, its original restriction law.

Run with `lake env lean research/bench/ProjectorReconstruction.lean`.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w z

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable {Gamma : Type w} [Ring Gamma] [Algebra ℚ Gamma]
variable {H : Type v} [AddCommGroup H] [Module ℚ H]
variable {M : MarkedAugmentedAlgebra ℚ A}
variable {rho : RationalCorrespondenceAction Gamma (ℚ × H)}
variable {projector : Gamma}

namespace MarkedProjectorActionComparison

/-- Reconstruct a graph-projector lift from the decoded Chow class.
The chosen correspondence is literally `construct.encode (detect.decode projector)`;
it need not be the original correspondence. Neither original idempotence nor
surjectivity of the residual realization is required. -/
def reconstructedGraphProjectorLift
    {Chow : Type z} [AddCommGroup Chow] [Module ℚ Chow]
    {N : RationalHodgeCycleClassModel Chow H}
    (B : MarkedProjectorActionComparison M rho projector)
    (construct : ClassGraphProjectorConstruction N rho)
    (detect : ClassGraphProjectorDetection N rho) :
    AlgebraicProjectorLift rho
      (ClassGraphProjector.operator
        (M.generatedClass B.residualRealization)) where
  projector := construct.encode (detect.decode projector)
  projector_isIdempotent := construct.encode_isIdempotent (detect.decode projector)
  realizes := by
    rw [construct.encode_realizes, B.cycleClass_decode_eq_generatedClass detect]

end MarkedProjectorActionComparison

end

end HodgeConjecture

#check HodgeConjecture.MarkedProjectorActionComparison.reconstructedGraphProjectorLift
#print axioms HodgeConjecture.MarkedProjectorActionComparison.reconstructedGraphProjectorLift

noncomputable section CoreChowDetectionRegressions

open HodgeConjecture

variable {A Gamma Chow H : Type*}
variable [CommRing A] [Algebra ℚ A] [Ring Gamma] [Algebra ℚ Gamma]
variable [AddCommGroup Chow] [Module ℚ Chow] [AddCommGroup H] [Module ℚ H]
variable {M : MarkedAugmentedAlgebra ℚ A}
variable {N : RationalHodgeCycleClassModel Chow H}
variable {rho : RationalCorrespondenceAction Gamma (ℚ × H)} {projector : Gamma}
variable (B : MarkedProjectorActionComparison M rho projector)
variable (construct : ClassGraphProjectorConstruction N rho)
variable (detect : ClassGraphProjectorDetection N rho)

-- Reconstruction chooses encode(decode Π), with no idempotence assumption on Π.
example :
    (B.reconstructedGraphProjectorLift construct detect).projector =
      construct.encode (detect.decode projector) :=
  rfl

-- Its whole action realizes the generated class without surjectivity of B's map.
example :
    rho.action (B.reconstructedGraphProjectorLift construct detect).projector =
      ClassGraphProjector.operator (M.generatedClass B.residualRealization) :=
  (B.reconstructedGraphProjectorLift construct detect).realizes

-- The reconstructed lift also satisfies the complete universal algebra-hom square.
example :
    rho.action.comp
        (B.reconstructedGraphProjectorLift construct detect).algebraIdempotentMap =
      (B.reconstructedGraphProjectorLift construct detect).cohomologicalIdempotentMap :=
  (B.reconstructedGraphProjectorLift construct detect).realization_idempotentMap_square

end CoreChowDetectionRegressions
