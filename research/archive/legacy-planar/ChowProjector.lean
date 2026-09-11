import HodgeConjecture.ChowProjector
import HodgeConjecture.Planar.Conclusion

/-!
# Planar purity and Chow projectors

This file connects the locally copied planar purity spine to the
correspondence, Chow, and Hodge-style realization interfaces of this project.
-/

set_option autoImplicit false

namespace HodgeConjecture.Planar

open CollisionIdeals
open CollisionIdeals.Planar

noncomputable section

universe u v w z t

variable {F : PlanarPolynomialMap}

/--
With the two geometric inputs made explicit, the local planar purity spine
kills the chosen off-diagonal collision idempotent.
-/
theorem planarCollisionIdempotent_eq_zero_of_branchPurity
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    planarCollisionIdempotent F M.keller = 0 := by
  apply
    (planarCollisionIdempotent_eq_zero_iff_ker_barMu_eq_bot
      F M.keller).2
  rw [collisionDiagonal_ker]
  exact
    planarVanishing_of
      hPurity hFiniteEtaleRigidity M hNoHidden

variable {Γ : Type u} {K : Type v} {V : Type w}
variable [Ring Γ] [CommRing K]
variable [AddCommGroup V] [Module K V]

/--
The planar collision idempotent realizes to a cohomological projector before
any purity or no-hidden-inertia input is used.
-/
theorem planarCollisionIdempotent_isRealizedProjector
    (hKeller : IsPlanarKeller F)
    (ρ : CorrespondenceRealization (CollisionRing F) Γ K V) :
    ρ.IsRealizedProjector
      (planarCollisionIdempotent F hKeller) := by
  exact
    ρ.isRealizedProjector
      (planarCollisionIdempotent_isProjector F hKeller).1

/--
After branch purity, finite-étale rigidity, and no hidden inertia, the
realized off-diagonal projector is the zero endomorphism.
-/
theorem planarRealizedProjector_eq_zero_of_branchPurity
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram)
    (ρ : CorrespondenceRealization (CollisionRing F) Γ K V) :
    ρ.realizedOperator
        (planarCollisionIdempotent F M.keller) = 0 := by
  have hq :
      planarCollisionIdempotent F M.keller = 0 :=
    planarCollisionIdempotent_eq_zero_of_branchPurity
      hPurity hFiniteEtaleRigidity M hNoHidden
  simp [hq, CorrespondenceRealization.realizedOperator]

variable {Z : Type z} [CommRing Z]
variable {ι : Type t}

/--
Chow/Hodge-style form of the locally copied purity spine.  The planar
idempotent gives a bigraded Chow projector, and the purity route identifies
its cohomological action with zero.
-/
theorem planarBigradedChowProjector_of_branchPurity
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram)
    (ρ :
      BigradedChowCorrespondenceRealization
        (CollisionRing F) Z K V ι) :
    ρ.toBigradedCorrespondenceRealization.IsBigradedRealizedProjector
        (planarCollisionIdempotent F M.keller) ∧
      (ρ.toBigradedCorrespondenceRealization).toCorrespondenceRealization.realizedOperator
          (planarCollisionIdempotent F M.keller) = 0 := by
  constructor
  · exact
      ρ.isBigradedChowProjector
        (planarCollisionIdempotent_isProjector
          F M.keller).1
  · exact
      planarRealizedProjector_eq_zero_of_branchPurity
        hPurity hFiniteEtaleRigidity M hNoHidden
        (ρ.toBigradedCorrespondenceRealization).toCorrespondenceRealization

/--
User-facing wrapper using the locally copied standard-geometry assumptions.

`#print axioms` exposes branch purity and finite-étale rigidity through
`HodgeConjecture.Planar.ExternalAssumptions`.
-/
theorem planarBigradedChowProjector_assuming_standardGeometry
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram)
    (ρ :
      BigradedChowCorrespondenceRealization
        (CollisionRing F) Z K V ι) :
    ρ.toBigradedCorrespondenceRealization.IsBigradedRealizedProjector
        (planarCollisionIdempotent F M.keller) ∧
      (ρ.toBigradedCorrespondenceRealization).toCorrespondenceRealization.realizedOperator
          (planarCollisionIdempotent F M.keller) = 0 :=
  planarBigradedChowProjector_of_branchPurity
    ExternalAssumptions.branchPurityA2
    ExternalAssumptions.affinePlaneFiniteEtaleRigidity
    M hNoHidden ρ

end

end HodgeConjecture.Planar
