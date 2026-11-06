module

public import HodgeConjecture.Realization.Betti.Examples.SplitCycleClass
public import HodgeConjecture.Correspondence.ProjectorLift

@[expose] public section

/-!
# Geometric correspondence action on finite split Betti cohomology

The action is defined by continuous pullback, the singular degree-zero cup
product, and actual-fiber transfer. The cycle-class comparison intertwines
this action with the constructed Chow action. Its matrix formula and algebra
homomorphism laws are consequences of that geometric comparison.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitBetti

noncomputable section

open Classical

variable {I J L : Type} [Finite I] [Finite J] [Finite L]

/-- The Betti action is pullback, cup product with the cycle class, and
transfer along the other actual complex-point projection. -/
def action [Fintype I] [Fintype J]
    (c : SplitChowCorrespondence.Correspondence ℂ I J) (h : Cohomology I) : Cohomology J :=
  pushforward (Prod.snd : I × J → J)
    (cycleClass (I × J) c * pullback (Prod.fst : I × J → I) h)

/-- Cycle classes intertwine the two geometrically constructed actions. -/
theorem cycleClass_action [Fintype I] [Fintype J]
    (c : SplitChowCorrespondence.Correspondence ℂ I J)
    (z : SplitZeroCycles.Chow ℂ I ℚ) :
    cycleClass J (SplitChowCorrespondence.action ℂ c z) = action c (cycleClass I z) := by
  simp only [SplitChowCorrespondence.action, cycleClass_pushforward,
    cycleClass_intersection, cycleClass_pullback, action]

/-- The actual cohomological action has the same matrix coefficients as
geometric Chow convolution, with rows indexing outputs. -/
theorem coordinates_action [Fintype I] [Fintype J]
    (c : SplitChowCorrespondence.Correspondence ℂ I J) (h : Cohomology I) :
    coordinates J (action c h) =
      (SplitChowCorrespondence.matrixCoordinates ℂ I J c).mulVec (coordinates I h) := by
  obtain ⟨z, rfl⟩ := (cycleClass I).surjective h
  rw [← cycleClass_action, coordinates_cycleClass,
    SplitChowCorrespondence.chowCoordinates_action, coordinates_cycleClass]

/-- Geometric Chow convolution realizes as composition on singular cohomology. -/
theorem action_comp [Fintype I] [Fintype J] [Fintype L]
    (b : SplitChowCorrespondence.Correspondence ℂ J L)
    (a : SplitChowCorrespondence.Correspondence ℂ I J) (h : Cohomology I) :
    action (SplitChowCorrespondence.comp ℂ b a) h = action b (action a h) := by
  apply (coordinates L).injective
  simp only [coordinates_action, SplitChowCorrespondence.matrixCoordinates_comp,
    Matrix.mulVec_mulVec]

@[simp]
theorem diagonal_action [Fintype I] (h : Cohomology I) :
    action (SplitChowCorrespondence.diagonal ℂ) h = h := by
  apply (coordinates I).injective
  simp [coordinates_action]

/-- For a fixed correspondence, the geometric Betti action is rational linear. -/
def actionLinear [Fintype I] [Fintype J]
    (c : SplitChowCorrespondence.Correspondence ℂ I J) : Cohomology I →ₗ[ℚ] Cohomology J where
  toFun := action c
  map_add' h k := by
    apply (coordinates J).injective
    simp only [coordinates_action, map_add, Matrix.mulVec_add]
  map_smul' r h := by
    apply (coordinates J).injective
    simp only [coordinates_action, map_smul, RingHom.id_apply, Matrix.mulVec_smul]

variable (I) [Fintype I]

/-- The action also depends rational linearly on the actual Chow correspondence. -/
def linearRepresentation :
    SplitChowCorrespondence.EndAlgebra ℂ I →ₗ[ℚ] Module.End ℚ (Cohomology I) where
  toFun := actionLinear
  map_add' c d := by
    apply LinearMap.ext
    intro h
    apply (coordinates I).injective
    change coordinates I (action (c + d) h) =
      coordinates I (action c h + action d h)
    simp only [coordinates_action, map_add, Matrix.add_mulVec]
  map_smul' r c := by
    apply LinearMap.ext
    intro h
    apply (coordinates I).injective
    change coordinates I (action (r • c) h) = coordinates I (r • action c h)
    simp only [coordinates_action, map_smul, Matrix.smul_mulVec]

/-- The constructed Betti realization is an algebra homomorphism from the
actual Chow convolution algebra to actual singular-cohomology endomorphisms. -/
def realization :
    SplitChowCorrespondence.EndAlgebra ℂ I →ₐ[ℚ] Module.End ℚ (Cohomology I) :=
  AlgHom.ofLinearMap (linearRepresentation I)
    (by apply LinearMap.ext; intro h; exact diagonal_action h)
    (by intro a b; apply LinearMap.ext; intro h; exact action_comp a b h)

@[simp]
theorem realization_apply (c : SplitChowCorrespondence.EndAlgebra ℂ I) (h : Cohomology I) :
    realization I c h = action c h := rfl

/-- The cycle-class square for the complete Chow algebra action. -/
theorem realization_cycleClass (c : SplitChowCorrespondence.EndAlgebra ℂ I)
    (z : SplitZeroCycles.Chow ℂ I ℚ) :
    realization I c (cycleClass I z) =
      cycleClass I (SplitChowCorrespondence.action ℂ c z) :=
  (cycleClass_action c z).symm

/-- The existing projector-realization interface is instantiated with the
constructed Betti cohomology and geometric action. -/
def correspondenceAction :
    RationalCorrespondenceAction (SplitChowCorrespondence.EndAlgebra ℂ I) (Cohomology I) where
  action := realization I

end

end HodgeConjecture.SplitBetti
