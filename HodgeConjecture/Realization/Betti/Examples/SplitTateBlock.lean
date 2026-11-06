module

public import HodgeConjecture.Realization.Betti.Examples.SplitCorrespondenceAction
public import HodgeConjecture.Realization.Betti.Examples.SplitHodgeStructure
public import HodgeConjecture.Realization.Chow.Examples.SplitTateBlock
public import HodgeConjecture.Realization.Chow.TateGraphProjector
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# The actual finite split Tate-augmented Betti block

The distinguished point of `Option I` supplies the degree-zero Tate line.
Restriction to this point and to the complementary split scheme gives the
decomposition of actual singular cohomology as `ℚ × Cohomology I`.
The block action is conjugation of the constructed geometric Betti action
by this fixed decomposition; it is not a separately postulated matrix action.
The geometric Chow graph and lower-left pullback then instantiate the
construction and detection interfaces, with the independently complexified
degree-zero Hodge structure supplying Hodge compatibility.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitBettiTateBlock

noncomputable section

open Classical SplitBetti

variable (I : Type) [Fintype I]

/-- The fixed decomposition into the distinguished point and its complement. -/
def blockCoordinates : Cohomology (Option I) ≃ₗ[ℚ] ℚ × Cohomology I :=
  (coordinates (Option I)).trans
    ((LinearEquiv.piOptionEquivProd ℚ).trans
      ((LinearEquiv.refl ℚ ℚ).prodCongr (coordinates I).symm))

@[simp]
theorem blockCoordinates_fst (h : Cohomology (Option I)) :
    (blockCoordinates I h).1 = coordinates (Option I) h none := rfl

/-- The second component is actual continuous restriction to the complement. -/
theorem blockCoordinates_snd (h : Cohomology (Option I)) :
    (blockCoordinates I h).2 = pullback (some : I → Option I) h := by
  apply (coordinates I).injective
  funext i
  simp only [blockCoordinates, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.apply_symm_apply, coordinates_pullback]
  rfl

@[simp]
theorem coordinates_blockCoordinates_snd (h : Cohomology (Option I)) (i : I) :
    coordinates I (blockCoordinates I h).2 i = coordinates (Option I) h (some i) := by
  rw [blockCoordinates_snd, coordinates_pullback]

@[simp]
theorem coordinates_blockCoordinates_symm_none (v : ℚ × Cohomology I) :
    coordinates (Option I) ((blockCoordinates I).symm v) none = v.1 := by
  exact congrArg Prod.fst ((blockCoordinates I).apply_symm_apply v)

@[simp]
theorem coordinates_blockCoordinates_symm_some (v : ℚ × Cohomology I) (i : I) :
    coordinates (Option I) ((blockCoordinates I).symm v) (some i) =
      coordinates I v.2 i := by
  have h := congrArg (fun w : ℚ × Cohomology I ↦ coordinates I w.2 i)
    ((blockCoordinates I).apply_symm_apply v)
  simpa only [blockCoordinates_snd, coordinates_pullback] using h

/-- Change coordinates on the already constructed Betti endomorphism algebra. -/
def coordinateChange :
    Module.End ℚ (Cohomology (Option I)) ≃ₐ[ℚ] Module.End ℚ (ℚ × Cohomology I) :=
  AlgEquiv.ofLinearEquiv (blockCoordinates I).conj
    (by exact (blockCoordinates I).conj_id)
    (fun c d ↦ (blockCoordinates I).conj_comp d c)

set_option synthInstance.maxHeartbeats 60000 in
/-- The actual Chow convolution algebra acts on the Tate-augmented block. -/
def realization : SplitChowCorrespondence.EndAlgebra ℂ (Option I) →ₐ[ℚ]
    Module.End ℚ (ℚ × Cohomology I) :=
  (coordinateChange I).toAlgHom.comp (SplitBetti.realization (Option I))

@[simp]
theorem realization_apply (c : SplitChowCorrespondence.EndAlgebra ℂ (Option I))
    (v : ℚ × Cohomology I) :
    realization I c v =
      blockCoordinates I (action c ((blockCoordinates I).symm v)) := rfl

def correspondenceAction :
    RationalCorrespondenceAction (SplitChowCorrespondence.EndAlgebra ℂ (Option I))
      (ℚ × Cohomology I) where
  action := realization I

variable [DecidableEq I]

/-- The computed coefficients of the geometric graph action. -/
theorem coordinates_action_encode (z : SplitZeroCycles.Chow ℂ I ℚ)
    (h : Cohomology (Option I)) (output : Option I) :
    coordinates (Option I) (action (SplitChowTateBlock.encode I z) h) output =
      output.elim 1 (SplitZeroCycles.chowCoordinates ℂ I ℚ z) *
        coordinates (Option I) h none := by
  rw [coordinates_action, ← SplitChowCorrespondence.matrixAlgEquiv_apply,
    SplitChowTateBlock.matrix_encode]
  simp [Matrix.mulVec, dotProduct]

/-- The Chow graph realizes the prescribed canonical Betti graph projector. -/
theorem realization_encode (z : SplitZeroCycles.Chow ℂ I ℚ) :
    realization I (SplitChowTateBlock.encode I z) =
      ClassGraphProjector.operator (cycleClass I z) := by
  apply LinearMap.ext
  intro v
  rw [realization_apply, ClassGraphProjector.operator_apply]
  apply Prod.ext
  · rw [blockCoordinates_fst, coordinates_action_encode]
    simp only [Option.elim_none, one_mul, coordinates_blockCoordinates_symm_none]
  · apply (coordinates I).injective
    funext i
    rw [coordinates_blockCoordinates_snd, coordinates_action_encode]
    simp only [Option.elim_some, coordinates_blockCoordinates_symm_none,
      map_smul, coordinates_cycleClass, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Evaluation on the Tate unit selects exactly the distinguished source column. -/
theorem coordinates_lowerLeftClass (c : SplitChowCorrespondence.EndAlgebra ℂ (Option I))
    (i : I) :
    coordinates I (ClassGraphProjector.lowerLeftClass (realization I c)) i =
      SplitChowCorrespondence.matrixAlgEquiv ℂ (Option I) c (some i) none := by
  change coordinates I (realization I c (1, 0)).2 i = _
  rw [realization_apply, coordinates_blockCoordinates_snd, coordinates_action,
    ← SplitChowCorrespondence.matrixAlgEquiv_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option,
    coordinates_blockCoordinates_symm_none, coordinates_blockCoordinates_symm_some,
    map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_one]

/-- The lower-left square is proved for every actual Chow correspondence. -/
theorem cycleClass_decode :
    (cycleClass I).toLinearMap.comp (SplitChowTateBlock.decode I) =
      ClassGraphProjector.lowerLeftClassLinear.comp (realization I).toLinearMap := by
  apply LinearMap.ext
  intro c
  apply (coordinates I).injective
  funext i
  change coordinates I (cycleClass I (SplitChowTateBlock.decode I c)) i =
    coordinates I (ClassGraphProjector.lowerLeftClass (realization I c)) i
  rw [coordinates_cycleClass, SplitChowTateBlock.coordinates_decode, coordinates_lowerLeftClass]

/-- The actual finite split degree-zero cycle-class model, whose Hodge
subspace was defined using complexification before the cycle-class map. -/
def hodgeModel :
    RationalHodgeCycleClassModel (SplitZeroCycles.Chow ℂ I ℚ) (Cohomology I) where
  hodgeClasses := SplitHodgeStructure.rationalHodgeClasses I
  cycleClass := (cycleClass I).toLinearMap
  cycleClass_lands := by
    intro h _
    exact SplitHodgeStructure.all_hodge I h

/-- Actual Chow pushforward supplies the graph construction interface. -/
def construction : ClassGraphProjectorConstruction (hodgeModel I) (correspondenceAction I) where
  encode := SplitChowTateBlock.encode I
  encode_isIdempotent := SplitChowTateBlock.encode_isIdempotent I
  encode_realizes := realization_encode I

/-- Actual lower-left Chow pullback supplies the detection interface. -/
def detection : ClassGraphProjectorDetection (hodgeModel I) (correspondenceAction I) where
  decode := SplitChowTateBlock.decode I
  cycleClass_decode := cycleClass_decode I

/-- A block map is Hodge precisely when its scalar extension preserves the
independent bigrading on the actual cohomology of the disjoint-union scheme. -/
def IsBlockHodgeMorphism (f : Module.End ℚ (ℚ × Cohomology I)) : Prop :=
  SplitHodgeStructure.IsHodgeMorphism ((coordinateChange I).symm f)

omit [DecidableEq I] in
/-- All rational block maps preserve the finite degree-zero type-`(0,0)`
structure, as follows from the complexified-bigrading calculation. -/
theorem all_isBlockHodgeMorphism (f : Module.End ℚ (ℚ × Cohomology I)) :
    IsBlockHodgeMorphism I f :=
  SplitHodgeStructure.all_isHodgeMorphism _

/-- The third generic interface is proved from the independent Hodge data. -/
def hodgeCompatibility :
    ClassGraphProjectorHodgeCompatibility (hodgeModel I) (IsBlockHodgeMorphism I) where
  graph_isHodge_iff α :=
    ⟨fun _ ↦ SplitHodgeStructure.all_hodge I α,
      fun _ ↦ all_isBlockHodgeMorphism I _⟩

omit [DecidableEq I] in
/-- Every rational degree-zero Hodge class has its constructed Chow representative. -/
theorem hodgeConjectureAt : RationalHodgeConjectureAt (hodgeModel I) := by
  intro α _
  exact ⟨(cycleClass I).symm α, (cycleClass I).apply_symm_apply α⟩

/-- A chosen Betti class has an explicit actual Chow graph-projector lift. -/
def graphProjectorLift (α : Cohomology I) :
    AlgebraicProjectorLift (correspondenceAction I) (ClassGraphProjector.operator α) where
  projector := SplitChowTateBlock.encode I ((cycleClass I).symm α)
  projector_isIdempotent := SplitChowTateBlock.encode_isIdempotent I _
  realizes := by
    change realization I _ = _
    rw [realization_encode, (cycleClass I).apply_symm_apply]

/-- The graph/Hodge equivalence now has constructed finite split inputs. -/
theorem hodgeConjectureAt_iff_hodgeMorphismLift :
    RationalHodgeConjectureAt (hodgeModel I) ↔
      EveryClassGraphHodgeMorphismHasAlgebraicLift
        (correspondenceAction I) (IsBlockHodgeMorphism I) :=
  rationalHodgeConjectureAt_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
    (construction I) (detection I) (hodgeCompatibility I)

/-- The Palomar equation-of-algebra-homomorphisms target is equivalent to
the actual finite split degree-zero cycle-class surjectivity statement. -/
theorem hodgeConjectureAt_iff_palomarTargetSquare :
    RationalHodgeConjectureAt (hodgeModel I) ↔
      EveryHodgeClassHasPalomarTargetSquare (hodgeModel I) (correspondenceAction I) :=
  rationalHodgeConjectureAt_iff_everyHodgeClassHasPalomarTargetSquare
    (construction I) (detection I)

/-- The finite split degree-zero target square exists for every Hodge class. -/
theorem everyHodgeClassHasPalomarTargetSquare :
    EveryHodgeClassHasPalomarTargetSquare (hodgeModel I) (correspondenceAction I) :=
  (hodgeConjectureAt_iff_palomarTargetSquare I).mp (hodgeConjectureAt I)

end

end HodgeConjecture.SplitBettiTateBlock
