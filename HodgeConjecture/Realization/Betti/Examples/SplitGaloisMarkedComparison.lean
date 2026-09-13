import HodgeConjecture.Correspondence.Examples.SplitGaloisSheets
import HodgeConjecture.Realization.Chow.Examples.SplitGaloisResidual
import HodgeConjecture.Realization.Chow.Examples.SplitChowDiagonal
import HodgeConjecture.Realization.Chow.MultiplicativeResidualRigidity
import HodgeConjecture.Realization.Betti.Examples.SplitChowShear

/-!
# The geometric marked-sheet residual/action comparison

For the homogeneous sheets of the constructed split finite-group torsor,
the augmentation ideal maps to actual Chow cycles on the complement of the
base sheet and then to actual singular cohomology. Diagonal pushforward
embeds the sheet algebra into Chow correspondences. An invertible Chow
shear changes from point coordinates to constant-marked coordinates.
The resulting algebra map sends the marked selector to an actual Chow
projector and its action square is proved, not supplied as an input.

The generated class is intrinsic to these marked sheets: minus the
fundamental class of the complement. Multiplicative residual rigidity
explains why this bijective multiplicative map does not vary that class.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitGaloisMarkedComparison

noncomputable section

open Classical CategoryTheory SplitBetti SplitGaloisResidual

variable {G : Type} [Group G] [Finite G] (D : Subgroup G)

local instance : Fintype (SplitGaloisResidual.Complement D) := Fintype.ofFinite (SplitGaloisResidual.Complement D)

/-- Reindex the actual homogeneous sheets by the distinguished point and complement. -/
def sheetReindex : GenericSheetAlgebra ℚ D →ₐ[ℚ] (Option (SplitGaloisResidual.Complement D) → ℚ) where
  toFun f := f ∘ sheetEquiv D
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The actual homogeneous sheet scheme in the fixed point-plus-complement presentation. -/
def sheetSchemeIso :
    SplitPointGeometry.scheme ℂ (Option (SplitGaloisResidual.Complement D)) ≅
      SplitPointGeometry.scheme ℂ (CollisionFoundations.GaloisSheets D) :=
  SplitPointGeometry.isoOfEquiv ℂ (sheetEquiv D)

/-- Residual realization first constructs Chow cycles and then takes their Betti classes. -/
def residualRealization : MarkedSheetProjector.Residual D →ₗ[ℚ] Cohomology (SplitGaloisResidual.Complement D) :=
  (cycleClass (SplitGaloisResidual.Complement D)).toLinearMap.comp (residualChow D)

@[simp]
theorem coordinates_residualRealization (x : MarkedSheetProjector.Residual D)
    (s : SplitGaloisResidual.Complement D) :
    coordinates (SplitGaloisResidual.Complement D) (residualRealization D x) s = x.val s.val := by
  change coordinates (SplitGaloisResidual.Complement D) (cycleClass (SplitGaloisResidual.Complement D) (residualChow D x)) s = _
  rw [coordinates_cycleClass, chowCoordinates_residualChow]

/-- The geometric residual realization is a linear equivalence, not a lossy projection. -/
def residualRealizationEquiv :
    MarkedSheetProjector.Residual D ≃ₗ[ℚ] Cohomology (SplitGaloisResidual.Complement D) :=
  (residualChowEquiv D).trans (cycleClass (SplitGaloisResidual.Complement D))

@[simp]
theorem residualRealizationEquiv_apply (x : MarkedSheetProjector.Residual D) :
    residualRealizationEquiv D x = residualRealization D x := rfl

theorem residualRealization_surjective : Function.Surjective (residualRealization D) :=
  (residualRealizationEquiv D).surjective

/-- Multiplication in the residual ideal agrees with geometric intersection
followed by the singular cup product, not with ambient Chow convolution. -/
theorem residualRealization_mul (x y : MarkedSheetProjector.Residual D) :
    residualRealization D (x * y) = residualRealization D x * residualRealization D y := by
  change cycleClass (SplitGaloisResidual.Complement D) (residualChow D (x * y)) = _
  rw [residualChow_mul, cycleClass_intersection]
  rfl

/-- The marked Chow class is an output of the actual residual construction. -/
def generatedChowClass : SplitZeroCycles.Chow ℂ (SplitGaloisResidual.Complement D) ℚ :=
  residualChow D (MarkedSheetProjector.residualClass D)

theorem generatedChowClass_eq_neg_fundamental : generatedChowClass D = -fundamentalClass D :=
  residualChow_residualClass D

/-- The corresponding actual Betti class, determined by the marked sheets. -/
def generatedClass : Cohomology (SplitGaloisResidual.Complement D) :=
  residualRealization D (MarkedSheetProjector.residualClass D)

@[simp]
theorem cycleClass_generatedChowClass :
    cycleClass (SplitGaloisResidual.Complement D) (generatedChowClass D) = generatedClass D := rfl

@[simp]
theorem coordinates_generatedClass (s : SplitGaloisResidual.Complement D) :
    coordinates (SplitGaloisResidual.Complement D) (generatedClass D) s = -1 := by
  rw [generatedClass, coordinates_residualRealization]
  exact residualCoordinates_residualClass D s

/-- Here minus the fundamental class is minus the cup-product unit.
The general nonunital multiplicative rigidity theorem also forces this value. -/
theorem generatedClass_eq_neg_one : generatedClass D = -1 :=
  (MarkedSheetProjector.markedAugmentedAlgebra D).generatedClass_eq_neg_one_of_surjective
    (residualRealization D) (residualRealization_mul D) (residualRealization_surjective D)

/-- A sheet function gives its actual point-sum Chow class and then its
singular cohomology class on the full sheet scheme. -/
def sheetCohomology : GenericSheetAlgebra ℚ D →ₗ[ℚ] Cohomology (Option (SplitGaloisResidual.Complement D)) :=
  (cycleClass (Option (SplitGaloisResidual.Complement D))).toLinearMap.comp
    ((SplitZeroCycles.classMap ℂ (Option (SplitGaloisResidual.Complement D)) ℚ).comp
      ((SplitChowDiagonal.cyclesOfFunction ℂ (Option (SplitGaloisResidual.Complement D))).comp
        (sheetReindex D).toLinearMap))

@[simp]
theorem coordinates_sheetCohomology (f : GenericSheetAlgebra ℚ D)
    (s : Option (SplitGaloisResidual.Complement D)) :
    coordinates (Option (SplitGaloisResidual.Complement D)) (sheetCohomology D f) s = f (sheetEquiv D s) := by
  change coordinates (Option (SplitGaloisResidual.Complement D))
    (cycleClass (Option (SplitGaloisResidual.Complement D))
      (SplitZeroCycles.classMap ℂ (Option (SplitGaloisResidual.Complement D)) ℚ
        (SplitChowDiagonal.cyclesOfFunction ℂ (Option (SplitGaloisResidual.Complement D)) (sheetReindex D f)))) s = _
  rw [coordinates_cycleClass, SplitZeroCycles.chowCoordinates_classMap,
    SplitChowDiagonal.coordinates_cyclesOfFunction]
  rfl

/-- The actual residual realization applied to the existing constant-marked decomposition. -/
def sourceToBlock : GenericSheetAlgebra ℚ D →ₗ[ℚ] ℚ × Cohomology (SplitGaloisResidual.Complement D) :=
  ((MarkedSheetProjector.markedAugmentedAlgebra D).productRealization
    (residualRealization D)).comp
      (MarkedSheetProjector.markedAugmentedAlgebra D).decomposition.toLinearMap

@[simp]
theorem sourceToBlock_fst (f : GenericSheetAlgebra ℚ D) :
    (sourceToBlock D f).1 = f (baseSheet D) := rfl

theorem coordinates_sourceToBlock_snd (f : GenericSheetAlgebra ℚ D) (s : SplitGaloisResidual.Complement D) :
    coordinates (SplitGaloisResidual.Complement D) (sourceToBlock D f).2 s = f s.val - f (baseSheet D) := by
  change coordinates (SplitGaloisResidual.Complement D)
    (residualRealization D ((MarkedSheetProjector.markedAugmentedAlgebra D).decomposition f).2) s = _
  rw [coordinates_residualRealization]
  change f s.val - f (baseSheet D) • (1 : ℚ) = _
  simp only [smul_eq_mul, mul_one]

/-- Constant-marked coordinates are exactly the shear of the actual Betti
class of the sheet cycle, with the class fixed by the marked residual. -/
theorem sourceToBlock_eq_shear (f : GenericSheetAlgebra ℚ D) :
    sourceToBlock D f = ClassGraphProjector.shear (generatedClass D)
      (SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D) (sheetCohomology D f)) := by
  apply Prod.ext
  · change f (baseSheet D) =
      coordinates (Option (SplitGaloisResidual.Complement D)) (sheetCohomology D f) none
    rw [coordinates_sheetCohomology, sheetEquiv_none]
  · apply (coordinates (SplitGaloisResidual.Complement D)).injective
    funext s
    change coordinates (SplitGaloisResidual.Complement D) (sourceToBlock D f).2 s =
      coordinates (SplitGaloisResidual.Complement D)
        ((SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D) (sheetCohomology D f)).2 +
          (SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D) (sheetCohomology D f)).1 •
            generatedClass D) s
    rw [coordinates_sourceToBlock_snd, map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      SplitBettiTateBlock.coordinates_blockCoordinates_snd,
      SplitBettiTateBlock.blockCoordinates_fst, coordinates_sheetCohomology,
      sheetEquiv_none, sheetEquiv_some, coordinates_generatedClass, mul_neg_one, sub_eq_add_neg]

/-- The same coordinate change is realized by the actual invertible Chow shear. -/
theorem sourceToBlock_eq_realization_shear (f : GenericSheetAlgebra ℚ D) :
    sourceToBlock D f =
      SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)
        (SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D))
          (SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D) (sheetCohomology D f)) := by
  rw [SplitBettiTateBlock.realization_shear, cycleClass_generatedChowClass]
  exact sourceToBlock_eq_shear D f

/-- The injective sheet-to-Chow algebra map, followed by the actual Chow
coordinate shear. No algebra map in the opposite direction is required. -/
def markedEmbedding : GenericSheetAlgebra ℚ D →ₐ[ℚ]
    SplitChowCorrespondence.EndAlgebra ℂ (Option (SplitGaloisResidual.Complement D)) :=
  (SplitChowShear.conjugation (SplitGaloisResidual.Complement D) (generatedChowClass D)).toAlgHom.comp
    ((SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))).comp (sheetReindex D))

theorem markedEmbedding_injective : Function.Injective (markedEmbedding D) := by
  intro f g h
  have hdiag := (SplitChowShear.conjugation (SplitGaloisResidual.Complement D) (generatedChowClass D)).injective h
  have hfun := SplitChowDiagonal.diagonalAlgHom_injective ℂ (Option (SplitGaloisResidual.Complement D)) hdiag
  funext s
  obtain ⟨a, rfl⟩ := (sheetEquiv D).surjective s
  exact congrFun hfun a

omit [Finite G] in
theorem sheetReindex_selector :
    sheetReindex D (MarkedSheetProjector.selector D) = Pi.single none 1 := by
  funext s
  cases s with
  | none => simp [sheetReindex, MarkedSheetProjector.selector, genericSheetSelector]
  | some s =>
    simp [sheetReindex, MarkedSheetProjector.selector, genericSheetSelector, s.property]

/-- The marked selector enters the actual Chow algebra through the constructed algebra map. -/
def markedProjector : SplitChowCorrespondence.EndAlgebra ℂ (Option (SplitGaloisResidual.Complement D)) :=
  markedEmbedding D (MarkedSheetProjector.selector D)

theorem markedProjector_eq_encode :
    markedProjector D = SplitChowTateBlock.encode (SplitGaloisResidual.Complement D) (generatedChowClass D) := by
  change SplitChowShear.conjugation (SplitGaloisResidual.Complement D) (generatedChowClass D)
    (SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))
      (sheetReindex D (MarkedSheetProjector.selector D))) = _
  rw [sheetReindex_selector, SplitChowDiagonal.diagonalAlgHom_single]
  exact SplitChowShear.conjugation_pointProjector (SplitGaloisResidual.Complement D) (generatedChowClass D)

theorem markedProjector_isIdempotent : IsIdempotentElem (markedProjector D) :=
  (MarkedSheetProjector.markedAugmentedAlgebra D).selector_isIdempotent.map (markedEmbedding D)

theorem markedProjector_realizes :
    SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D) (markedProjector D) =
      ClassGraphProjector.operator (generatedClass D) := by
  rw [markedProjector_eq_encode, SplitBettiTateBlock.realization_encode,
    cycleClass_generatedChowClass]

/-- The canonical marked comparison has a geometrically constructed residual
map and a proved action square for the actual Chow projector. -/
def comparison :
    MarkedProjectorActionComparison (MarkedSheetProjector.markedAugmentedAlgebra D)
      (SplitBettiTateBlock.correspondenceAction (SplitGaloisResidual.Complement D)) (markedProjector D) where
  residualRealization := residualRealization D
  action_intertwines := by
    change (SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D) (markedProjector D)).comp _ = _
    rw [markedProjector_realizes]
    exact ((MarkedSheetProjector.markedAugmentedAlgebra D).productRealization_intertwines_selectorMultiplication
      (residualRealization D)).symm

/-- Lower-left detection recovers the actual residual Chow class. -/
theorem detectedClass :
    SplitChowTateBlock.decode (SplitGaloisResidual.Complement D) (markedProjector D) = generatedChowClass D := by
  rw [markedProjector_eq_encode, SplitChowTateBlock.decode_encode]

def projectorLift :
    AlgebraicProjectorLift (SplitBettiTateBlock.correspondenceAction (SplitGaloisResidual.Complement D))
      (ClassGraphProjector.operator (generatedClass D)) :=
  (comparison D).toAlgebraicProjectorLift
    (markedProjector_isIdempotent D) (residualRealization_surjective D)

set_option synthInstance.maxHeartbeats 60000 in
/-- The actual marked-sheet construction satisfies the universal algebra-hom square. -/
theorem palomarTargetSquare :
    (SplitBettiTateBlock.correspondenceAction (SplitGaloisResidual.Complement D)).action.comp
      (UniversalIdempotentAlgebra.mapOfIdempotent
        (markedProjector D) (markedProjector_isIdempotent D)) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator (generatedClass D))
        (ClassGraphProjector.operator_isIdempotent (generatedClass D)) :=
  (comparison D).action_comp_idempotentMap_eq_classGraph
    (markedProjector_isIdempotent D) (residualRealization_surjective D)

end

end HodgeConjecture.SplitGaloisMarkedComparison
