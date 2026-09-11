import HodgeConjecture.Boundary.GaloisProjectorExtension
import HodgeConjecture.Realization.Chow.GaloisMarkedBlock

/-!
# Realizing a marked Galois selector as a Tate graph projector

This file isolates the conditional comparison between a compactified
correspondence projector extending the generic base-sheet selector and the
Tate graph projector of a cohomology class.  The generic sheet algebra is
commutative, while the compactified correspondence algebra `Γ` may be
noncommutative.  `AlgebraProjectorExtension` keeps those two roles separate:
its restriction map points from `Γ` to the generic sheet algebra, and its
chosen compactified projectors are idempotents in `Γ`.

A `MarkedGaloisSelectorComparison` supplies a rational realization `θ` of the
residual sheet module, identifies `θ(q - 1)` with the class `alpha`, and
records the square comparing the compactified projector action with generic
selector multiplication.  This square is equivalently a morphism of
representations of the universal one-idempotent algebra `ℚ × ℚ`; no algebra
map from the whole pointwise sheet algebra to the group/convolution algebra
is asserted.  Evaluating the square on `(1, 0)` already identifies the
lower-left class and therefore suffices for Chow detection.  If `θ` is
additionally surjective, cancellation identifies the entire action with the
canonical Tate graph projector, gives an algebraic projector lift, and proves
the Palomar-facing equality of the two universal algebra-homomorphism
composites.

The class-dependent coverage predicate below fixes only the ambient algebra
`Γ` and its action.  For each Hodge class its witness may choose a new finite group,
subgroup, extension package, extension element, residual realization, and
comparison.  The witness is universe-bounded: for fixed levels `u` and `b`,
it ranges over `G : Type u` and extension types in `Type b`.  This is the
usual predicative Lean encoding, not quantification over every universe at
once.

No actual finite cover or normal-closure datum is bundled into the witness,
and no geometric comparison, residual realization, or coverage instance is
constructed here.  Thus these are conditional endpoints rather than a proof
of a Hodge case.  The separately named strong replacement predicate is an
additional geometric hypothesis, not a consequence of the Hodge conjecture
or of selector idempotence.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u w c a b

variable {G : Type u} [Group G]
variable {D : Subgroup G}
variable {Γ : Type a} [Ring Γ] [Algebra ℚ Γ]
variable {H : Type w} [AddCommGroup H] [Module ℚ H]
variable
  {rho : RationalCorrespondenceAction Γ (ℚ × H)}
variable
  {E :
    AlgebraProjectorExtension
      (GenericSheetAlgebra ℚ D) Γ
      (MarkedSheetProjector.selector D)}
variable {x : E.Extension}
variable {alpha : H}

/--
The missing realization square for a chosen compactified extension of the
marked generic-sheet selector.

The residual map sends the canonical residual class `q - 1` to `alpha`.
The final field is the substantive geometric comparison; it must not be
constructed from an algebraic representative of `alpha` or from the desired
graph-projector equality.  Surjectivity is intentionally not part of this
structure: lower-left detection does not need it, while the stronger equality
of whole operators accepts it as a separate hypothesis.
-/
structure MarkedGaloisSelectorComparison
    (rho : RationalCorrespondenceAction Γ (ℚ × H))
    (E :
      AlgebraProjectorExtension
        (GenericSheetAlgebra ℚ D) Γ
        (MarkedSheetProjector.selector D))
    (x : E.Extension)
    (alpha : H) where
  residualRealization :
    MarkedSheetProjector.Residual D →ₗ[ℚ] H
  residualClass_eq :
    residualRealization
        (MarkedSheetProjector.residualClass D) =
      alpha
  action_intertwines :
    (rho.action (E.projector x)).comp
        (MarkedSheetProjector.productRealization
          D residualRealization) =
      (MarkedSheetProjector.productRealization
          D residualRealization).comp
        ((MarkedSheetProjector.decomposition D).conj
          (MarkedSheetProjector.multiplication D))

namespace MarkedGaloisSelectorComparison

/-- Forgetting the prescribed target class turns a Galois-sheet comparison
into the alpha-free comparison for its marked augmented source algebra.  The
equation with `alpha` remains separate as `residualClass_eq`. -/
def toMarkedSelectorActionComparison
    (B : MarkedGaloisSelectorComparison rho E x alpha) :
    MarkedSelectorActionComparison
      (MarkedSheetProjector.markedAugmentedAlgebra D) rho E x where
  residualRealization := B.residualRealization
  action_intertwines := by
    simpa only [
      MarkedSheetProjector.markedAugmentedAlgebra_decomposition,
      MarkedSheetProjector.markedAugmentedAlgebra_multiplication] using
        B.action_intertwines

@[simp]
theorem toMarkedSelectorActionComparison_residualRealization
    (B : MarkedGaloisSelectorComparison rho E x alpha) :
    B.toMarkedSelectorActionComparison.residualRealization =
      B.residualRealization :=
  rfl

/-- The alpha-free comparison generates the prescribed class from the marked
residual element. -/
theorem generatedClass_eq
    (B : MarkedGaloisSelectorComparison rho E x alpha) :
    (MarkedSheetProjector.markedAugmentedAlgebra D).generatedClass
        B.residualRealization =
      alpha := by
  rw [MarkedAugmentedAlgebra.generatedClass,
    MarkedSheetProjector.markedAugmentedAlgebra_residualClass]
  exact B.residualClass_eq

/--
Evaluating the comparison square at the marked unit detects the lower-left
class of the compactified selector action.  No surjectivity is required.
-/
theorem lowerLeftClass_action_eq
    (B : MarkedGaloisSelectorComparison rho E x alpha) :
    ClassGraphProjector.lowerLeftClass
        (rho.action (E.projector x)) =
      alpha := by
  calc
    ClassGraphProjector.lowerLeftClass
          (rho.action (E.projector x)) =
      (MarkedSheetProjector.markedAugmentedAlgebra D).generatedClass
          B.residualRealization :=
      B.toMarkedSelectorActionComparison.lowerLeftClass_action_eq_generatedClass
    _ = alpha := B.generatedClass_eq

/--
Surjective cancellation against the residual product realization identifies
the whole compactified selector action with the canonical graph projector.
-/
theorem realizes
    (B : MarkedGaloisSelectorComparison rho E x alpha)
    (hSurjective : Function.Surjective B.residualRealization) :
    rho.action (E.projector x) =
      ClassGraphProjector.operator alpha := by
  simpa only [toMarkedSelectorActionComparison_residualRealization,
    B.generatedClass_eq] using
    B.toMarkedSelectorActionComparison.realizes hSurjective

/--
Under surjectivity, the chosen compactified selector is an algebraic lift of
the generated graph projector.
-/
def toAlgebraicProjectorLift
    (B : MarkedGaloisSelectorComparison rho E x alpha)
    (hSurjective : Function.Surjective B.residualRealization) :
    AlgebraicProjectorLift rho
      (ClassGraphProjector.operator alpha) := by
  rw [← B.generatedClass_eq]
  exact
    B.toMarkedSelectorActionComparison.toAlgebraicProjectorLift
      hSurjective

/-- The comparison as a morphism of representations of the universal
one-idempotent algebra.  The full law is equivalent to the stored selector
square and therefore adds no hypothesis. -/
noncomputable def toIdempotentRepresentationMorphism
    (B : MarkedGaloisSelectorComparison rho E x alpha) :=
  B.toMarkedSelectorActionComparison.toIdempotentRepresentationMorphism

/-- Palomar-facing target square.  Under surjectivity, the correspondence
action after the compactified one-idempotent presentation is exactly the
canonical presentation of the class graph projector `P_alpha`. -/
theorem palomarTargetSquare
    (B : MarkedGaloisSelectorComparison rho E x alpha)
    (hSurjective : Function.Surjective B.residualRealization) :
    rho.action.comp (E.compactifiedIdempotentMap x) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator alpha)
        (ClassGraphProjector.operator_isIdempotent alpha) := by
  simpa only [toMarkedSelectorActionComparison_residualRealization,
    B.generatedClass_eq] using
    MarkedSelectorActionComparison.action_comp_compactifiedIdempotentMap_eq_classGraph
        B.toMarkedSelectorActionComparison hSurjective

/--
Ambient lower-left Chow-block detection turns a marked-selector comparison
into an algebraic representative.  This pointwise result only evaluates the
comparison square at `(1, 0)` and therefore does not require surjectivity.
-/
theorem isAlgebraicHodgeClass_of_comparison
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    {M : RationalHodgeCycleClassModel Chow H}
    (detect : ClassGraphProjectorDetection M rho)
    (B : MarkedGaloisSelectorComparison rho E x alpha) :
    IsAlgebraicHodgeClass M alpha := by
  refine ⟨detect.decode (E.projector x), ?_⟩
  have hDecode :=
    LinearMap.congr_fun detect.cycleClass_decode (E.projector x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] at hDecode
  calc
    M.cycleClass (detect.decode (E.projector x)) =
        ClassGraphProjector.lowerLeftClassLinear
          (rho.action (E.projector x)) := hDecode
    _ = ClassGraphProjector.lowerLeftClass
          (rho.action (E.projector x)) := rfl
    _ = alpha := B.lowerLeftClass_action_eq

end MarkedGaloisSelectorComparison

/--
A class-dependent marked-selector witness inside a fixed ambient
correspondence action.

The finite group `G`, subgroup `D`, extension package `E`, chosen extension, and
comparison are all fields of the witness and hence may vary with `alpha`.
The levels `u` and `b` bound the universes of `G` and `E.Extension`,
respectively.  This package records only sheet-indexing and abstract extension
algebra; it contains neither a finite cover nor a normal-closure datum.
-/
structure ClassDependentMarkedGaloisSelectorWitness
    (rho : RationalCorrespondenceAction Γ (ℚ × H))
    (alpha : H) where
  G : Type u
  [groupG : Group G]
  [finiteG : Finite G]
  D : Subgroup G
  extensionData :
    AlgebraProjectorExtension.{u, a, b}
      (GenericSheetAlgebra ℚ D) Γ
      (MarkedSheetProjector.selector D)
  extension : extensionData.Extension
  comparison :
    MarkedGaloisSelectorComparison
      rho extensionData extension alpha
  residualRealization_surjective :
    Function.Surjective comparison.residualRealization

namespace ClassDependentMarkedGaloisSelectorWitness

/-- A class-dependent witness supplies a graph-projector lift in `Γ`. -/
def toAlgebraicProjectorLift
    (W : ClassDependentMarkedGaloisSelectorWitness.{u, w, a, b}
      rho alpha) :
    AlgebraicProjectorLift rho
      (ClassGraphProjector.operator alpha) := by
  letI := W.groupG
  exact W.comparison.toAlgebraicProjectorLift
    W.residualRealization_surjective

end ClassDependentMarkedGaloisSelectorWitness

/--
Every rational Hodge class has some marked-selector witness in the fixed
ambient correspondence algebra.  Only `Γ` and `rho` are fixed; all extension
and sheet data may depend on the class.

The universe parameters bound the witness types (`G : Type u` and
`E.Extension : Type b`).  No inhabitant is constructed in this file.
-/
def ClassDependentMarkedGaloisSelectorCoverage
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    (M : RationalHodgeCycleClassModel Chow H)
    (rho : RationalCorrespondenceAction Γ (ℚ × H)) : Prop :=
  ∀ alpha : H, IsRationalHodgeClass M alpha →
    Nonempty
      (ClassDependentMarkedGaloisSelectorWitness.{u, w, a, b}
        rho alpha)

/-- Class-dependent marked-selector coverage gives all graph-projector lifts. -/
theorem everyHodgeClassHasGraphProjectorLift_of_classDependentMarkedGaloisSelectorCoverage
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    {M : RationalHodgeCycleClassModel Chow H}
    (coverage :
      ClassDependentMarkedGaloisSelectorCoverage.{u, w, c, a, b}
        M rho) :
    EveryHodgeClassHasGraphProjectorLift M rho := by
  intro alpha hAlpha
  obtain ⟨W⟩ := coverage alpha hAlpha
  exact ⟨W.toAlgebraicProjectorLift⟩

/--
Class-dependent marked-selector coverage proves the modeled rational Hodge
target once the fixed ambient correspondence action has lower-left Chow
detection.
-/
theorem rationalHodgeConjectureAt_of_classDependentMarkedGaloisSelectorCoverage
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    {M : RationalHodgeCycleClassModel Chow H}
    (detect : ClassGraphProjectorDetection M rho)
    (coverage :
      ClassDependentMarkedGaloisSelectorCoverage.{u, w, c, a, b}
        M rho) :
    RationalHodgeConjectureAt M :=
  rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
    detect
    (everyHodgeClassHasGraphProjectorLift_of_classDependentMarkedGaloisSelectorCoverage
      coverage)

/--
The strong assertion that existence of an ambient graph-projector lift can be
replaced by existence of some class-dependent marked-selector witness.

No replacement is constructed here.  This hypothesis is deliberately named
separately because an arbitrary algebraic lift does not formally determine a
group, subgroup, extension package, or residual realization.
-/
def StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector
    (target : H → Prop)
    (rho : RationalCorrespondenceAction Γ (ℚ × H)) : Prop :=
  ∀ alpha : H, target alpha →
    Nonempty
        (AlgebraicProjectorLift rho
          (ClassGraphProjector.operator alpha)) →
      Nonempty
        (ClassDependentMarkedGaloisSelectorWitness.{u, w, a, b}
          rho alpha)

/-- The strong replacement hypothesis converts arbitrary graph lifts into coverage. -/
theorem classDependentMarkedGaloisSelectorCoverage_of_everyHodgeClassHasGraphProjectorLift
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    {M : RationalHodgeCycleClassModel Chow H}
    (replacement :
      StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector.{u, w, a, b}
        (IsRationalHodgeClass M) rho)
    (h : EveryHodgeClassHasGraphProjectorLift M rho) :
    ClassDependentMarkedGaloisSelectorCoverage.{u, w, c, a, b}
      M rho := by
  intro alpha hAlpha
  exact replacement alpha hAlpha (h alpha hAlpha)

/--
Conditional reformulation of the modeled rational Hodge target by
class-dependent marked-selector coverage.  The forward direction uses the
explicitly named strong replacement hypothesis; the reverse direction uses
ambient lower-left Chow detection.
-/
theorem rationalHodgeConjectureAt_iff_classDependentMarkedGaloisSelectorCoverage
    {Chow : Type c}
    [AddCommGroup Chow] [Module ℚ Chow]
    {M : RationalHodgeCycleClassModel Chow H}
    (construct : ClassGraphProjectorConstruction M rho)
    (detect : ClassGraphProjectorDetection M rho)
    (replacement :
      StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector.{u, w, a, b}
        (IsRationalHodgeClass M) rho) :
    RationalHodgeConjectureAt M ↔
      ClassDependentMarkedGaloisSelectorCoverage.{u, w, c, a, b}
        M rho := by
  constructor
  · intro h
    apply
      classDependentMarkedGaloisSelectorCoverage_of_everyHodgeClassHasGraphProjectorLift
        replacement
    exact
      everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
        construct h
  · exact
      rationalHodgeConjectureAt_of_classDependentMarkedGaloisSelectorCoverage
        detect

end

end HodgeConjecture
