import HodgeConjecture.Realization.Chow.Model
import HodgeConjecture.Realization.HodgeClasses
import HodgeConjecture.LinearAlgebra.BlockGraphProjector
import HodgeConjecture.LinearAlgebra.UniversalIdempotentAlgebra

/-!
# Tate-block graph projectors and the Hodge target

This module gives a non-circular projector reformulation of the rational
Hodge conjecture stated in `Realization.HodgeClasses`.

For a rational Hodge class `α` in codimension `p`, consider the graph
projector

```text
             [ 1  0 ]
e_α(t, x) =  [ α  0 ] (t, x) = (t, t • α)
```

on the underlying rational module of
`ℚ(-p) ⊕ H^(2p)(X, ℚ)`.  The Tate twist is part of the intended Hodge
interpretation: in the cohomological convention used here, `ℚ(-p)` has Hodge
type `(p,p)` and weight `2p`.  This file records only the underlying rational
linear map.  The class is recovered by evaluating at `(1, 0)` and taking the
second component.

The Chow-level comparison is split into two independently auditable pieces.

* `ClassGraphProjectorConstruction` constructs the block correspondence
  `[[1, 0], [z, 0]]` from a Chow class and identifies its action.
* `ClassGraphProjectorDetection` extracts the lower-left Chow block of a
  correspondence and identifies its cycle class with the lower-left block of
  the cohomological action.

The forward and reverse implications use only the corresponding half.  With
both, the rational Hodge conjecture is equivalent to algebraic liftability of
every canonical graph projector.

For a genuine Hodge realization one must additionally prove that `α` is a
rational Hodge class exactly when `e_α` is a morphism of Hodge structures.
`ClassGraphProjectorHodgeCompatibility` names that comparison without
pretending that the present rational-module model already contains Hodge
structures.

These are substantive geometric interfaces for a full Tate-block Chow
correspondence algebra.  The repository's current arbitrary or
cover-generated compactified algebra does not yet instantiate them, nor does
the finite-cover branch show that it produces every canonical graph
projector.  A concrete motive-level construction must also choose covariant
or contravariant Chow motives and the corresponding convolution/opposite-
algebra convention.  It should use `End(ℚ(-p) ⊕ h(X))` and realization in
degree `2p`, without assuming an algebraic Künneth projector `h^(2p)(X)`.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w

namespace ClassGraphProjector

variable {H : Type v} [AddCommGroup H] [Module ℚ H]

/-- The linear map from the Tate line sending `t` to `t • α`. -/
abbrev lineMap (α : H) : ℚ →ₗ[ℚ] H :=
  BlockGraphProjector.lineMap (R := ℚ) α

/--
The graph projector of `α` on `ℚ × H`, representing the underlying rational
module of the Tate-block object `ℚ(-p) ⊕ H^(2p)(X, ℚ)`.
-/
abbrev operator (α : H) : Module.End ℚ (ℚ × H) :=
  BlockGraphProjector.operator (R := ℚ) α

@[simp]
theorem operator_apply (α : H) (t : ℚ) (x : H) :
    operator α (t, x) = (t, t • α) :=
  rfl

/-- Every class graph defines an idempotent endomorphism. -/
theorem operator_isIdempotent (α : H) :
    IsIdempotentElem (operator α) :=
  BlockGraphProjector.operator_isIdempotent (R := ℚ) α

/-- The standard projector onto the Tate factor in the fixed product
coordinates. -/
abbrev diagonalOperator : Module.End ℚ (ℚ × H) :=
  BlockGraphProjector.diagonalOperator (R := ℚ) (M := H)

@[simp]
theorem diagonalOperator_apply (t : ℚ) (x : H) :
    diagonalOperator (H := H) (t, x) = (t, 0) :=
  rfl

/-- The change of splitting which carries the standard Tate line to the
graph of `α`.  Its inverse is the same shear with `-α`. -/
abbrev shear (α : H) : (ℚ × H) ≃ₗ[ℚ] (ℚ × H) :=
  BlockGraphProjector.shear (R := ℚ) α

@[simp]
theorem shear_apply (α : H) (t : ℚ) (x : H) :
    shear α (t, x) = (t, x + t • α) :=
  rfl

@[simp]
theorem shear_symm_apply (α : H) (t : ℚ) (x : H) :
    (shear α).symm (t, x) = (t, x - t • α) :=
  rfl

/-- In coordinates adapted to the graph line, the class graph projector is
the standard block-diagonal projector. -/
theorem operator_eq_shear_diagonal_shear_symm (α : H) :
    operator α =
      (shear α).toLinearMap * diagonalOperator (H := H) *
        (shear α).symm.toLinearMap :=
  BlockGraphProjector.operator_eq_shear_diagonal_shear_symm (R := ℚ) α

/-- The reflection across the graph line of `α` along the second factor. -/
def reflection (α : H) : Module.End ℚ (ℚ × H) :=
  (2 : ℚ) • operator α - 1

@[simp]
theorem reflection_apply (α : H) (t : ℚ) (x : H) :
    reflection α (t, x) = (t, (2 * t) • α - x) := by
  apply Prod.ext
  · simp [reflection, operator]
    ring
  · simp [reflection, operator, mul_smul]

/-- The graph reflection is an involution. -/
theorem reflection_isInvolution (α : H) :
    reflection α * reflection α = 1 := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  simp [Module.End.mul_apply]

/-- The graph projector is the normalized average of the identity and its
associated involution.  This is the exact rational `C₂`-averaging identity;
constructing the involution geometrically is a separate problem. -/
theorem operator_eq_average_reflection (α : H) :
    operator α = (2 : ℚ)⁻¹ • (1 + reflection α) := by
  rw [reflection]
  module

/-- The graph projector as an independently specified cohomological target. -/
def projector (α : H) : RationalCohomologicalProjector (ℚ × H) where
  operator := operator α
  operator_isIdempotent := operator_isIdempotent α

@[simp]
theorem projector_operator (α : H) :
    (projector α).operator = operator α :=
  rfl

/-- Extract the lower-left class by evaluating at `(1, 0)`. -/
def lowerLeftClass (e : Module.End ℚ (ℚ × H)) : H :=
  (LinearMap.snd ℚ ℚ H) (e (1, 0))

/-- Linear form of lower-left class extraction. -/
def lowerLeftClassLinear :
    Module.End ℚ (ℚ × H) →ₗ[ℚ] H :=
  (LinearMap.snd ℚ ℚ H).comp
    ((LinearMap.applyₗ (R := ℚ) (M := ℚ × H) (M₂ := ℚ × H)) (1, 0))

@[simp]
theorem lowerLeftClassLinear_apply
    (e : Module.End ℚ (ℚ × H)) :
    lowerLeftClassLinear e = lowerLeftClass e :=
  rfl

@[simp]
theorem lowerLeftClass_operator (α : H) :
    lowerLeftClass (operator α) = α := by
  simp [lowerLeftClass]

/-- Equality of canonical graph projectors detects equality of their classes. -/
theorem operator_injective :
    Function.Injective (operator (H := H)) := by
  intro α β h
  rw [← lowerLeftClass_operator α, ← lowerLeftClass_operator β, h]

/-- Composition of two class-graph projectors retains the class of the
outer projector. -/
theorem operator_mul_operator (α β : H) :
    operator α * operator β = operator α := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  simp [Module.End.mul_apply]

/-- Two class-graph projectors commute exactly when they encode the same
class.  In particular, a commutative correspondence algebra cannot realize
distinct graph projectors through one fixed algebra action. -/
theorem operator_mul_comm_iff (α β : H) :
    operator α * operator β = operator β * operator α ↔
      α = β := by
  rw [operator_mul_operator, operator_mul_operator]
  exact operator_injective.eq_iff

end ClassGraphProjector

variable {Chow : Type u} {H : Type v} {Γ : Type w}
variable [AddCommGroup Chow] [Module ℚ Chow]
variable [AddCommGroup H] [Module ℚ H]
variable [Ring Γ] [Algebra ℚ Γ]

/--
Construction half of the Tate-block comparison: a Chow class supplies the
block correspondence `[[1, 0], [z, 0]]`, it is idempotent, and its action is
the graph projector of the cycle class of `z`.

The encoding is intentionally only a function.  Adjoining the diagonal `1`
makes the graph-projector construction affine rather than linear.
-/
structure ClassGraphProjectorConstruction
    (M : RationalHodgeCycleClassModel Chow H)
    (ρ : RationalCorrespondenceAction Γ (ℚ × H)) where
  encode : Chow → Γ
  encode_isIdempotent :
    ∀ z, IsIdempotentElem (encode z)
  encode_realizes :
    ∀ z,
      ρ.action (encode z) =
        ClassGraphProjector.operator (M.cycleClass z)

/--
Detection half of the Tate-block comparison: every correspondence has a
lower-left Chow block, and its cycle class agrees with the lower-left
component of the cohomological action.

This is expected for the full correspondence algebra of
`ℚ(-p) ⊕ h(X)`.  It is not automatic for an arbitrary or cover-generated
compactified algebra.
-/
structure ClassGraphProjectorDetection
    (M : RationalHodgeCycleClassModel Chow H)
    (ρ : RationalCorrespondenceAction Γ (ℚ × H)) where
  decode : Γ →ₗ[ℚ] Chow
  cycleClass_decode :
    M.cycleClass.comp decode =
      ClassGraphProjector.lowerLeftClassLinear.comp ρ.action.toLinearMap

/--
Compatibility between Hodge type and the canonical graph construction.

In a concrete Hodge realization, `IsHodgeMorphism e` should mean that `e` is
a morphism of rational Hodge structures.  The expected equivalence uses the
cohomological convention in which `ℚ(-p)` has type `(p,p)` and weight `2p`.
It is kept separate from Chow construction and detection.
-/
structure ClassGraphProjectorHodgeCompatibility
    (M : RationalHodgeCycleClassModel Chow H)
    (IsHodgeMorphism : Module.End ℚ (ℚ × H) → Prop) : Prop where
  graph_isHodge_iff :
    ∀ α : H,
      IsHodgeMorphism (ClassGraphProjector.operator α) ↔
        IsRationalHodgeClass M α

/-- Algebraicity of one class constructs a lift of its graph projector. -/
theorem graphProjectorLift_of_isAlgebraicHodgeClass
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (C : ClassGraphProjectorConstruction M ρ)
    {α : H} (hα : IsAlgebraicHodgeClass M α) :
    Nonempty
      (AlgebraicProjectorLift ρ
        (ClassGraphProjector.operator α)) := by
  obtain ⟨z, hz⟩ := hα
  refine ⟨{
    projector := C.encode z
    projector_isIdempotent := C.encode_isIdempotent z
    realizes := ?_
  }⟩
  rw [C.encode_realizes, hz]

/-- A lift of one graph projector detects an algebraic representative. -/
theorem isAlgebraicHodgeClass_of_graphProjectorLift
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (D : ClassGraphProjectorDetection M ρ)
    {α : H}
    (hα : Nonempty
      (AlgebraicProjectorLift ρ
        (ClassGraphProjector.operator α))) :
    IsAlgebraicHodgeClass M α := by
  obtain ⟨L⟩ := hα
  refine ⟨D.decode L.projector, ?_⟩
  have hDecode := LinearMap.congr_fun D.cycleClass_decode L.projector
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, L.realizes] at hDecode
  simpa using hDecode

/-- Pointwise equivalence between algebraic classes and graph-projector lifts. -/
theorem isAlgebraicHodgeClass_iff_graphProjectorLift
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (C : ClassGraphProjectorConstruction M ρ)
    (D : ClassGraphProjectorDetection M ρ)
    (α : H) :
    IsAlgebraicHodgeClass M α ↔
      Nonempty
        (AlgebraicProjectorLift ρ
          (ClassGraphProjector.operator α)) :=
  ⟨graphProjectorLift_of_isAlgebraicHodgeClass C,
    isAlgebraicHodgeClass_of_graphProjectorLift D⟩

/-- Every rational Hodge-class graph projector has an algebraic lift. -/
def EveryHodgeClassHasGraphProjectorLift
    (M : RationalHodgeCycleClassModel Chow H)
    (ρ : RationalCorrespondenceAction Γ (ℚ × H)) : Prop :=
  ∀ α : H, IsRationalHodgeClass M α →
    Nonempty
      (AlgebraicProjectorLift ρ
        (ClassGraphProjector.operator α))

/-- Every rational Hodge-class graph projector has an idempotent
correspondence whose universal one-idempotent presentation commutes with
realization.  This is the Palomar-style equation-of-composites form of
`EveryHodgeClassHasGraphProjectorLift`. -/
def EveryHodgeClassHasPalomarTargetSquare
    (M : RationalHodgeCycleClassModel Chow H)
    (ρ : RationalCorrespondenceAction Γ (ℚ × H)) : Prop :=
  ∀ α : H, IsRationalHodgeClass M α →
    ∃ projector : Γ,
      ∃ hProjector : IsIdempotentElem projector,
        ρ.action.comp
            (UniversalIdempotentAlgebra.mapOfIdempotent
              projector hProjector) =
          UniversalIdempotentAlgebra.mapOfIdempotent
            (ClassGraphProjector.operator α)
            (ClassGraphProjector.operator_isIdempotent α)

/-- The structure-valued lift target and the equality-of-algebra-homomorphism
target are pointwise equivalent. -/
theorem everyHodgeClassHasGraphProjectorLift_iff_palomarTargetSquare
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)} :
    EveryHodgeClassHasGraphProjectorLift M ρ ↔
      EveryHodgeClassHasPalomarTargetSquare M ρ := by
  constructor
  · intro h α hα
    exact
      (AlgebraicProjectorLift.nonempty_iff_exists_idempotentMap_square
        (ClassGraphProjector.operator_isIdempotent α)).mp
        (h α hα)
  · intro h α hα
    exact
      (AlgebraicProjectorLift.nonempty_iff_exists_idempotentMap_square
        (ClassGraphProjector.operator_isIdempotent α)).mpr
        (h α hα)

/--
Every canonical class graph that is a Hodge morphism has an algebraic lift.
Unlike `EveryHodgeClassHasGraphProjectorLift`, this formulation exposes the
Hodge-morphism predicate that a concrete realization must provide.
-/
def EveryClassGraphHodgeMorphismHasAlgebraicLift
    (ρ : RationalCorrespondenceAction Γ (ℚ × H))
    (IsHodgeMorphism : Module.End ℚ (ℚ × H) → Prop) : Prop :=
  ∀ α : H,
    IsHodgeMorphism (ClassGraphProjector.operator α) →
      Nonempty
        (AlgebraicProjectorLift ρ
          (ClassGraphProjector.operator α))

/-- Hodge compatibility identifies the two quantified projector targets. -/
theorem everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    {IsHodgeMorphism : Module.End ℚ (ℚ × H) → Prop}
    (K : ClassGraphProjectorHodgeCompatibility M IsHodgeMorphism) :
    EveryHodgeClassHasGraphProjectorLift M ρ ↔
      EveryClassGraphHodgeMorphismHasAlgebraicLift ρ IsHodgeMorphism := by
  constructor
  · intro h α hHodge
    exact h α ((K.graph_isHodge_iff α).mp hHodge)
  · intro h α hα
    exact h α ((K.graph_isHodge_iff α).mpr hα)

/--
The Chow-level graph construction sends algebraic Hodge classes to algebraic
lifts of their canonical graph projectors.
-/
theorem everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (C : ClassGraphProjectorConstruction M ρ)
    (h : RationalHodgeConjectureAt M) :
    EveryHodgeClassHasGraphProjectorLift M ρ := by
  intro α hα
  exact graphProjectorLift_of_isAlgebraicHodgeClass C (h hα)

/--
Lower-left Chow-block detection turns lifts of all canonical graph projectors
back into algebraic representatives of all rational Hodge classes.
-/
theorem rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (D : ClassGraphProjectorDetection M ρ)
    (h : EveryHodgeClassHasGraphProjectorLift M ρ) :
    RationalHodgeConjectureAt M := by
  intro α hα
  exact isAlgebraicHodgeClass_of_graphProjectorLift D (h α hα)

/--
Pointwise equivalence between the rational Hodge conjecture and canonical
graph-projector lifting, under the explicit construction and detection maps.
-/
theorem rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (C : ClassGraphProjectorConstruction M ρ)
    (D : ClassGraphProjectorDetection M ρ) :
    RationalHodgeConjectureAt M ↔
      EveryHodgeClassHasGraphProjectorLift M ρ :=
  ⟨everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt C,
    rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift D⟩

/-- Palomar-style target theorem: the modeled rational Hodge conjecture is
equivalent to producing, for every Hodge class, an idempotent correspondence
whose universal one-idempotent map commutes with cohomological realization. -/
theorem rationalHodgeConjectureAt_iff_everyHodgeClassHasPalomarTargetSquare
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    (C : ClassGraphProjectorConstruction M ρ)
    (D : ClassGraphProjectorDetection M ρ) :
    RationalHodgeConjectureAt M ↔
      EveryHodgeClassHasPalomarTargetSquare M ρ :=
  (rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift
    C D).trans
      everyHodgeClassHasGraphProjectorLift_iff_palomarTargetSquare

/--
Hodge-theoretic form of the graph-projector equivalence.  The extra
compatibility hypothesis is precisely the comparison between `(p,p)` classes
and morphisms from the Tate line; it is not hidden in the algebraic lift.
-/
theorem rationalHodgeConjectureAt_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
    {M : RationalHodgeCycleClassModel Chow H}
    {ρ : RationalCorrespondenceAction Γ (ℚ × H)}
    {IsHodgeMorphism : Module.End ℚ (ℚ × H) → Prop}
    (C : ClassGraphProjectorConstruction M ρ)
    (D : ClassGraphProjectorDetection M ρ)
    (K : ClassGraphProjectorHodgeCompatibility M IsHodgeMorphism) :
    RationalHodgeConjectureAt M ↔
      EveryClassGraphHodgeMorphismHasAlgebraicLift ρ IsHodgeMorphism :=
  (rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift C D).trans
    (everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms K)

section Graded

variable {ChowByCodim : ℕ → Type u}
variable {Cohomology : ℕ → Type v}
variable [∀ p, AddCommGroup (ChowByCodim p)]
variable [∀ p, Module ℚ (ChowByCodim p)]
variable [∀ n, AddCommGroup (Cohomology n)]
variable [∀ n, Module ℚ (Cohomology n)]

/--
Globally quantified form: with Tate-block construction and detection in every
codimension, the rational Hodge conjecture is equivalent to liftability of
every canonical graph projector.
-/
theorem rationalHodgeConjectureForModel_iff_everyHodgeClassHasGraphProjectorLift
    (M : ∀ p,
      RationalHodgeCycleClassModel
        (ChowByCodim p) (Cohomology (2 * p)))
    (ΓByCodim : ℕ → Type w)
    [∀ p, Ring (ΓByCodim p)] [∀ p, Algebra ℚ (ΓByCodim p)]
    (ρ : ∀ p,
      RationalCorrespondenceAction
        (ΓByCodim p) (ℚ × Cohomology (2 * p)))
    (C : ∀ p, ClassGraphProjectorConstruction (M p) (ρ p))
    (D : ∀ p, ClassGraphProjectorDetection (M p) (ρ p)) :
    RationalHodgeConjectureForModel M ↔
      ∀ p, EveryHodgeClassHasGraphProjectorLift (M p) (ρ p) := by
  constructor
  · intro h p
    exact
      everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
        (C p) (h p)
  · intro h p
    exact
      rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
        (D p) (h p)

/--
All-codimension form using an explicit Hodge-morphism predicate in each
degree of one modeled variety.
-/
theorem rationalHodgeConjectureForModel_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
    (M : ∀ p,
      RationalHodgeCycleClassModel
        (ChowByCodim p) (Cohomology (2 * p)))
    (ΓByCodim : ℕ → Type w)
    [∀ p, Ring (ΓByCodim p)] [∀ p, Algebra ℚ (ΓByCodim p)]
    (ρ : ∀ p,
      RationalCorrespondenceAction
        (ΓByCodim p) (ℚ × Cohomology (2 * p)))
    (IsHodgeMorphism : ∀ p,
      Module.End ℚ (ℚ × Cohomology (2 * p)) → Prop)
    (C : ∀ p, ClassGraphProjectorConstruction (M p) (ρ p))
    (D : ∀ p, ClassGraphProjectorDetection (M p) (ρ p))
    (K : ∀ p,
      ClassGraphProjectorHodgeCompatibility
        (M p) (IsHodgeMorphism p)) :
    RationalHodgeConjectureForModel M ↔
      ∀ p,
        EveryClassGraphHodgeMorphismHasAlgebraicLift
          (ρ p) (IsHodgeMorphism p) := by
  constructor
  · intro h p
    exact
      (everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms (K p)).mp
        (everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
          (C p) (h p))
  · intro h p
    apply rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
      (D p)
    exact
      (everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms (K p)).mpr
        (h p)

end Graded

section Family

universe x

variable {Variety : Type x}
variable {ChowByVarietyCodim : Variety → ℕ → Type u}
variable {CohomologyByVarietyDegree : Variety → ℕ → Type v}
variable [∀ X p, AddCommGroup (ChowByVarietyCodim X p)]
variable [∀ X p, Module ℚ (ChowByVarietyCodim X p)]
variable [∀ X n, AddCommGroup (CohomologyByVarietyDegree X n)]
variable [∀ X n, Module ℚ (CohomologyByVarietyDegree X n)]

/--
Family-level graph-projector equivalence.  If `Variety` indexes all smooth
projective complex varieties and the supplied models are the genuine
geometric ones, the left side is the universal rational Hodge conjecture.
-/
theorem rationalHodgeConjectureForFamily_iff_everyHodgeClassHasGraphProjectorLift
    (M : ∀ X p,
      RationalHodgeCycleClassModel
        (ChowByVarietyCodim X p)
        (CohomologyByVarietyDegree X (2 * p)))
    (ΓByVarietyCodim : Variety → ℕ → Type w)
    [∀ X p, Ring (ΓByVarietyCodim X p)]
    [∀ X p, Algebra ℚ (ΓByVarietyCodim X p)]
    (ρ : ∀ X p,
      RationalCorrespondenceAction
        (ΓByVarietyCodim X p)
        (ℚ × CohomologyByVarietyDegree X (2 * p)))
    (C : ∀ X p, ClassGraphProjectorConstruction (M X p) (ρ X p))
    (D : ∀ X p, ClassGraphProjectorDetection (M X p) (ρ X p)) :
    RationalHodgeConjectureForFamily M ↔
      ∀ X p, EveryHodgeClassHasGraphProjectorLift (M X p) (ρ X p) := by
  constructor
  · intro h X p
    exact
      everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
        (C X p) (h X p)
  · intro h X p
    exact
      rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
        (D X p) (h X p)

/--
Family-level form with an explicit Hodge-morphism predicate.  Besides the
Chow block maps, this exposes the Tate/Hodge comparison needed for the
classical projector wording.
-/
theorem rationalHodgeConjectureForFamily_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
    (M : ∀ X p,
      RationalHodgeCycleClassModel
        (ChowByVarietyCodim X p)
        (CohomologyByVarietyDegree X (2 * p)))
    (ΓByVarietyCodim : Variety → ℕ → Type w)
    [∀ X p, Ring (ΓByVarietyCodim X p)]
    [∀ X p, Algebra ℚ (ΓByVarietyCodim X p)]
    (ρ : ∀ X p,
      RationalCorrespondenceAction
        (ΓByVarietyCodim X p)
        (ℚ × CohomologyByVarietyDegree X (2 * p)))
    (IsHodgeMorphism : ∀ X p,
      Module.End ℚ
        (ℚ × CohomologyByVarietyDegree X (2 * p)) → Prop)
    (C : ∀ X p, ClassGraphProjectorConstruction (M X p) (ρ X p))
    (D : ∀ X p, ClassGraphProjectorDetection (M X p) (ρ X p))
    (K : ∀ X p,
      ClassGraphProjectorHodgeCompatibility
        (M X p) (IsHodgeMorphism X p)) :
    RationalHodgeConjectureForFamily M ↔
      ∀ X p,
        EveryClassGraphHodgeMorphismHasAlgebraicLift
          (ρ X p) (IsHodgeMorphism X p) := by
  constructor
  · intro h X p
    exact
      (everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms (K X p)).mp
        (everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
          (C X p) (h X p))
  · intro h X p
    apply rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
      (D X p)
    exact
      (everyHodgeClassHasGraphProjectorLift_iff_hodgeMorphisms (K X p)).mpr
        (h X p)

end Family

end

end HodgeConjecture
