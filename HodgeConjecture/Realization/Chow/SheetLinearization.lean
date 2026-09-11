import HodgeConjecture.Boundary.Sheets.MarkedBlockProjector
import HodgeConjecture.Correspondence.HeckeProjector
import HodgeConjecture.Realization.Chow.Model

/-!
# Linearizing generic sheets into Chow correspondences

For a finite subgroup `H ≤ G`, a right coset `gH` determines the element

`[g] e_H ∈ ℚ[G]`,

where `e_H` is the normalized subgroup average.  Right multiplication of a
representative by an element of `H` does not change this element, so the
construction descends to the generic sheet set `G / H`.  Extending it
linearly gives a canonical map from the split sheet-function space to the
rational group algebra.  The distinguished base-sheet selector maps exactly
to `e_H`, and hence to the subgroup-averaging graph correspondence and its
generic Chow class.

This is deliberately a linear map, not an algebra homomorphism.  The source
uses pointwise multiplication, whereas the targets use group-algebra or
correspondence convolution.  For example, with trivial `H`, distinct delta
functions multiply to zero pointwise while their group-basis images need not
multiply to zero.  Any compatibility between selector multiplication and a
correspondence action is therefore additional geometric input.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u v w q z

namespace SchemeCorrespondence

variable {G : Type v} [Group G]

/--
The group-algebra vector attached to a right coset `gH`, namely `[g] e_H`.

The quotient relation for `G ⫸ H` says that equivalent representatives
differ by right multiplication by an element of `H`.  The lemma
`single_mul_subgroupAverage` makes the displayed formula independent of that
choice.
-/
noncomputable def rightCosetAverage
    (H : Subgroup G) [Fintype H] :
    CollisionFoundations.GaloisSheets H → MonoidAlgebra ℚ G :=
  fun q ↦ Quotient.liftOn' q
    (fun g ↦ MonoidAlgebra.single g 1 * subgroupAverage H)
    (by
      intro a b hab
      have hh : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      let h : H := ⟨a⁻¹ * b, hh⟩
      calc
        MonoidAlgebra.single a 1 * subgroupAverage H =
            MonoidAlgebra.single a 1 *
              (MonoidAlgebra.single (h : G) 1 * subgroupAverage H) := by
                rw [single_mul_subgroupAverage H h]
        _ = (MonoidAlgebra.single a 1 *
              MonoidAlgebra.single (h : G) 1) * subgroupAverage H := by
                rw [mul_assoc]
        _ = MonoidAlgebra.single b 1 * subgroupAverage H := by
          rw [MonoidAlgebra.single_mul_single]
          simp [h])

theorem rightCosetAverage_mk
    (H : Subgroup G) [Fintype H] (g : G) :
    rightCosetAverage H
        (g : CollisionFoundations.GaloisSheets H) =
      MonoidAlgebra.single g 1 * subgroupAverage H :=
  rfl

/-- The base coset maps to the normalized subgroup average. -/
@[simp]
theorem rightCosetAverage_base
    (H : Subgroup G) [Fintype H] :
    rightCosetAverage H (baseSheet H) = subgroupAverage H := by
  change
    MonoidAlgebra.single (1 : G) 1 * subgroupAverage H =
      subgroupAverage H
  simpa using single_mul_subgroupAverage H (1 : H)

/--
Linear extension of `gH ↦ [g] e_H` from rational functions on the finite
sheet set to the rational group algebra.

This map does not claim to preserve multiplication: the source multiplication
is pointwise and the target multiplication is convolution.
-/
noncomputable def sheetLinearization
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)] :
    GenericSheetAlgebra ℚ H →ₗ[ℚ] MonoidAlgebra ℚ G where
  toFun f := ∑ s, f s • rightCosetAverage H s
  map_add' f g := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp [smul_smul, Finset.smul_sum]

/-- The distinguished sheet selector linearizes to `e_H`. -/
@[simp]
theorem sheetLinearization_selector
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)] :
    sheetLinearization H (MarkedSheetProjector.selector H) =
      subgroupAverage H := by
  classical
  change
    (∑ s, MarkedSheetProjector.selector H s • rightCosetAverage H s) = _
  rw [Fintype.sum_eq_single (baseSheet H)]
  · simp
  · intro s hs
    simp [MarkedSheetProjector.selector, genericSheetSelector, hs]

variable {T X : Scheme.{u}} (pX : X ⟶ T)

/--
The sheet linearization followed by the deck-graph algebra map into the free
finite-étale correspondence algebra.
-/
noncomputable def sheetToFiniteEtale
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)]
    (alpha : FiniteDeckAction pX G) :
    GenericSheetAlgebra ℚ H →ₗ[ℚ] FiniteEtaleFreeAlgebra pX :=
  (alpha.toFiniteEtaleAlgebra pX).toLinearMap.comp
    (sheetLinearization H)

/-- The base-sheet selector becomes the subgroup-averaging correspondence. -/
@[simp]
theorem sheetToFiniteEtale_selector
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)]
    (alpha : FiniteDeckAction pX G) :
    sheetToFiniteEtale pX H alpha (MarkedSheetProjector.selector H) =
      subgroupAveragingProjector pX H alpha := by
  change
    alpha.toFiniteEtaleAlgebra pX
        (sheetLinearization H (MarkedSheetProjector.selector H)) = _
  rw [sheetLinearization_selector,
    subgroupAverage_toFiniteEtaleAlgebra]

variable {genericAlgebra : Type q}
variable {compactifiedAlgebra : Type w}
variable {V : Type z}
variable [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
variable [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
variable [AddCommGroup V] [Module ℚ V]

/--
The sheet linearization followed by deck-graph realization and the supplied
generic Chow cycle-class map.
-/
noncomputable def sheetToGenericChow
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)]
    (alpha : FiniteDeckAction pX G)
    (chi :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra V) :
    GenericSheetAlgebra ℚ H →ₗ[ℚ] genericAlgebra :=
  chi.genericCycleClass.toLinearMap.comp
    (sheetToFiniteEtale pX H alpha)

/--
The generic Chow image of the base-sheet selector is the cycle class of the
subgroup-averaging graph correspondence.
-/
@[simp]
theorem sheetToGenericChow_selector
    (H : Subgroup G) [Fintype H]
    [Fintype (CollisionFoundations.GaloisSheets H)]
    (alpha : FiniteDeckAction pX G)
    (chi :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra V) :
    sheetToGenericChow pX H alpha chi
        (MarkedSheetProjector.selector H) =
      chi.genericCycleClass
        (subgroupAveragingProjector pX H alpha) := by
  change
    chi.genericCycleClass
        (sheetToFiniteEtale pX H alpha
          (MarkedSheetProjector.selector H)) = _
  rw [sheetToFiniteEtale_selector]

end SchemeCorrespondence

end

end HodgeConjecture
