module

public import HodgeConjecture.LinearAlgebra.Harmonic.Cohomology
public import HodgeConjecture.Realization.Betti.Examples.CircleCohomology

@[expose] public section

/-!
# Finite harmonic comparison from the actual two-open circle cover

The vertices are the original two contractible charts and the edges the two
components of their overlap. The finite coboundary is first-chart value minus
second-chart value on both components. The native quotient maps isomorphically
to actual singular H¹ through the original Mayer–Vietoris boundary.

Scalar inclusion and the genuine cellular harmonic projection commute with
that boundary. In contrast to a zero-differential coordinate presentation,
this finite complex retains the nonzero differential of the geometric cover.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.CircleCoverHarmonicComparison

open Harmonic

def coverComplex : OrientedTwoComplex Bool Bool Empty where
  incidence01 v _ := if v then -1 else 1
  incidence12 _ f := nomatch f
  boundarySqZero _ f := nomatch f

def coverSheaf : CellularSheaf coverComplex where
  vertexDim _ := 1
  edgeDim _ := 1
  faceDim f := nomatch f
  restrict01 _ _ := LinearMap.id
  restrict12 _ f := nomatch f
  restrict02 _ f := nomatch f
  restrictionComp _ _ f := nomatch f

/-- The finite chart-difference map on rational component coordinates. -/
def rationalCoboundary : (Bool → ℚ) →ₗ[ℚ] (Bool → ℚ) :=
  TwoComponentBoundary.diagonal.comp
    ((LinearMap.proj false : (Bool → ℚ) →ₗ[ℚ] ℚ) - LinearMap.proj true)

theorem rationalCoboundary_apply (a : Bool → ℚ) (b : Bool) :
    rationalCoboundary a b = a false - a true := rfl

theorem range_rationalCoboundary : LinearMap.range rationalCoboundary =
    LinearMap.range TwoComponentBoundary.diagonal := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a false - a true, rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨fun b => if b then 0 else q, ?_⟩
    ext b
    simp [rationalCoboundary_apply, TwoComponentBoundary.diagonal]

/-- The finite native quotient computes the actual circle singular cohomology. -/
def quotientCircleEquiv :
    ((Bool → ℚ) ⧸ LinearMap.range rationalCoboundary) ≃ₗ[ℚ]
      SingularCochains.Cohomology CircleCohomology.space 1 :=
  (Submodule.quotEquivOfEq _ _
    (range_rationalCoboundary.trans CircleCohomology.ker_componentBoundary.symm)).trans
      (CircleCohomology.componentBoundary.quotKerEquivOfSurjective
        CircleCohomology.componentBoundary_surjective)

theorem quotientCircleEquiv_mk (f : Bool → ℚ) :
    quotientCircleEquiv (Submodule.Quotient.mk f) = CircleCohomology.componentBoundary f := rfl

def ofReal : (Bool → ℝ) →ₗ[ℝ] coverSheaf.C1 :=
  (WithLp.linearEquiv 2 ℝ ((Σ _ : Bool, Fin 1) → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i => LinearMap.proj i.1)

/-- Literal scalar inclusion of the rational overlap-component cochains. -/
def realize : (Bool → ℚ) →ₗ[ℚ] coverSheaf.C1 :=
  (ofReal.restrictScalars ℚ).comp
    (LinearMap.pi fun b => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj b))

theorem realize_apply (f : Bool → ℚ) (b : Bool) (i : Fin 1) :
    realize f ⟨b, i⟩ = (f b : ℝ) := rfl

theorem delta0_apply (a : coverSheaf.C0) (b : Bool) :
    coverSheaf.delta0 a ⟨b, (0 : Fin 1)⟩ =
      a ⟨false, (0 : Fin 1)⟩ - a ⟨true, (0 : Fin 1)⟩ := by
  simp [CellularSheaf.delta0, CellularSheaf.assemble, CellularSheaf.delta0At,
    CellularSheaf.component, OrientedTwoComplex.incidence01Real,
    coverSheaf, coverComplex, sub_eq_add_neg]
  ring

theorem delta1_eq_zero : coverSheaf.delta1 = 0 := by
  apply LinearMap.ext
  intro a
  apply PiLp.ext
  rintro ⟨f, i⟩
  exact nomatch f

/-- The rational finite differential is exactly the real cellular differential. -/
theorem realize_coboundary (a : Bool → ℚ) :
    realize (rationalCoboundary a) = coverSheaf.delta0 (realize a) := by
  apply PiLp.ext
  rintro ⟨b, i⟩
  change Fin 1 at i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rw [delta0_apply]
  simp only [realize_apply, rationalCoboundary_apply, Rat.cast_sub]

def realJump : coverSheaf.C1 →ₗ[ℝ] ℝ :=
  ((LinearMap.proj (⟨true, (0 : Fin 1)⟩ : Σ _ : Bool, Fin 1) :
      ((Σ _ : Bool, Fin 1) → ℝ) →ₗ[ℝ] ℝ) -
    LinearMap.proj (⟨false, (0 : Fin 1)⟩ : Σ _ : Bool, Fin 1)).comp
    (WithLp.linearEquiv 2 ℝ ((Σ _ : Bool, Fin 1) → ℝ)).toLinearMap

theorem realJump_delta0 (a : coverSheaf.C0) : realJump (coverSheaf.delta0 a) = 0 := by
  change coverSheaf.delta0 a ⟨true, (0 : Fin 1)⟩ -
    coverSheaf.delta0 a ⟨false, (0 : Fin 1)⟩ = 0
  rw [delta0_apply, delta0_apply, sub_self]

theorem realJump_realize (f : Bool → ℚ) :
    realJump (realize f) = (TwoComponentBoundary.jump f : ℝ) := by
  change (f true : ℝ) - (f false : ℝ) = ((f true - f false : ℚ) : ℝ)
  simp

theorem realJump_projection (c : coverSheaf.C1) :
    realJump (coverSheaf.harmonicOneProjection c) = realJump c := by
  have hc : coverSheaf.IsOneCocycle c := by simp [CellularSheaf.IsOneCocycle, delta1_eq_zero]
  obtain ⟨a, ha⟩ := coverSheaf.sub_harmonicOneProjection_exact hc
  have h := congrArg realJump ha
  rw [realJump_delta0, map_sub] at h
  exact (sub_eq_zero.mp h.symm).symm

def projectedRealization : (Bool → ℚ) →ₗ[ℚ] coverSheaf.harmonicOneSubspace :=
  ((coverSheaf.harmonicOneProjection.restrictScalars ℚ).comp realize).codRestrict
    (coverSheaf.harmonicOneSubspace.restrictScalars ℚ)
      (fun f => coverSheaf.harmonicOneProjection_isHarmonic (realize f))

/-- Harmonic witnesses for actual singular classes, normalized by the native boundary. -/
def witness : SingularCochains.Cohomology CircleCohomology.space 1 →ₗ[ℚ]
    coverSheaf.harmonicOneSubspace :=
  projectedRealization.comp (TwoComponentBoundary.step.comp CircleCohomology.h1Equiv.toLinearMap)

theorem realJump_witness (z : SingularCochains.Cohomology CircleCohomology.space 1) :
    realJump (witness z) = (CircleCohomology.h1Equiv z : ℝ) := by
  change realJump (coverSheaf.harmonicOneProjection
    (realize (TwoComponentBoundary.step (CircleCohomology.h1Equiv z)))) = _
  rw [realJump_projection, realJump_realize, TwoComponentBoundary.jump_step]

theorem witness_injective : Function.Injective witness := by
  intro x y h
  apply CircleCohomology.h1Equiv.injective
  have hr := congrArg (fun z : coverSheaf.harmonicOneSubspace => realJump z) h
  rw [realJump_witness, realJump_witness] at hr
  exact_mod_cast hr

/-- The comparison square uses the original geometric connecting map. -/
theorem witness_componentBoundary (f : Bool → ℚ) :
    witness (CircleCohomology.componentBoundary f) = projectedRealization f := by
  apply Subtype.ext
  change coverSheaf.harmonicOneProjection
    (realize (TwoComponentBoundary.step
      (CircleCohomology.h1Equiv (CircleCohomology.componentBoundary f)))) = _
  rw [show CircleCohomology.h1Equiv (CircleCohomology.componentBoundary f) =
    TwoComponentBoundary.jump f from TwoComponentBoundary.boundaryEquiv_apply
      CircleCohomology.componentBoundary CircleCohomology.componentBoundary_surjective
        CircleCohomology.ker_componentBoundary f]
  have hdiff : f - TwoComponentBoundary.step (TwoComponentBoundary.jump f) =
      rationalCoboundary (fun b => if b then 0 else f false) := by
    ext b
    cases b <;> simp [TwoComponentBoundary.step, TwoComponentBoundary.jump,
      rationalCoboundary_apply]
  have hexact : coverSheaf.IsExactOneCochain
      (realize f - realize (TwoComponentBoundary.step (TwoComponentBoundary.jump f))) := by
    refine ⟨realize (fun b => if b then 0 else f false), ?_⟩
    rw [← realize_coboundary, ← hdiff, map_sub]
  have h := coverSheaf.harmonicOneProjection_of_exact hexact
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

end HodgeConjecture.CircleCoverHarmonicComparison

end
