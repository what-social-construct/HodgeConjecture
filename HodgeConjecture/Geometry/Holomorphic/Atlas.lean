module

public import HodgeConjecture.Geometry.Holomorphic.Pullback
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

@[expose] public section

/-!
# Descent of coordinate forms through an analytic atlas

A form is a family of the existing coordinate sections satisfying the
actual derivative pullback equation on every overlap. This is a submodule
of the product of coordinate section spaces. The exterior differential
preserves that submodule by its proved pullback naturality.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicAtlas

open TopologicalSpace IsManifold
open scoped Manifold ContDiff Topology
open HolomorphicForms

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- Charts of the given native atlas, with no additional atlas choices. -/
abbrev Chart (E M : Type) [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace E M] :=
  {e : OpenPartialHomeomorph M E // e ∈ atlas E M}

/-- The coordinate open on which an intrinsic open U meets a chart. -/
def domain (e : Chart E M) (U : Opens M) : Opens E :=
  ⟨e.1.target ∩ e.1.symm ⁻¹' U, e.1.isOpen_inter_preimage_symm U.isOpen⟩

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem domain_mono (e : Chart E M) {U V : Opens M} (h : U ≤ V) :
    domain e U ≤ domain e V := fun _ hz ↦ ⟨hz.1, h hz.2⟩

/-- The actual coordinate transition, defined on the original partial maps. -/
def transition (e e' : Chart E M) : E → E := e'.1 ∘ e.1.symm

def overlap (e e' : Chart E M) (U : Opens M) : Opens E :=
  domain e (U ⊓ ⟨e'.1.source, e'.1.open_source⟩)

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem overlap_le (e e' : Chart E M) (U : Opens M) : overlap e e' U ≤ domain e U :=
  domain_mono e inf_le_left

theorem transition_contDiffOn (e e' : Chart E M) (U : Opens M) :
    ContDiffOn ℂ ∞ (transition e e') (overlap e e' U) := by
  have h := (𝓘(ℂ, E)).contDiffOn_extendCoordChange
    (subset_maximalAtlas (n := ∞) e.2) (subset_maximalAtlas (n := ∞) e'.2)
  have h' : ContDiffOn ℂ ∞ (transition e e')
      (e.1.target ∩ e.1.symm ⁻¹' e'.1.source) := by
    simpa [ModelWithCorners.extendCoordChange, transition, mfld_simps] using h
  exact h'.mono (fun _ hz ↦ ⟨hz.1, hz.2.2⟩)

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem transition_mapsTo (e e' : Chart E M) (U : Opens M) :
    Set.MapsTo (transition e e') (overlap e e' U) (domain e' U) := by
  intro z hz
  refine ⟨e'.1.map_source hz.2.2, ?_⟩
  change e'.1.symm (e'.1 (e.1.symm z)) ∈ U
  rw [e'.1.left_inv hz.2.2]
  exact hz.2.1

/-- The coordinate pullback on the actual overlap. -/
def overlapPullback (e e' : Chart E M) (U : Opens M) (n : ℕ) :
    Sections (domain e' U) n →ₗ[ℂ] Sections (overlap e e' U) n :=
  pullback (transition e e') (transition_contDiffOn e e' U) (transition_mapsTo e e' U) n

/-- Descent means equality of genuine coordinate sections on every overlap. -/
def compatibleSubmodule (U : Opens M) (n : ℕ) :
    Submodule ℂ (∀ e : Chart E M, Sections (domain e U) n) where
  carrier := {a : (∀ e : Chart E M, Sections (domain e U) n) |
    ∀ (e e' : Chart E M), HolomorphicForms.restrict (overlap_le e e' U) n (a e) =
      overlapPullback e e' U n (a e')}
  zero_mem' := by intro e e'; simp
  add_mem' ha hb := by intro e e'; simp only [Pi.add_apply, map_add, ha e e', hb e e']
  smul_mem' c a ha := by intro e e'; simp only [Pi.smul_apply, map_smul, ha e e']

/-- Intrinsic forms on M, obtained by descent of the original coordinate sections. -/
abbrev Forms (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    (U : Opens M) (n : ℕ) := compatibleSubmodule (E := E) U n

/-- Evaluation in a chart is a linear map to the original coordinate section space. -/
def inChart (U : Opens M) (n : ℕ) (e : Chart E M) :
    Forms E U n →ₗ[ℂ] Sections (domain e U) n :=
  (LinearMap.proj e).comp (compatibleSubmodule U n).subtype

/-- The coordinate exterior derivative preserves the proved overlap equations. -/
def differential (U : Opens M) (n : ℕ) : Forms E U n →ₗ[ℂ] Forms E U (n + 1) where
  toFun a := ⟨fun e ↦ HolomorphicForms.differential (domain e U) n (a.1 e), by
    change ∀ e e', _
    intro e e'
    rw [HolomorphicForms.restrict_differential, a.2 e e']
    exact pullback_differential _ _ _ n (a.1 e')⟩
  map_add' a b := Subtype.ext (funext fun e ↦ map_add _ _ _)
  map_smul' c a := Subtype.ext (funext fun e ↦ map_smul _ c _)

@[simp]
theorem inChart_differential (U : Opens M) (n : ℕ) (e : Chart E M) (a : Forms E U n) :
    inChart U (n + 1) e (differential U n a) =
      HolomorphicForms.differential (domain e U) n (inChart U n e a) := rfl

theorem differential_comp (U : Opens M) (n : ℕ) :
    (differential (E := E) U (n + 1)).comp (differential U n) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext e
  exact LinearMap.congr_fun (HolomorphicForms.differential_comp (domain e U) n) (a.1 e)

/-- Restriction descends the original coordinate restriction maps. -/
def restrict {U V : Opens M} (h : U ≤ V) (n : ℕ) : Forms E V n →ₗ[ℂ] Forms E U n where
  toFun a := ⟨fun e ↦ HolomorphicForms.restrict (domain_mono e h) n (a.1 e), by
    change ∀ e e', _
    intro e e'
    apply ContMDiffMap.ext
    intro z
    exact congrArg (fun b : Sections (overlap e e' V) n ↦ b
      ⟨z.1, ⟨z.2.1, h z.2.2.1, z.2.2.2⟩⟩) (a.2 e e')⟩
  map_add' a b := Subtype.ext (funext fun e ↦ map_add _ _ _)
  map_smul' c a := Subtype.ext (funext fun e ↦ map_smul _ c _)

theorem restrict_differential {U V : Opens M} (h : U ≤ V) (n : ℕ) (a : Forms E V n) :
    restrict h (n + 1) (differential V n a) = differential U n (restrict h n a) := by
  apply Subtype.ext
  funext e
  exact HolomorphicForms.restrict_differential (domain_mono e h) n (a.1 e)

end HodgeConjecture.HolomorphicAtlas
