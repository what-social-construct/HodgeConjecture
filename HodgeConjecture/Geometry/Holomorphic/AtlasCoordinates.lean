module

public import HodgeConjecture.Geometry.Holomorphic.Atlas

@[expose] public section

/-!
# Local coordinates for the descended forms

On an open contained in one chart source, the actual coordinate section
determines and constructs the whole compatible family. Composition and
local equality of derivative pullbacks prove the transition cocycle.
The resulting linear equivalence commutes with the same differentials.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicAtlas

open TopologicalSpace
open scoped Manifold ContDiff Topology
open HolomorphicForms

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def source (e : Chart E M) : Opens M := ⟨e.1.source, e.1.open_source⟩

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem domain_le_overlap {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (j : Chart E M) : domain j U ≤ overlap j e U :=
  fun _ hz ↦ ⟨hz.1, hz.2, hU hz.2⟩

theorem transition_contDiffOn_domain {U : Opens M} (e : Chart E M)
    (hU : U ≤ source e) (j : Chart E M) :
    ContDiffOn ℂ ∞ (transition j e) (domain j U) :=
  (transition_contDiffOn j e U).mono (domain_le_overlap e hU j)

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem transition_mapsTo_domain {U : Opens M} (e : Chart E M)
    (hU : U ≤ source e) (j : Chart E M) :
    Set.MapsTo (transition j e) (domain j U) (domain e U) :=
  fun _ hz ↦ transition_mapsTo j e U (domain_le_overlap e hU j hz)

/-- Pullback from a chart covering the whole intrinsic open. -/
def chartPullback {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (j : Chart E M) (n : ℕ) : Sections (domain e U) n →ₗ[ℂ] Sections (domain j U) n :=
  pullback (transition j e) (transition_contDiffOn_domain e hU j)
    (transition_mapsTo_domain e hU j) n

/-- The actual overlap cocycle, including derivative factors in every argument. -/
theorem chartPullback_compatible {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (n : ℕ) (a : Sections (domain e U) n) :
    (fun j ↦ chartPullback e hU j n a) ∈ compatibleSubmodule (E := E) U n := by
  intro j k
  change HolomorphicForms.restrict (overlap_le j k U) n
    (pullback (transition j e) (transition_contDiffOn_domain e hU j)
      (transition_mapsTo_domain e hU j) n a) = pullback (transition j k) (transition_contDiffOn j k U)
    (transition_mapsTo j k U) n (pullback (transition k e)
      (transition_contDiffOn_domain e hU k) (transition_mapsTo_domain e hU k) n a)
  rw [restrict_pullback, pullback_comp]
  apply pullback_congr
  intro z hz
  change e.1 (j.1.symm z) = e.1 (k.1.symm (k.1 (j.1.symm z)))
  rw [k.1.left_inv hz.2.2]

/-- A coordinate section extends by the proved transition pullbacks, without extra data. -/
def fromChart {U : Opens M} (e : Chart E M) (hU : U ≤ source e) (n : ℕ) :
    Sections (domain e U) n →ₗ[ℂ] Forms E U n where
  toFun a := ⟨fun j ↦ chartPullback e hU j n a, chartPullback_compatible e hU n a⟩
  map_add' a b := Subtype.ext (funext fun j ↦ map_add (chartPullback e hU j n) a b)
  map_smul' c a := Subtype.ext (funext fun j ↦ map_smul (chartPullback e hU j n) c a)

theorem fromChart_inChart {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (n : ℕ) (a : Forms E U n) : fromChart e hU n (inChart U n e a) = a := by
  apply Subtype.ext
  funext j
  apply ContMDiffMap.ext
  intro z
  exact (congrArg (fun b : Sections (overlap j e U) n ↦ b
    ⟨z.1, domain_le_overlap e hU j z.2⟩) (a.2 j e)).symm

theorem inChart_fromChart {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (n : ℕ) (a : Sections (domain e U) n) :
    inChart U n e (fromChart e hU n a) = a := by
  change pullback (transition e e) (transition_contDiffOn_domain e hU e)
    (transition_mapsTo_domain e hU e) n a = a
  have heq : Set.EqOn (transition e e) id (domain e U) :=
    fun _ hz ↦ e.1.right_inv hz.1
  exact (pullback_congr _ contDiffOn_id _ (fun _ hz ↦ hz) heq n a).trans
    (pullback_id (domain e U) n a)

/-- The local identification uses exactly the original intrinsic and coordinate sections. -/
def chartEquiv {U : Opens M} (e : Chart E M) (hU : U ≤ source e) (n : ℕ) :
    Forms E U n ≃ₗ[ℂ] Sections (domain e U) n where
  toLinearMap := inChart U n e
  invFun := fromChart e hU n
  left_inv := fromChart_inChart e hU n
  right_inv := inChart_fromChart e hU n

theorem inChart_injective {U : Opens M} (e : Chart E M) (hU : U ≤ source e) (n : ℕ) :
    Function.Injective (inChart U n e) := (chartEquiv e hU n).injective

theorem fromChart_differential {U : Opens M} (e : Chart E M) (hU : U ≤ source e)
    (n : ℕ) (a : Sections (domain e U) n) :
    differential U n (fromChart e hU n a) =
      fromChart e hU (n + 1) (HolomorphicForms.differential (domain e U) n a) := by
  apply inChart_injective e hU (n + 1)
  rw [inChart_differential, inChart_fromChart, inChart_fromChart]

/-- The inverse image of a coordinate open, in the original manifold topology. -/
def coordinateOpen (e : Chart E M) (V : Opens E) : Opens M :=
  ⟨e.1.source ∩ e.1 ⁻¹' V, e.1.isOpen_inter_preimage V.isOpen⟩

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem coordinateOpen_le_source (e : Chart E M) (V : Opens E) :
    coordinateOpen e V ≤ source e := fun _ hz ↦ hz.1

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem coordinateOpen_le (e : Chart E M) {U : Opens M} {V : Opens E}
    (hV : V ≤ domain e U) : coordinateOpen e V ≤ U := by
  intro p hp
  have h := (hV hp.2).2
  change e.1.symm (e.1 p) ∈ U at h
  rwa [e.1.left_inv hp.1] at h

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem domain_coordinateOpen_le (e : Chart E M) (V : Opens E) :
    domain e (coordinateOpen e V) ≤ V := by
  intro z hz
  have h := hz.2.2
  change e.1 (e.1.symm z) ∈ V at h
  rwa [e.1.right_inv hz.1] at h

end HodgeConjecture.HolomorphicAtlas
