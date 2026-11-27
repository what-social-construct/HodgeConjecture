module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

/-!
# Joint one-point extension of a compact family

A jointly continuous family with jointly continuous left inverses is
uniformly proper over a compact parameter space. The extended family is
therefore jointly continuous on the one-point compactifications. The
proof uses the compact image of all inverse images of a target compact
set, without a metric or a bound chosen separately for each parameter.
-/

set_option autoImplicit false

namespace HodgeConjecture.OnePointHomotopy

open Set Topology OnePoint

universe u v w

variable {P : Type u} {X : Type v} {Y : Type w}

/-- Extend each member of the original family by fixing the added point. -/
def mapFamily (F : P × X → Y) (q : P × OnePoint X) : OnePoint Y :=
  OnePoint.map (fun x ↦ F (q.1, x)) q.2

@[simp]
theorem mapFamily_infty (F : P × X → Y) (p : P) : mapFamily F (p, ∞) = ∞ := rfl

@[simp]
theorem mapFamily_coe (F : P × X → Y) (p : P) (x : X) :
    mapFamily F (p, (x : OnePoint X)) = (F (p, x) : OnePoint Y) := rfl

variable [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact family of continuous maps with continuous left inverses
extends jointly continuously at infinity. Only the source needs to be Hausdorff. -/
theorem continuous_map_family_of_leftInverse [CompactSpace P] [T2Space X]
    (F : P × X → Y) (G : P × Y → X) (hF : Continuous F) (hG : Continuous G)
    (hGF : ∀ (p : P) (x : X), G (p, F (p, x)) = x) :
    Continuous (mapFamily F) := by
  let i : P × X → P × OnePoint X := Prod.map id ((↑) : X → OnePoint X)
  have hi : IsOpenMap i :=
    ((Homeomorph.refl P).isOpenEmbedding.prodMap OnePoint.isOpenEmbedding_coe).isOpenMap
  apply continuous_def.mpr
  intro O hO
  let M : Set (P × X) := F ⁻¹' (((↑) : Y → OnePoint Y) ⁻¹' O)
  have hM : IsOpen M := (hO.preimage OnePoint.continuous_coe).preimage hF
  have hfinite : IsOpen (i '' M) := hi M hM
  by_cases hinfty : (∞ : OnePoint Y) ∈ O
  · let K : Set Y := (((↑) : Y → OnePoint Y) ⁻¹' O)ᶜ
    have hK : IsCompact K := ((OnePoint.isOpen_iff_of_mem hinfty).mp hO).2
    let L : Set X := G '' ((univ : Set P) ×ˢ K)
    have hL : IsCompact L := (isCompact_univ.prod hK).image hG
    let N : Set (OnePoint X) := (((↑) : X → OnePoint X) '' L)ᶜ
    have hN : IsOpen N := OnePoint.isOpen_compl_image_coe.mpr ⟨hL.isClosed, hL⟩
    have hmaps (p : P) (z : OnePoint X) (hz : z ∈ N) : mapFamily F (p, z) ∈ O := by
      cases z using OnePoint.rec with
      | infty => exact hinfty
      | coe x =>
          change (F (p, x) : OnePoint Y) ∈ O
          by_contra hx
          have hxL : x ∈ L := ⟨(p, F (p, x)), ⟨mem_univ p, hx⟩, hGF p x⟩
          exact hz ⟨x, hxL, rfl⟩
    have hpreimage : mapFamily F ⁻¹' O = (univ ×ˢ N) ∪ i '' M := by
      ext q
      constructor
      · intro hq
        rcases q with ⟨p, z⟩
        cases z using OnePoint.rec with
        | infty => exact Or.inl ⟨mem_univ p, OnePoint.infty_notMem_image_coe⟩
        | coe x => exact Or.inr ⟨(p, x), hq, rfl⟩
      · intro hq
        rcases hq with ⟨_, hz⟩ | ⟨⟨p, x⟩, hx, rfl⟩
        · exact hmaps q.1 q.2 hz
        · exact hx
    rw [hpreimage]
    exact (isOpen_univ.prod hN).union hfinite
  · have hpreimage : mapFamily F ⁻¹' O = i '' M := by
      ext q
      constructor
      · intro hq
        rcases q with ⟨p, z⟩
        cases z using OnePoint.rec with
        | infty => exact (hinfty hq).elim
        | coe x => exact ⟨(p, x), hq, rfl⟩
      · rintro ⟨⟨p, x⟩, hx, rfl⟩
        exact hx
    rw [hpreimage]
    exact hfinite

/-- Jointly continuous homeomorphisms and inverses extend as the original
pointwise one-point homeomorphisms over a compact parameter space. -/
theorem continuous_onePointCongr_family [CompactSpace P] [T2Space X]
    (e : P → X ≃ₜ Y)
    (he : Continuous (fun q : P × X ↦ e q.1 q.2))
    (heinv : Continuous (fun q : P × Y ↦ (e q.1).symm q.2)) :
    Continuous (fun q : P × OnePoint X ↦ (e q.1).onePointCongr q.2) := by
  change Continuous (mapFamily (fun q : P × X ↦ e q.1 q.2))
  exact continuous_map_family_of_leftInverse _ _ he heinv
    (fun p x ↦ (e p).symm_apply_apply x)

end HodgeConjecture.OnePointHomotopy
