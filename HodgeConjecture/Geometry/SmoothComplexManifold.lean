/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Geometry.EtaleAnalyticCoordinates
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

@[expose] public section

/-!
# The analytic atlas on canonical complex points of a smooth scheme

A scheme smooth of relative dimension d over ℂ has étale coordinates to
`Spec ℂ[Fin d]` near every original complex point. The constructed analytic
local inverses give the native `ChartedSpace (Fin d → ℂ)` structure for the
existing evaluation topology. Every regular function is analytic in these
charts, which proves analytic compatibility of all coordinate changes.

Adapted and generalized from AxiomMath/Weil, revision
`27cdb2049be62ee2911429b47f54774078450e32`,
`ComplexPoints/RiemannSurface.lean` (Apache-2.0).
The one-dimensional differentiability shortcut is replaced by the analytic
implicit-function proof, valid in every finite coordinate dimension.
See `third_party/axiom-weil/LICENSE`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory TopologicalSpace Topology Filter
open scoped Manifold ContDiff

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable (d : ℕ) {C : Scheme.{0}} {c : C ⟶ Spec (.of ℂ)}

/-- Smoothness supplies an actual étale algebraic coordinate morphism near each point. -/
theorem exists_etaleCoordinates [SmoothOfRelativeDimension d c] (p : ComplexPoints c) :
    ∃ (V : C.Opens) (hV : IsAffineOpen V)
      (f : Spec Γ(C, V) ⟶ Spec (.of (MvPolynomial (Fin d) ℂ))),
      p.Mem V ∧ Etale f ∧ f ≫ (HodgeConjecture.AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)) = hV.fromSpec ≫ c := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨U, hU, V, hV, hx, e, hst⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := c)
      (p.hom.base pt)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun z _ => by
    rw [Subsingleton.elim z (c.base (p.hom.base pt))]
    exact e hx
  obtain ⟨g, hgC, hg⟩ := hst.exists_etale_mvPolynomial
  let ρ : ℂ ≃+* Γ(Spec (.of ℂ), ⊤) := (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm
  let m : CommRingCat.of (MvPolynomial (Fin d) ℂ) ≅
      CommRingCat.of (MvPolynomial (Fin d) Γ(Spec (.of ℂ), ⊤)) :=
    (MvPolynomial.mapEquiv (Fin d) ρ).toCommRingCatIso
  have : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.2 hg
  refine ⟨V, hV, Spec.map (CommRingCat.ofHom g) ≫ Spec.map m.hom, (mem_iff pt).2 hx,
    inferInstance, ?_⟩
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hV e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, HodgeConjecture.AffineComplexPoints.structureMorphism, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change g (MvPolynomial.map ρ.toRingHom (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C, ← RingHom.comp_apply g MvPolynomial.C, hgC]
  rfl


/-- An algebraic coordinate chart whose regular-function expressions are complex analytic. -/
def IsAlgebraicChart (e : OpenPartialHomeomorph (ComplexPoints c) (Fin d → ℂ)) : Prop :=
  (∃ (V : C.Opens) (t : Fin d → Γ(C, V)), (∀ q ∈ e.source, q.Mem V) ∧
      Set.EqOn e (coordsOrZero t) e.source) ∧
  ∀ (V : C.Opens) (g : Γ(C, V)),
    ContDiffOn ℂ ω (evalOrZero V g ∘ e.symm) (e.target ∩ e.symm ⁻¹' {q | q.Mem V})

/-- Every canonical point has a constructed algebraic analytic chart. -/
theorem exists_isAlgebraicChart [SmoothOfRelativeDimension d c] (p : ComplexPoints c) :
    ∃ e : OpenPartialHomeomorph (ComplexPoints c) (Fin d → ℂ), p ∈ e.source ∧ IsAlgebraicChart d e := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨V, hV, f, hpV, hfe, hf⟩ := exists_etaleCoordinates d p
  set y' : Spec Γ(C, V) ⟶ Spec (.of ℂ) := hV.fromSpec ≫ c
  let J : ComplexPoints y' → ComplexPoints c := map hV.fromSpec rfl
  have hJ : IsOpenEmbedding J := isOpenEmbedding_map_of_isOpenImmersion _ rfl
  have hrange : Set.range J = {q | q.Mem V} := by
    rw [range_map_of_isOpenImmersion, IsAffineOpen.opensRange_fromSpec]
  obtain ⟨q₀, hq₀⟩ : p ∈ Set.range J := hrange ▸ hpV
  have : Nonempty (ComplexPoints y') := ⟨q₀⟩
  have htop : (⊤ : (Spec Γ(C, V)).Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  obtain ⟨φ, W, hq₀φ, hφ, -, -, -, -⟩ :=
    exists_analyticOpenPartialHomeomorph_of_etale f hf (isAffineOpen_top _)
      (HodgeConjecture.PolynomialComplexPoints.surjective_presentationHom_coordinateSections d) (isAffineOpen_top _) htop q₀ (mem_top q₀)
  let κ := HodgeConjecture.PolynomialComplexPoints.homeomorph d
  let J' := hJ.toOpenPartialHomeomorph J
  let e := J'.symm.trans (φ.trans κ.toOpenPartialHomeomorph)
  have he_symm : ∀ z, e.symm z = J (φ.symm (κ.symm z)) := fun z => rfl
  have he_apply : ∀ q, e q = κ (φ (J'.symm q)) := fun q => rfl
  have hsrc : ∀ q, q ∈ e.source ↔ ∃ q' ∈ φ.source, J q' = q := by
    intro q
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ, Set.inter_univ, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨⟨q', -, rfl⟩, h⟩
      exact ⟨q', by rwa [hJ.toOpenPartialHomeomorph_left_inv] at h, rfl⟩
    · rintro ⟨q', h, rfl⟩
      exact ⟨⟨q', trivial, rfl⟩, by rwa [hJ.toOpenPartialHomeomorph_left_inv]⟩
  refine ⟨e, (hsrc p).2 ⟨q₀, hq₀φ, hq₀⟩,
    ⟨⟨V, (fun i => (Scheme.ΓSpecIso Γ(C, V)).hom (f.appLE ⊤ ⊤ htop (HodgeConjecture.PolynomialComplexPoints.coordinateSections d i))), ?_, ?_⟩, ?_⟩⟩
  · intro q hq
    obtain ⟨q', -, rfl⟩ := (hsrc q).1 hq
    exact hrange.subset ⟨q', rfl⟩
  · intro q hq
    obtain ⟨q', -, rfl⟩ := (hsrc q).1 hq
    have hmem : (J q').Mem V := hrange.subset ⟨q', rfl⟩
    funext i
    have key := eval_appLE hV.fromSpec rfl hV.fromSpec_preimage_self.ge
      ((Scheme.ΓSpecIso Γ(C, V)).hom (f.appLE ⊤ ⊤ htop (HodgeConjecture.PolynomialComplexPoints.coordinateSections d i))) q' (mem_top q')
    rw [fromSpec_appLE_top, Iso.hom_inv_id_apply, eval_appLE f hf htop] at key
    change e (J q') i = evalOrZero V _ (J q')
    rw [he_apply, hJ.toOpenPartialHomeomorph_left_inv, hφ,
      HodgeConjecture.PolynomialComplexPoints.homeomorph_apply, evalOrZero_of_mem _ hmem]
    exact key
  · intro V'' g z₀ hz₀
    have htgt : ∀ z, z ∈ e.target ↔ κ.symm z ∈ φ.target := by
      intro z
      simp [e, J', κ]
    obtain ⟨hz₀t, hz₀V⟩ := hz₀
    rw [htgt] at hz₀t
    set a₀ := κ.symm z₀ with ha₀
    set q₀' := φ.symm a₀ with hq₀'
    have hJq : (J q₀').Mem V'' := by rw [← he_symm]; exact hz₀V
    obtain ⟨U'', hU'', hxU'', hU''le⟩ :=
      (Opens.isBasis_iff_nbhd.1 (Spec Γ(C, V)).isBasis_affineOpens)
        (show q₀'.hom.base pt ∈ hV.fromSpec ⁻¹ᵁ V'' from (mem_iff pt).1 hJq)
    obtain ⟨φ₂, W₂, hq₂, hφ₂, hW₂, hsrc₂, htgt₂, hol₂⟩ :=
      exists_analyticOpenPartialHomeomorph_of_etale f hf (isAffineOpen_top _)
        (HodgeConjecture.PolynomialComplexPoints.surjective_presentationHom_coordinateSections d) hU'' (by simp) q₀' ((mem_iff pt).2 hxU'')
    obtain ⟨G, hG, hGeq⟩ := hol₂ (hV.fromSpec.appLE V'' U'' hU''le g)
    have hφq : φ q₀' = a₀ := φ.right_inv hz₀t
    have hmemW : z₀ ∈ W₂ := by
      have h1 : φ₂ q₀' ∈ φ₂.target := φ₂.map_source hq₂
      rw [htgt₂] at h1
      obtain ⟨ha, h2⟩ := h1
      rw [HodgeConjecture.PolynomialComplexPoints.coords_coordinateSections, hφ₂, ← hφ, hφq, ha₀, Homeomorph.apply_symm_apply] at h2
      exact h2
    have hdiff : ContDiffAt ℂ ω G z₀ := hG.contDiffAt (hW₂.mem_nhds hmemW)
    have hopen : IsOpen (κ.symm ⁻¹' (φ.target ∩ φ.symm ⁻¹' φ₂.source)) :=
      (φ.isOpen_inter_preimage_symm φ₂.open_source).preimage κ.symm.continuous
    have hev : (evalOrZero V'' g ∘ e.symm) =ᶠ[𝓝 z₀] G := by
      filter_upwards [hopen.mem_nhds ⟨hz₀t, hq₂⟩] with z hz
      obtain ⟨hzt, hz2⟩ := hz
      have hqU : (φ.symm (κ.symm z)).Mem U'' := hsrc₂ _ hz2
      have hJqV : (J (φ.symm (κ.symm z))).Mem V'' := (map_mem_iff _ _ _ _).2 (hqU.mono hU''le)
      simp only [Function.comp_apply, he_symm]
      rw [evalOrZero_of_mem _ hJqV, ← eval_appLE hV.fromSpec rfl hU''le g _ hqU,
        hGeq _ hz2 hqU (mem_top _), HodgeConjecture.PolynomialComplexPoints.coords_coordinateSections, ← hφ, φ.right_inv hzt,
        Homeomorph.apply_symm_apply]
    exact (hdiff.congr_of_eventuallyEq hev).contDiffWithinAt


variable [SmoothOfRelativeDimension d c]

/-- The atlas is built on the original analytic topology, without transporting a new topology. -/
instance analyticChartedSpace : ChartedSpace (Fin d → ℂ) (ComplexPoints c) where
  atlas := {e | IsAlgebraicChart d e}
  chartAt p := (exists_isAlgebraicChart d p).choose
  mem_chart_source p := (exists_isAlgebraicChart d p).choose_spec.1
  chart_mem_atlas p := (exists_isAlgebraicChart d p).choose_spec.2

theorem isAlgebraicChart_of_mem_atlas {e : OpenPartialHomeomorph (ComplexPoints c) (Fin d → ℂ)}
    (he : e ∈ atlas (Fin d → ℂ) (ComplexPoints c)) : IsAlgebraicChart d e := he

theorem isAlgebraicChart_chartAt (p : ComplexPoints c) :
    IsAlgebraicChart d (chartAt (Fin d → ℂ) p) := (exists_isAlgebraicChart d p).choose_spec.2

/-- All transitions of the constructed native atlas are complex analytic. -/
instance analyticIsManifold : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (ComplexPoints c) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨⟨V', t', hV', heq'⟩, -⟩ := isAlgebraicChart_of_mem_atlas d he'
  simp only [modelWithCornersSelf_coe, Set.range_id, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.inter_univ]
  apply contDiffOn_pi.mpr
  intro i
  refine ((isAlgebraicChart_of_mem_atlas d he).2 V' (t' i) |>.mono ?_).congr ?_
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact ⟨hz.1, hV' _ hz.2⟩
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact congrFun (heq' hz.2) i

/-- The same analytic atlas supports the native complex C∞ differential-form APIs. -/
instance smoothIsManifold : IsManifold 𝓘(ℂ, Fin d → ℂ) ∞ (ComplexPoints c) :=
  IsManifold.of_le (n := ω) (by simp)

/-- Every original regular function is analytic in the actual chart at a point of its domain. -/
theorem contDiffAt_evalOrZero_comp_chartAt_symm {V : C.Opens} (g : Γ(C, V))
    {p : ComplexPoints c} (hp : p.Mem V) :
    ContDiffAt ℂ ω (evalOrZero V g ∘ (chartAt (Fin d → ℂ) p).symm) (chartAt (Fin d → ℂ) p p) := by
  have hopen : IsOpen ((chartAt (Fin d → ℂ) p).target ∩
      (chartAt (Fin d → ℂ) p).symm ⁻¹' {q | q.Mem V}) :=
    (chartAt (Fin d → ℂ) p).isOpen_inter_preimage_symm (isOpen_setOf_mem V)
  refine ((isAlgebraicChart_chartAt d p).2 V g).contDiffAt (hopen.mem_nhds ⟨?_, ?_⟩)
  · exact (chartAt (Fin d → ℂ) p).map_source (mem_chart_source (Fin d → ℂ) p)
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [(chartAt (Fin d → ℂ) p).left_inv (mem_chart_source (Fin d → ℂ) p)]
    exact hp

/-- Regular functions on every scheme open are holomorphic for the constructed atlas. -/
theorem contMDiffOn_evalOrZero (V : C.Opens) (g : Γ(C, V)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (evalOrZero V g)
      {q : ComplexPoints c | q.Mem V} := by
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff]
  refine ⟨(continuousOn_evalOrZero V g).continuousAt ((isOpen_setOf_mem V).mem_nhds hp), ?_⟩
  simp only [extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv]
  simp only [mfld_simps]
  exact (contDiffAt_evalOrZero_comp_chartAt_symm d g hp).contDiffWithinAt

/-- Morphisms over ℂ are analytic on the original complex points, allowing different dimensions. -/
theorem contMDiff_map (e : ℕ) {D : Scheme.{0}} {f : D ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension e f] (φ : C ⟶ D) (hφ : φ ≫ f = c) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω (map φ hφ) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(continuous_map φ hφ).continuousAt, ?_⟩
  simp only [extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id]
  simp only [mfld_simps]
  apply ContDiffAt.contDiffWithinAt
  set κ := chartAt (Fin d → ℂ) p
  set κ' := chartAt (Fin e → ℂ) (map φ hφ p)
  obtain ⟨⟨V', t', hV', heq'⟩, -⟩ := isAlgebraicChart_chartAt e (map φ hφ p)
  have hmp : map φ hφ p ∈ κ'.source := mem_chart_source (Fin e → ℂ) _
  have hpV : p.Mem (φ ⁻¹ᵁ V') := hV' _ hmp
  apply contDiffAt_pi.mpr
  intro i
  have hd := contDiffAt_evalOrZero_comp_chartAt_symm d (φ.app V' (t' i)) hpV
  apply hd.congr_of_eventuallyEq
  have hopen : IsOpen (κ.target ∩ κ.symm ⁻¹' (map φ hφ ⁻¹' κ'.source)) :=
    κ.isOpen_inter_preimage_symm (κ'.open_source.preimage (continuous_map φ hφ))
  have hmem : κ p ∈ κ.target ∩ κ.symm ⁻¹' (map φ hφ ⁻¹' κ'.source) := by
    refine ⟨κ.map_source (mem_chart_source (Fin d → ℂ) p), ?_⟩
    simp only [Set.mem_preimage]
    rw [κ.left_inv (mem_chart_source (Fin d → ℂ) p)]
    exact hmp
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨-, hz⟩ := hz
  have hzV : (map φ hφ (κ.symm z)).Mem V' := hV' _ hz
  simp only [Function.comp_apply]
  rw [heq' hz]
  change evalOrZero V' (t' i) _ = evalOrZero (φ ⁻¹ᵁ V') (φ.app V' (t' i)) _
  rw [evalOrZero_of_mem _ hzV,
    evalOrZero_of_mem _ (show (κ.symm z).Mem (φ ⁻¹ᵁ V') from hzV), eval_map_point]

end AlgebraicGeometry.Scheme.ComplexPoints
