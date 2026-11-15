module

public import HodgeConjecture.Realization.Betti.ComplexSingularCochainPatching
public import HodgeConjecture.Realization.Betti.ComplexSingularSheafificationKernel
public import HodgeConjecture.SheafCohomology.SheafifyLocalLifts
public import HodgeConjecture.SheafCohomology.ComplexKernelComparison

@[expose] public noncomputable section

/-!
# Actual complex singular cochains and sheafified global sections

On paracompact Hausdorff spaces the native unit is degreewise surjective.
Together with its proved acyclic native kernel this gives a quasi-isomorphism
of the original unrestricted complex-valued singular cochain complexes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace HodgeConjecture.SingularCoefficientChange

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

variable (X : TopCat.{0})

theorem globalCochainsToSheaf_restrict (U : Opens X) (n : ℕ)
    (φ : (complexCochains X).X n) :
    (cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((globalCochainsToSheaf X).f n φ) =
    (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op U)
      ((pullback (Opens.inclusion' U)).f n φ) := by
  rw [← restrict_top_cochain X U n φ]
  exact ((toSheafify (Opens.grothendieckTopology X) (presheaf X n)).naturality_apply
    (homOfLE (show U ≤ ⊤ from le_top)).op
    ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)).symm

theorem globalCochainsToSheaf_germ_eq_iff (n : ℕ)
    (φ ψ : (complexCochains X).X n) (x : X) :
    TopCat.Presheaf.germ (cochainSheaf X n).obj ⊤ x trivial
        ((globalCochainsToSheaf X).f n φ) =
      TopCat.Presheaf.germ (cochainSheaf X n).obj ⊤ x trivial
        ((globalCochainsToSheaf X).f n ψ) ↔
      ∃ V : Opens X, x ∈ V ∧
        (pullback (Opens.inclusion' V)).f n φ = (pullback (Opens.inclusion' V)).f n ψ := by
  change TopCat.Presheaf.germ (sheafify _ (presheaf X n)) ⊤ x trivial _ =
    TopCat.Presheaf.germ (sheafify _ (presheaf X n)) ⊤ x trivial _ ↔ _
  rw [globalCochainsToSheaf_apply, globalCochainsToSheaf_apply,
    SheafCohomology.toSheafify_germ_eq_iff]
  constructor
  · rintro ⟨V, hV, hxV, he⟩
    exact ⟨V, hxV, by simpa only [restrict_top_cochain] using he⟩
  · rintro ⟨V, hxV, he⟩
    exact ⟨V, le_top, hxV, by simpa only [restrict_top_cochain] using he⟩

theorem exists_global_cochain_local_lift (n : ℕ)
    (s : (cochainSheaf X n).obj.obj (op ⊤)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ φ : (complexCochains X).X n,
      (cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
          ((globalCochainsToSheaf X).f n φ) =
        (cochainSheaf X n).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  obtain ⟨U, hU, hxU, t, ht⟩ :=
    SheafCohomology.toSheafify_exists_local_lift (presheaf X n) ⊤ s x trivial
  refine ⟨U, hxU, openExtension X U n t, ?_⟩
  rw [globalCochainsToSheaf_restrict, pullback_openExtension]
  exact ht

/-- The native complex-valued global sheafification unit is degreewise surjective. -/
theorem globalCochainsToSheaf_surjective [ParacompactSpace X] [T2Space X] (n : ℕ) :
    Function.Surjective ((globalCochainsToSheaf X).f n) := by
  classical
  intro s
  choose U hxU φ hφ using exists_global_cochain_local_lift X n s
  obtain ⟨C, hclosed, hfinite, hcover, hCU⟩ :=
    SingularCochains.exists_locallyFinite_closed_refinement X U
      (SingularCochains.point_cover_eq_univ X U hxU)
  have hg (x i : X) (hi : x ∈ C i) :
      TopCat.Presheaf.germ (cochainSheaf X n).obj ⊤ x trivial
          ((globalCochainsToSheaf X).f n (φ i)) =
        TopCat.Presheaf.germ (cochainSheaf X n).obj ⊤ x trivial s := by
    rw [← TopCat.Presheaf.germ_res_apply (cochainSheaf X n).obj
        (homOfLE (show U i ≤ ⊤ from le_top)) x (hCU i hi)
        ((globalCochainsToSheaf X).f n (φ i)),
      ← TopCat.Presheaf.germ_res_apply (cochainSheaf X n).obj
        (homOfLE (show U i ≤ ⊤ from le_top)) x (hCU i hi) s, hφ i]
  obtain ⟨ψ, hψ⟩ := exists_cochain_locally_eq_of_closed_cover X C hclosed hfinite hcover n φ
    (fun x i j hi hj ↦ (globalCochainsToSheaf_germ_eq_iff X n (φ i) (φ j) x).mp
      ((hg x i hi).trans (hg x j hj).symm))
  refine ⟨ψ, ?_⟩
  apply TopCat.Presheaf.section_ext (cochainSheaf X n) ⊤
  intro x _
  obtain ⟨i, hi⟩ := hcover x
  exact ((globalCochainsToSheaf_germ_eq_iff X n ψ (φ i) x).mpr (hψ x i hi)).trans (hg x i hi)

/-- The native global unit is a quasi-isomorphism on paracompact Hausdorff spaces. -/
theorem globalCochainsToSheaf_quasiIso [ParacompactSpace X] [T2Space X] :
    QuasiIso (globalCochainsToSheaf X) :=
  SheafCohomology.ComplexKernel.quasiIso_of_surjective_of_acyclic (globalCochainsToSheaf X)
    (globalCochainsToSheaf_surjective X) (sheafificationKernel_acyclic X)

end HodgeConjecture.SingularCoefficientChange
