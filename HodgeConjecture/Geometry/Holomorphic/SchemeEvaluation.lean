module

public import HodgeConjecture.Geometry.SmoothComplexManifold
public import HodgeConjecture.Geometry.SectionAlgebra
public import HodgeConjecture.Geometry.Holomorphic.Forms

@[expose] public section

/-!
# Actual regular functions as holomorphic functions

The canonical analytic atlas makes every original regular-function
evaluation holomorphic. The maps below use the original section rings,
their existing constant ring map and native bundled complex C∞ maps.
They also give the actual algebra map on a coordinate chart needed by
the existing Kähler realization, with no supplied evaluation hypothesis.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace AlgebraicGeometry.Scheme.ComplexPoints

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

variable {X : Scheme.{0}} {x : X ⟶ Spec (.of ℂ)}

/-- The analytic open determined by an original scheme open. -/
def analyticOpen (U : X.Opens) : TopologicalSpace.Opens (ComplexPoints x) :=
  ⟨{p | p.Mem U}, isOpen_setOf_mem U⟩

theorem analyticOpen_mono {U V : X.Opens} (h : V ≤ U) :
    analyticOpen (x := x) V ≤ analyticOpen U := fun _ hp ↦ hp.mono h

/-- The original structure morphism's constants, as the scalar structure on the same section ring. -/
@[instance_reducible]
def regularFunctionsAlgebra (U : X.Opens) : Algebra ℂ Γ(X, U) :=
  HodgeConjecture.SchemeDeRham.sectionAlgebra ℂ X x U

variable (d : ℕ) [SmoothOfRelativeDimension d x]

/-- The actual evaluation function as an existing bundled holomorphic function. -/
def regularEvaluationFunction (U : X.Opens) (g : Γ(X, U)) :
    C^∞⟮𝓘(ℂ, Fin d → ℂ), analyticOpen (x := x) U; 𝓘(ℂ), ℂ⟯ :=
  ⟨fun (p : analyticOpen (x := x) U) ↦ eval g p.1 p.2, by
    have hg := (contMDiffOn_evalOrZero (c := x) d U g).of_le (by simp : (∞ : WithTop ℕ∞) ≤ ω)
    have hs : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ∞
        (fun p : analyticOpen (x := x) U ↦ evalOrZero (z := x) U g p.1) := by
      intro p
      exact contMDiffAt_subtype_iff.mpr
        ((hg p.1 p.2).contMDiffAt ((analyticOpen (x := x) U).isOpen.mem_nhds p.2))
    exact hs.congr (fun p ↦ (evalOrZero_of_mem g p.2).symm)⟩

/-- Original regular-function evaluation on its actual analytic open. -/
def regularEvaluation (U : X.Opens) :
    letI : Algebra ℂ Γ(X, U) := regularFunctionsAlgebra (x := x) U
    Γ(X, U) →ₐ[ℂ] C^∞⟮𝓘(ℂ, Fin d → ℂ), analyticOpen (x := x) U; 𝓘(ℂ), ℂ⟯ := by
  letI : Algebra ℂ Γ(X, U) := regularFunctionsAlgebra (x := x) U
  exact {
    toFun := regularEvaluationFunction (x := x) d U
    map_one' := by apply ContMDiffMap.ext; intro p; exact (evalHom p.1 p.2).map_one
    map_mul' g h := by apply ContMDiffMap.ext; intro p; exact (evalHom p.1 p.2).map_mul g h
    map_zero' := by apply ContMDiffMap.ext; intro p; exact (evalHom p.1 p.2).map_zero
    map_add' g h := by apply ContMDiffMap.ext; intro p; exact (evalHom p.1 p.2).map_add g h
    commutes' c := by apply ContMDiffMap.ext; intro p; exact eval_constHom (y := x) c p.1 p.2
  }

@[simp]
theorem regularEvaluation_apply (U : X.Opens) (g : Γ(X, U)) (p : analyticOpen (x := x) U) :
    regularEvaluation (x := x) d U g p = eval g p.1 p.2 := rfl

/-- Evaluation commutes with the original restriction map of the section sheaf. -/
theorem regularEvaluation_restrict {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U)) :
    regularEvaluation (x := x) d V (X.presheaf.map (homOfLE h).op g) =
      (ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ℂ (analyticOpen_mono h))
        (regularEvaluation (x := x) d U g) := by
  apply ContMDiffMap.ext
  intro p
  exact eval_map h g p.1 p.2

/-- The coordinate part of an analytic chart on which an original regular section is defined. -/
def chartDomain (e : OpenPartialHomeomorph (ComplexPoints x) (Fin d → ℂ)) (U : X.Opens) :
    TopologicalSpace.Opens (Fin d → ℂ) :=
  ⟨e.target ∩ e.symm ⁻¹' {p | p.Mem U}, e.isOpen_inter_preimage_symm (isOpen_setOf_mem U)⟩

/-- The actual regular evaluation algebra map in any chart of the constructed atlas. -/
def chartEvaluation (e : OpenPartialHomeomorph (ComplexPoints x) (Fin d → ℂ))
    (he : e ∈ atlas (Fin d → ℂ) (ComplexPoints x)) (U : X.Opens) :
    letI : Algebra ℂ Γ(X, U) := regularFunctionsAlgebra (x := x) U
    Γ(X, U) →ₐ[ℂ] C^∞⟮𝓘(ℂ, Fin d → ℂ), chartDomain d e U; 𝓘(ℂ), ℂ⟯ := by
  letI : Algebra ℂ Γ(X, U) := regularFunctionsAlgebra (x := x) U
  exact {
    toFun g := ⟨fun z ↦ eval g (e.symm z) z.2.2, by
      have hg := ((isAlgebraicChart_of_mem_atlas d he).2 U g).of_le
        (by simp : (∞ : WithTop ℕ∞) ≤ ω)
      have hs : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ∞
          (fun z : chartDomain d e U ↦ evalOrZero U g (e.symm z)) :=
        HodgeConjecture.HolomorphicForms.contMDiff_restrict
          (fun _ hz ↦ hg.contDiffAt ((chartDomain d e U).isOpen.mem_nhds hz))
      exact hs.congr (fun z ↦ (evalOrZero_of_mem g z.2.2).symm)⟩
    map_one' := by apply ContMDiffMap.ext; intro p; exact (evalHom (e.symm p) p.2.2).map_one
    map_mul' g h := by apply ContMDiffMap.ext; intro p; exact (evalHom (e.symm p) p.2.2).map_mul g h
    map_zero' := by apply ContMDiffMap.ext; intro p; exact (evalHom (e.symm p) p.2.2).map_zero
    map_add' g h := by apply ContMDiffMap.ext; intro p; exact (evalHom (e.symm p) p.2.2).map_add g h
    commutes' c := by apply ContMDiffMap.ext; intro p; exact eval_constHom c (e.symm p) p.2.2
  }

@[simp]
theorem chartEvaluation_apply (e : OpenPartialHomeomorph (ComplexPoints x) (Fin d → ℂ))
    (he : e ∈ atlas (Fin d → ℂ) (ComplexPoints x)) (U : X.Opens) (g : Γ(X, U))
    (p : chartDomain d e U) : chartEvaluation d e he U g p = eval g (e.symm p) p.2.2 := rfl

/-- Chartwise and intrinsic evaluation retain exactly the same value at the original point. -/
theorem chartEvaluation_eq_regularEvaluation (e : OpenPartialHomeomorph (ComplexPoints x) (Fin d → ℂ))
    (he : e ∈ atlas (Fin d → ℂ) (ComplexPoints x)) (U : X.Opens) (g : Γ(X, U))
    (p : chartDomain d e U) :
    chartEvaluation d e he U g p = regularEvaluation (x := x) d U g ⟨e.symm p, p.2.2⟩ := rfl

/-- Evaluation pullback is the actual pullback of regular functions under a scheme morphism. -/
theorem regularEvaluation_map (e : ℕ) {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension e y] (φ : X ⟶ Y) (hφ : φ ≫ y = x)
    (U : Y.Opens) (g : Γ(Y, U)) (p : analyticOpen (x := x) (φ ⁻¹ᵁ U)) :
    regularEvaluation (x := x) d (φ ⁻¹ᵁ U) (φ.app U g) p =
      regularEvaluation (x := y) e U g ⟨map φ hφ p.1, p.2⟩ := by
  exact (eval_map_point φ hφ g p.1 p.2).symm

end AlgebraicGeometry.Scheme.ComplexPoints
