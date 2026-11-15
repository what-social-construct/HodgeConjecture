module

public import HodgeConjecture.Geometry.Holomorphic.SchemeEvaluation
public import HodgeConjecture.Realization.DeRham.HolomorphicAtlasComplex
public import HodgeConjecture.Realization.DeRham.HolomorphicAtlasPoincare
public import HodgeConjecture.Realization.DeRham.HolomorphicFormsDifferential
public import HodgeConjecture.Realization.DeRham.SheafComplex

@[expose] public section

/-!
# Algebraic forms on the canonical analytic atlas

The original section algebras, their actual Kähler exterior powers, and
the constructed regular evaluation maps supply holomorphic forms in
every chart. Proved coordinate naturality glues these into the intrinsic
atlas sheaf. The map commutes with the original de Rham differential.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The native restriction ring homomorphism, retaining its constant scalar action. -/
def functionsRestriction {U V : Opens E} (h : U ≤ V) : Functions V →ₐ[ℂ] Functions U :=
  { ContMDiffMap.restrictRingHom 𝓘(ℂ, E) 𝓘(ℂ) ℂ h with commutes' _ := rfl }

end HodgeConjecture.HolomorphicDeRham

namespace AlgebraicGeometry.Scheme.ComplexPoints

open CategoryTheory TopologicalSpace KaehlerDifferential
open scoped Manifold ContDiff
open HodgeConjecture
open HolomorphicForms HolomorphicDeRham

variable {X : Scheme.{0}} {x : X ⟶ Spec (.of ℂ)} (d : ℕ) [SmoothOfRelativeDimension d x]

/-- Algebraic forms realized in a chart of the actual scheme atlas. -/
def chartFormsMap (U : X.Opens) (n : ℕ) (e : HolomorphicAtlas.Chart (Fin d → ℂ) (ComplexPoints x)) :
    letI := regularFunctionsAlgebra (x := x) U
    ⋀[Γ(X, U)]^n Ω[Γ(X, U)⁄ℂ] →ₗ[ℂ]
      Sections (HolomorphicAtlas.domain e (analyticOpen (x := x) U)) n := by
  letI := regularFunctionsAlgebra (x := x) U
  exact algebraicFormsMap (chartDomain d e.1 U) (chartEvaluation d e.1 e.2 U) n

/-- These actual chartwise maps satisfy the derivative descent equation. -/
theorem chartFormsMap_compatible (U : X.Opens) (n : ℕ)
    (η : letI := regularFunctionsAlgebra (x := x) U; ⋀[Γ(X, U)]^n Ω[Γ(X, U)⁄ℂ]) :
    (fun e ↦ chartFormsMap d U n e η) ∈
      HolomorphicAtlas.compatibleSubmodule (E := Fin d → ℂ) (analyticOpen (x := x) U) n := by
  let := regularFunctionsAlgebra (x := x) U
  intro e e'
  let φ := chartEvaluation d e.1 e.2 U
  let ψ := chartEvaluation d e'.1 e'.2 U
  let h := HolomorphicAtlas.overlap_le e e' (analyticOpen (x := x) U)
  let θ := (functionsRestriction h).comp φ
  have hr := algebraicFormsMap_restrict h φ θ (fun _ _ ↦ rfl) n
  have hp := algebraicFormsMap_pullback (HolomorphicAtlas.transition e e')
    (HolomorphicAtlas.transition_contDiffOn e e' (analyticOpen (x := x) U))
    (HolomorphicAtlas.transition_mapsTo e e' (analyticOpen (x := x) U)) ψ θ (by
      intro a z
      change eval a (e.1.symm z.1) z.2.2.1 =
        eval a (e'.1.symm (e'.1 (e.1.symm z.1)))
          (HolomorphicAtlas.transition_mapsTo e e' (analyticOpen (x := x) U) z.2).2
      congr 1
      exact (e'.1.left_inv z.2.2.2).symm) n
  exact (LinearMap.congr_fun hr η).trans (LinearMap.congr_fun hp η).symm

/-- The all-degree map from the original algebraic forms to the descended analytic sheaf. -/
def algebraicFormsMap (U : X.Opens) (n : ℕ) :
    letI := regularFunctionsAlgebra (x := x) U
    ⋀[Γ(X, U)]^n Ω[Γ(X, U)⁄ℂ] →ₗ[ℂ]
      HolomorphicAtlas.Forms (Fin d → ℂ) (analyticOpen (x := x) U) n := by
  letI := regularFunctionsAlgebra (x := x) U
  exact {
    toFun η := ⟨fun e ↦ chartFormsMap d U n e η, chartFormsMap_compatible d U n η⟩
    map_add' η ξ := Subtype.ext (funext fun e ↦ map_add (chartFormsMap d U n e) η ξ)
    map_smul' c η := Subtype.ext (funext fun e ↦ map_smul (chartFormsMap d U n e) c η) }

@[simp]
theorem algebraicFormsMap_inChart (U : X.Opens) (n : ℕ)
    (η : letI := regularFunctionsAlgebra (x := x) U; ⋀[Γ(X, U)]^n Ω[Γ(X, U)⁄ℂ])
    (e : HolomorphicAtlas.Chart (Fin d → ℂ) (ComplexPoints x)) :
    HolomorphicAtlas.inChart (analyticOpen (x := x) U) n e (algebraicFormsMap d U n η) =
      chartFormsMap d U n e η := rfl

/-- The descended map commutes with the original algebraic and analytic differentials. -/
theorem algebraicFormsMap_differential (U : X.Opens) (n : ℕ) :
    letI := regularFunctionsAlgebra (x := x) U
    (HolomorphicAtlas.differential (analyticOpen (x := x) U) n).comp (algebraicFormsMap d U n) =
      (algebraicFormsMap d U (n + 1)).comp (deRhamDifferential (A := ℂ) n) := by
  let := regularFunctionsAlgebra (x := x) U
  apply LinearMap.ext
  intro η
  apply Subtype.ext
  funext e
  exact LinearMap.congr_fun (HolomorphicDeRham.algebraicFormsMap_differential
    (chartDomain d e.1 U) (chartEvaluation d e.1 e.2 U) n) η

/-- Restriction uses the same original section algebra maps as scheme de Rham. -/
theorem algebraicFormsMap_restrict {U V : X.Opens} (h : V ≤ U) (n : ℕ) :
    letI := regularFunctionsAlgebra (x := x) U
    letI := regularFunctionsAlgebra (x := x) V
    (HolomorphicAtlas.restrict (analyticOpen_mono h) n).comp (algebraicFormsMap d U n) =
      (algebraicFormsMap d V n).comp
        (AlgebraDeRham.formsMap ℂ (SchemeDeRham.sectionMap ℂ X x (homOfLE h)) n) := by
  let := regularFunctionsAlgebra (x := x) U
  let := regularFunctionsAlgebra (x := x) V
  apply LinearMap.ext
  intro η
  apply Subtype.ext
  funext e
  let f := SchemeDeRham.sectionMap ℂ X x (homOfLE h)
  let φ := chartEvaluation d e.1 e.2 U
  let ψ := chartEvaluation d e.1 e.2 V
  have hr := HolomorphicDeRham.algebraicFormsMap_restrict
    (HolomorphicAtlas.domain_mono e (analyticOpen_mono h)) φ (ψ.comp f)
    (fun a z ↦ eval_map h a (e.1.symm z.1) z.2.2) n
  exact (LinearMap.congr_fun hr η).trans
    (LinearMap.congr_fun (algebraicFormsMap_precomp (chartDomain d e.1 V) f ψ n) η).symm

/-- The actual analytic opens as a functor from the original scheme opens. -/
def analyticOpensFunctor : X.Opens ⥤ TopologicalSpace.Opens (ComplexPoints x) where
  obj U := analyticOpen (x := x) U
  map i := homOfLE (analyticOpen_mono (leOfHom i))

/-- The descended analytic forms evaluated on the original algebraic opens. -/
def analyticFormsPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℂ) X :=
  (analyticOpensFunctor (x := x)).op ⋙
    (HolomorphicAtlas.formsSheaf (Fin d → ℂ) (ComplexPoints x) n).obj

/-- All degrees form a natural transformation from the original algebraic forms presheaf. -/
def algebraicFormsComparison (n : ℕ) :
    SchemeDeRham.formsPresheaf ℂ X x n ⟶ analyticFormsPresheaf (x := x) d n where
  app U := ModuleCat.ofHom (algebraicFormsMap (x := x) d U.unop n)
  naturality _ _ i := by
    apply ModuleCat.hom_ext
    exact (algebraicFormsMap_restrict d (leOfHom i.unop) n).symm

theorem algebraicFormsComparison_differential (n : ℕ) :
    algebraicFormsComparison (x := x) d n ≫
      Functor.whiskerLeft (analyticOpensFunctor (x := x)).op
        (HolomorphicAtlas.sheafDifferential (E := Fin d → ℂ) (M := ComplexPoints x) n).hom =
    (SchemeDeRham.presheafComplex ℂ X x).d n (n + 1) ≫ algebraicFormsComparison (x := x) d (n + 1) := by
  rw [SchemeDeRham.presheafComplex_d]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  exact algebraicFormsMap_differential d U.unop n

/-- The actual intrinsic analytic complex, evaluated on the original algebraic opens. -/
def analyticPresheafComplex : CochainComplex (TopCat.Presheaf (ModuleCat.{0} ℂ) X) ℕ :=
  CochainComplex.of (analyticFormsPresheaf (x := x) d)
    (fun n ↦ Functor.whiskerLeft (analyticOpensFunctor (x := x)).op
      (HolomorphicAtlas.sheafDifferential (E := Fin d → ℂ) (M := ComplexPoints x) n).hom)
    (fun n ↦ by
      apply NatTrans.ext
      funext U
      exact ModuleCat.hom_ext (HolomorphicAtlas.differential_comp (E := Fin d → ℂ) (analyticOpen (x := x) U.unop) n))

/-- A genuine morphism from the existing scheme algebraic de Rham presheaf complex. -/
def algebraicComplexComparison :
    SchemeDeRham.presheafComplex ℂ X x ⟶ analyticPresheafComplex (x := x) d where
  f n := algebraicFormsComparison (x := x) d n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    simp only [analyticPresheafComplex, CochainComplex.of_d]
    exact algebraicFormsComparison_differential (x := x) d i

/-- The actual constant-to-holomorphic comparison on the original analytic scheme points. -/
def holomorphicComparison :
    (CochainComplex.single₀ _).obj (HolomorphicAtlas.constantSheaf (ComplexPoints x)) ⟶
      HolomorphicAtlas.complex (Fin d → ℂ) (ComplexPoints x) :=
  HolomorphicAtlas.comparison (Fin d → ℂ) (ComplexPoints x)

/-- Intrinsic Poincaré comparison in every degree on a smooth fixed-dimension scheme. -/
theorem holomorphicComparison_quasiIso : QuasiIso (holomorphicComparison (x := x) d) :=
  HolomorphicAtlas.comparison_quasiIso (Fin d → ℂ) (ComplexPoints x)

end AlgebraicGeometry.Scheme.ComplexPoints
