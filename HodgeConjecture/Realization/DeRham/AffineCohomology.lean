module

public import HodgeConjecture.Realization.DeRham.AffineDegreeZero
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Cohomology of the actual affine Kähler de Rham complex

In every degree, closed exterior forms are quotiented by the actual incoming
differential. This concrete quotient is canonically identified with categorical
homology of the existing deRhamComplex. Degree zero retains the existing
closed-function coordinates. No analytic comparison is supplied.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open CategoryTheory KaehlerDifferential

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- Closed forms for the original de Rham differential. -/
def closedForms (n : ℕ) : Submodule k (⋀[A]^n Ω[A⁄k]) :=
  LinearMap.ker (deRhamDifferential (A := k) (B := A) n)

instance closedFormsAddCommGroup (n : ℕ) : AddCommGroup (closedForms k A n) :=
  (closedForms k A n).addCommGroup

instance closedFormsModule (n : ℕ) : Module k (closedForms k A n) :=
  (closedForms k A n).module

@[simp]
theorem mem_closedForms (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    ω ∈ closedForms k A n ↔ deRhamDifferential (A := k) n ω = 0 := Iff.rfl

/-- The actual incoming differential, with its image proved closed by d²=0. -/
def differentialToClosedForms (n : ℕ) :
    (⋀[A]^n Ω[A⁄k]) →ₗ[k] closedForms k A (n + 1) :=
  (deRhamDifferential (A := k) n).codRestrict _
    (fun ω ↦ deRhamDifferential_comp_self n ω)

@[simp]
theorem differentialToClosedForms_val (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    (differentialToClosedForms k A n ω).val = deRhamDifferential (A := k) n ω := rfl

/-- Exact forms inside the closed forms. There is no incoming degree at zero. -/
def exactForms : (n : ℕ) → Submodule k (closedForms k A n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (differentialToClosedForms k A n)

@[simp]
theorem exactForms_zero : exactForms k A 0 = ⊥ := rfl

@[simp]
theorem exactForms_succ (n : ℕ) :
    exactForms k A (n + 1) = LinearMap.range (differentialToClosedForms k A n) := rfl

/-- Affine algebraic de Rham cohomology, as the actual closed/exact quotient. -/
abbrev Cohomology (n : ℕ) := (closedForms k A n) ⧸ exactForms k A n

/-- Passage from a closed form to its actual cohomology class. -/
def cohomologyClass (n : ℕ) : closedForms k A n →ₗ[k] Cohomology k A n :=
  (exactForms k A n).mkQ

theorem cohomologyClass_surjective (n : ℕ) :
    Function.Surjective (cohomologyClass k A n) := Submodule.mkQ_surjective _

@[simp]
theorem cohomologyClass_eq_zero_iff (n : ℕ) (ω : closedForms k A n) :
    cohomologyClass k A n ω = 0 ↔ ω ∈ exactForms k A n :=
  Submodule.Quotient.mk_eq_zero _

theorem cohomologyClass_eq_iff (n : ℕ) (ω η : closedForms k A n) :
    cohomologyClass k A n ω = cohomologyClass k A n η ↔ ω - η ∈ exactForms k A n :=
  Submodule.Quotient.eq _

@[simp]
theorem cohomologyClass_differential (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    cohomologyClass k A (n + 1) (differentialToClosedForms k A n ω) = 0 :=
  (cohomologyClass_eq_zero_iff k A _ _).mpr ⟨ω, rfl⟩

/-- Positive-degree exactness retains an actual primitive in the original form module. -/
theorem cohomologyClass_succ_eq_zero_iff (n : ℕ) (ω : closedForms k A (n + 1)) :
    cohomologyClass k A (n + 1) ω = 0 ↔
      ∃ η : ⋀[A]^n Ω[A⁄k], deRhamDifferential (A := k) n η = ω.val := by
  rw [cohomologyClass_eq_zero_iff, exactForms_succ, LinearMap.mem_range]
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η, congrArg Subtype.val hη⟩
  · rintro ⟨η, hη⟩
    exact ⟨η, Subtype.ext hη⟩

/-- The old degree-zero calculation is unchanged by the all-degree quotient. -/
def cohomologyZeroCoordinates : Cohomology k A 0 ≃ₗ[k] H0 k A :=
  ((exactForms k A 0).quotEquivOfEqBot rfl).trans (kernelCoordinates k A)

def differentialShortComplex (n : ℕ) : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk (deRhamDifferential (A := k) (B := A) n)
    (deRhamDifferential (A := k) (B := A) (n + 1))
    (deRhamDifferential_comp_deRhamDifferential n)

def differentialShortComplexIso (n : ℕ) :
    (deRhamComplex k A).sc' n (n + 1) ((n + 1) + 1) ≅ differentialShortComplex k A n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [differentialShortComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', deRhamComplex_d, Category.id_comp, Category.comp_id])
    (by simp [differentialShortComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', deRhamComplex_d, Category.id_comp, Category.comp_id])

/-- The explicit quotient is the categorical homology of the original de Rham complex. -/
def cohomologyIso : (n : ℕ) →
    (deRhamComplex k A).homology n ≅ ModuleCat.of k (Cohomology k A n)
  | 0 => cohomologyZeroIso k A ≪≫ (cohomologyZeroCoordinates k A).symm.toModuleIso
  | n + 1 =>
    (deRhamComplex k A).homologyIsoSc' n (n + 1) ((n + 1) + 1)
        (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1)) ≪≫
      ShortComplex.homologyMapIso (differentialShortComplexIso k A n) ≪≫
        (differentialShortComplex k A n).moduleCatHomologyIso

end

end HodgeConjecture.AffineDeRham
