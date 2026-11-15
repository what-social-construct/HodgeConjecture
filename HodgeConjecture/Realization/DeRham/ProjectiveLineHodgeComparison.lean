module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration
public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison
public import HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
public import HodgeConjecture.Realization.DeRham.BettiHodgeTarget

@[expose] public section

/-!
# The geometric degree-two Hodge filtration on the projective-line Betti tensor

The original derived degree filtration is carried through the constructed
boundary-period equivalence to the genuine complexification of actual
rational singular H². Its computed images agree with the independently
specified weight-two Betti filtration. Intersecting the actual transported
filtration with its canonical rational conjugate recovers type (1,1).

No cycle map is used to define these geometric pieces or their rational
inverse image. This is a bounded computation for the constructed P¹ period
comparison, not a general analytic/Gysin comparison or degeneration theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineHodgeComparison

open CategoryTheory TensorProduct ProjectiveLineBettiComplexification

private theorem map_filtration (e : ProjectiveLineDeRham.SchemeH2 ℂ ≃ₗ[ℂ] Complexification)
    (p : ℤ) :
    (ProjectiveLineDeRham.hodgeFiltration ℂ p).map e.toLinearMap =
      ProjectiveLineHodgeStructure.filtration p := by
  by_cases hp : p ≤ 1
  · rw [ProjectiveLineDeRham.hodgeFiltration_eq_top ℂ p hp,
      ProjectiveLineHodgeStructure.filtration_eq_top p hp, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  · rw [ProjectiveLineDeRham.hodgeFiltration_eq_bot ℂ p (by omega), Submodule.map_bot,
      ProjectiveLineHodgeStructure.filtration_eq_bot p (by omega)]

/-- The actual unnormalized period equivalence preserves the independently constructed filtrations. -/
theorem comparison_map_hodgeFiltration (p : ℤ) :
    (ProjectiveLineDeRham.hodgeFiltration ℂ p).map
        ProjectiveLinePeriodComparison.comparison.toLinearMap =
      ProjectiveLineHodgeStructure.filtration p :=
  map_filtration ProjectiveLinePeriodComparison.comparison p

/-- The same statement holds with the original 2πi period divided out. -/
theorem normalizedComparison_map_hodgeFiltration (p : ℤ) :
    (ProjectiveLineDeRham.hodgeFiltration ℂ p).map
        ProjectiveLinePeriodComparison.normalizedComparison.toLinearMap =
      ProjectiveLineHodgeStructure.filtration p :=
  map_filtration ProjectiveLinePeriodComparison.normalizedComparison p

/-- The actual geometric Hodge filtration, transported by the original boundary-period map. -/
def geometricFiltration (p : ℤ) : Submodule ℂ Complexification :=
  (ProjectiveLineDeRham.hodgeFiltration ℂ p).map
    ProjectiveLinePeriodComparison.comparison.toLinearMap

/-- Its agreement with the independently defined Betti decomposition is proved. -/
theorem geometricFiltration_eq (p : ℤ) :
    geometricFiltration p = ProjectiveLineHodgeStructure.filtration p :=
  comparison_map_hodgeFiltration p

theorem geometricFiltration_antitone : Antitone geometricFiltration := by
  intro p q hpq
  rw [geometricFiltration_eq, geometricFiltration_eq]
  exact ProjectiveLineHodgeStructure.filtration_antitone hpq

/-- Membership is retained along the actual filtered period isomorphism in both directions. -/
theorem comparison_mem_geometricFiltration (p : ℤ) (z : ProjectiveLineDeRham.SchemeH2 ℂ) :
    ProjectiveLinePeriodComparison.comparison z ∈ geometricFiltration p ↔
      z ∈ ProjectiveLineDeRham.hodgeFiltration ℂ p := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hwz : w = z := ProjectiveLinePeriodComparison.comparison.injective he
    change w ∈ ProjectiveLineDeRham.hodgeFiltration ℂ p at hw
    rw [hwz] at hw
    exact hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The geometric filtration is opposed to its canonical rational conjugate in weight two. -/
theorem geometricFiltration_opposed (p : ℤ) :
    IsCompl (geometricFiltration p)
      (ProjectiveLineHodgeStructure.conjugateSubmodule (geometricFiltration (3 - p))) := by
  simp only [geometricFiltration_eq]
  exact ProjectiveLineHodgeStructure.filtration_opposed p

/-- Weight-two pieces recovered from the actual geometric filtration and rational conjugation. -/
def geometricHodgePiece (p q : ℤ) : Submodule ℂ Complexification :=
  if p + q = 2 then
    geometricFiltration p ⊓ ProjectiveLineHodgeStructure.conjugateSubmodule (geometricFiltration q)
  else ⊥

/-- The actual geometric recovery agrees with the independently specified pure Hodge decomposition. -/
theorem geometricHodgePiece_eq_bigrading (p q : ℤ) :
    geometricHodgePiece p q = ProjectiveLineHodgeStructure.bigrading p q := by
  by_cases h : p + q = 2
  · rw [geometricHodgePiece, ite_eq_left h, geometricFiltration_eq, geometricFiltration_eq]
    exact (ProjectiveLineHodgeStructure.bigrading_eq_filtration_inf_conjugate p q h).symm
  · rw [geometricHodgePiece, ite_eq_right h,
      ProjectiveLineHodgeStructure.bigrading_pure_weight_two p q h]

@[simp]
theorem geometricHodgePiece_one_one : geometricHodgePiece 1 1 = ⊤ := by
  rw [geometricHodgePiece_eq_bigrading, ProjectiveLineHodgeStructure.bigrading_one_one]

theorem geometricHodgePiece_eq_bot (p q : ℤ) (h : ¬ (p = 1 ∧ q = 1)) :
    geometricHodgePiece p q = ⊥ := by
  rw [geometricHodgePiece_eq_bigrading, ProjectiveLineHodgeStructure.bigrading_eq_bot p q h]

/-- Rational classes are selected by the actual transported geometric type (1,1), independently of cycles. -/
def rationalHodgeClasses : Submodule ℚ Betti :=
  HodgeFiltration.rationalHodgeClasses geometricFiltration 1

/-- The geometric filtration satisfies the full pure weight-two conditions. -/
def pureHodgeStructure : PureRationalHodgeStructure Betti 2 where
  finiteDimensional := inferInstance
  filtration := geometricFiltration
  antitone := geometricFiltration_antitone
  exhaustive := ⟨1, by rw [geometricFiltration_eq]; exact ProjectiveLineHodgeStructure.filtration_one⟩
  separated := ⟨2, by rw [geometricFiltration_eq]; exact ProjectiveLineHodgeStructure.filtration_two⟩
  opposed := geometricFiltration_opposed

/-- The original P¹ target is exactly the target attached to its pure Hodge structure. -/
theorem rationalHodgeClasses_eq_pureStructure :
    rationalHodgeClasses = PureRationalHodgeStructure.rationalHodgeClasses 1 pureHodgeStructure := rfl

/-- The computed P¹ target specializes the general actual scheme-filtration construction. -/
theorem rationalHodgeClasses_eq_schemeTarget :
    rationalHodgeClasses = SchemeDeRham.rationalBettiHodgeClasses
      (AlgebraicGeometry.projectiveLine ℂ ↘ AlgebraicGeometry.Spec (.of ℂ))
      (TopCat.of ProjectiveLineComplexPoints.Point) 2 ProjectiveLinePeriodComparison.comparison 1 := rfl

theorem mem_rationalHodgeClasses (z : Betti) :
    z ∈ rationalHodgeClasses ↔ rationalEmbedding z ∈ geometricHodgePiece 1 1 := Iff.rfl

theorem rationalHodgeClasses_eq_candidate :
    rationalHodgeClasses = ProjectiveLineHodgeStructure.rationalHodgeClasses := by
  ext z
  rw [mem_rationalHodgeClasses, geometricHodgePiece_eq_bigrading]
  rfl

theorem all_rational_hodge (z : Betti) : z ∈ rationalHodgeClasses := by
  rw [mem_rationalHodgeClasses, geometricHodgePiece_one_one]
  trivial

theorem rationalHodgeClasses_eq_top : rationalHodgeClasses = ⊤ :=
  Submodule.eq_top_iff'.mpr all_rational_hodge

/-- The rational condition can also be read in the actual geometric filtration and its conjugate. -/
theorem mem_rationalHodgeClasses_geometricFiltration (z : Betti) :
    z ∈ rationalHodgeClasses ↔
      rationalEmbedding z ∈ geometricFiltration 1 ∧
        ProjectiveLineHodgeStructure.conjugation (rationalEmbedding z) ∈ geometricFiltration 1 := by
  rw [mem_rationalHodgeClasses]
  unfold geometricHodgePiece
  rw [ite_eq_left (by decide : (1 : ℤ) + 1 = 2)]
  rfl

end HodgeConjecture.ProjectiveLineHodgeComparison
