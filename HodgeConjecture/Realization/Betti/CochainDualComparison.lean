module

public import HodgeConjecture.Realization.Betti.CochainDualCoordinates
public import HodgeConjecture.Realization.Betti.RationalDual
public import HodgeConjecture.Realization.Betti.SmallSingularComparison

@[expose] public section

/-!
# Exact rational dualization identifies actual singular cochains

The algebraic dual of Mathlib's original rational chain complex is
identified, on actual generators and differentials, with the already
constructed unrestricted simplex-function cochains. The comparison is
natural for original simplicial maps. Exact dualization therefore carries
the proved small-chain inclusion to the actual cochain restriction
quasi-isomorphism for a genuine two-open cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CochainDualComparison

open CategoryTheory Opposite Simplicial HomologicalComplex

/-- The dual complex agrees with original simplex-function cochains, degree by degree
and with the original alternating differential. -/
def comparisonIso (S : SSet.{0}) :
    RationalDual.dualComplex (SingularChainCoordinates.complex S) ≅ SubcomplexCochains.complex S :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CochainDualCoordinates.coordinates S n).toModuleIso) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      rw [SubcomplexCochains.complex_d, RationalDual.dualComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      change SubcomplexCochains.differential S i (CochainDualCoordinates.coordinates S i φ) =
        CochainDualCoordinates.coordinates S (i + 1)
          (((SingularChainCoordinates.complex S).d (i + 1) i).hom.dualMap φ)
      exact (CochainDualCoordinates.coordinates_differential S i φ).symm)

@[simp]
theorem comparisonIso_hom_f_apply (S : SSet.{0}) (n : ℕ)
    (φ : Module.Dual ℚ ((SingularChainCoordinates.complex S).X n)) :
    (comparisonIso S).hom.f n φ = CochainDualCoordinates.coordinates S n φ := rfl

/-- The naturality square uses the original native chain map and the actual cochain pullback. -/
theorem comparisonIso_naturality {S T : SSet.{0}} (f : S ⟶ T) :
    RationalDual.dualMap (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)) ≫ (comparisonIso S).hom =
      (comparisonIso T).hom ≫ SubcomplexCochains.pullback f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  change CochainDualCoordinates.coordinates S n
    (((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n).hom.dualMap φ) = _
  exact CochainDualCoordinates.coordinates_naturality f n φ

/-- The actual cochain map is the proved conjugate of the actual dual chain map. -/
theorem pullback_eq_dualMap {S T : SSet.{0}} (f : S ⟶ T) :
    SubcomplexCochains.pullback f =
      (comparisonIso T).inv ≫ RationalDual.dualMap (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)) ≫
        (comparisonIso S).hom := by
  have h := congrArg (fun g ↦ (comparisonIso T).inv ≫ g) (comparisonIso_naturality f)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

/-- Exact rational dualization transfers genuine chain quasi-isomorphisms to the original
cochain pullback, without finite-dimensionality assumptions. -/
theorem pullback_quasiIso {S T : SSet.{0}} (f : S ⟶ T)
    [QuasiIso (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ))] :
    QuasiIso (SubcomplexCochains.pullback f) := by
  rw [pullback_eq_dualMap]
  infer_instance

/-- Restriction from the original full singular cochain complex to actual small cochains. -/
def smallRestriction (X : TopCat.{0}) (U V : Set X) :
    SingularCochains.complex X ⟶
      SubcomplexCochains.complex (SingularSubcomplexes.smallSingular X U V).toSSet :=
  SubcomplexCochains.pullback (SingularSubcomplexes.smallSingular X U V).ι

@[simp]
theorem smallRestriction_apply (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (φ : SingularCochains.Cochain X n)
    (σ : (SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) :
    (smallRestriction X U V).f n φ σ = φ σ.val := rfl

/-- The original actual singular restriction is a quasi-isomorphism for a genuine two-open
cover. The chain comparison is proved by constructed subdivision, not supplied as a premise. -/
theorem smallRestriction_quasiIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (smallRestriction X U V) := by
  exact @pullback_quasiIso _ _ (SingularSubcomplexes.smallSingular X U V).ι
    (SmallSingularComparison.inclusion_quasiIso X U V hU hV hcover)

/-- The resulting cohomology comparison is fixed by the original restriction map. -/
def smallCohomologyIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularCochains.Cohomology X n ≅
      (SubcomplexCochains.complex (SingularSubcomplexes.smallSingular X U V).toSSet).homology n := by
  letI := smallRestriction_quasiIso X U V hU hV hcover
  exact isoOfQuasiIsoAt (smallRestriction X U V) n

@[simp]
theorem smallCohomologyIso_hom (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallCohomologyIso X U V hU hV hcover n).hom =
      homologyMap (smallRestriction X U V) n := rfl

end HodgeConjecture.CochainDualComparison
