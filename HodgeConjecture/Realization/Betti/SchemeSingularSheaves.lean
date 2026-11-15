module

public import HodgeConjecture.Realization.Betti.Scheme
public import HodgeConjecture.Realization.Betti.SingularSheafResolution
public import HodgeConjecture.Realization.Betti.SingularSheafificationKernel
public import HodgeConjecture.Realization.Betti.SingularSheafGlobalSections
public import HodgeConjecture.Realization.Betti.SingularOpenRestriction
public import HodgeConjecture.Realization.Betti.SingularSheafAcyclicity
public import HodgeConjecture.Realization.Betti.SingularSheafHypercohomology
public import HodgeConjecture.Realization.Betti.SingularConstantSheafCohomology
public import HodgeConjecture.Geometry.SmoothComplexManifold
public import HodgeConjecture.Geometry.LocallyContractible

@[expose] public section

/-!
# The singular sheaf resolution on the canonical scheme point topology

The topology and charted space are the existing ones. The topological
local hypothesis is proved from those charts, rather than supplied as
comparison data. The original rational singular cohomology now identifies
the actual derived cohomology of the original rational constant sheaf,
under the stated point-topology hypotheses. Complex coefficients remain further work.
The native global sheafification kernel is acyclic for every canonical
scheme point space, independently of smoothness or an analytic atlas.
On paracompact Hausdorff canonical point spaces the actual global unit
is now a quasi-isomorphism to termwise sections. The individual flasque
sheaf terms have zero positive derived sections. The original whole-complex
underived-to-derived comparison is now invertible under the proved
flasqueness hypotheses. Composing it with the original global unit and
constant-sheaf resolution gives the constant-sheaf comparison in every degree.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace AlgebraicGeometry.Scheme.ComplexPoints

open CategoryTheory HodgeConjecture

variable {X : Scheme.{0}} {x : X ⟶ Spec (.of ℂ)}

/-- The native kernel on the original canonical scheme point space. -/
abbrev singularSheafificationKernel := SingularCochains.sheafificationKernel (SchemeBetti.space x)

/-- This kernel statement requires no additional geometric hypotheses. -/
theorem singularSheafificationKernel_acyclic : (singularSheafificationKernel (x := x)).Acyclic :=
  SingularCochains.sheafificationKernel_acyclic (SchemeBetti.space x)

/-- Surjectivity of the existing global unit, with explicit point-topology hypotheses. -/
theorem singularGlobalCochainsToSheaf_surjective [ParacompactSpace (ComplexPoints x)]
    [T2Space (ComplexPoints x)] (n : ℕ) :
    Function.Surjective ((SingularCochains.globalCochainsToSheaf (SchemeBetti.space x)).f n) :=
  SingularCochains.globalCochainsToSheaf_surjective (SchemeBetti.space x) n

/-- The map is the original unit; the target still consists of termwise sections. -/
theorem singularGlobalCochainsToSheaf_quasiIso [ParacompactSpace (ComplexPoints x)]
    [T2Space (ComplexPoints x)] :
    QuasiIso (SingularCochains.globalCochainsToSheaf (SchemeBetti.space x)) :=
  SingularCochains.globalCochainsToSheaf_quasiIso (SchemeBetti.space x)

/-- Native flasqueness on the original canonical point topology, with proved-open hypotheses. -/
theorem singularCochainSheaf_isFlasque [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)] (n : ℕ) :
    (SingularCochains.cochainSheaf (SchemeBetti.space x) n).IsFlasque :=
  SingularCochains.cochainSheaf_isFlasque_of_locallyCompact_secondCountable (SchemeBetti.space x) n

/-- Positive cohomology of each original sheaf term vanishes on every original open. -/
theorem singularCochainSheaf_cohomology_isZero [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (q : ℕ) (U : TopologicalSpace.Opens (ComplexPoints x)) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero (SheafCohomology.TwoOpenModules.Hobj ℚ (𝟭 _) U n
      (SingularCochains.cochainSheaf (SchemeBetti.space x) q)) :=
  SingularCochains.isZero_cochainSheaf_cohomology (SchemeBetti.space x) q U n hn

/-- This names the existing module-valued derived global-sections functor. -/
theorem singularCochainSheaf_derivedGlobalSections_isZero [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (q n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero
      (((SheafHypercohomology.globalSections ℚ (SchemeBetti.space x)).rightDerived n).obj
        (SingularCochains.cochainSheaf (SchemeBetti.space x) q)) :=
  SingularCochains.isZero_cochainSheaf_derivedGlobalSections (SchemeBetti.space x) q n hn

/-- The original comparison is now invertible for the entire singular sheaf complex. -/
theorem singularSheafDerivedComparison_isIso [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)] :
    IsIso (SheafHypercohomology.comparison ℚ (SchemeBetti.space x)
      (SingularCochains.sheafComplex (SchemeBetti.space x))) :=
  SingularCochains.derivedComparison_isIso (SchemeBetti.space x)

/-- This is the same comparison on homology in each integer degree. -/
def singularSheafSectionsHomologyIsoHypercohomology [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)] (n : ℤ) :
    (SheafHypercohomology.underivedGlobalSections ℚ (SchemeBetti.space x)
      (SingularCochains.sheafComplex (SchemeBetti.space x))).obj.homology n ≅
        SheafHypercohomology.hypercohomology ℚ (SchemeBetti.space x)
          (SingularCochains.sheafComplex (SchemeBetti.space x)) n :=
  SingularCochains.sheafSectionsHomologyIsoHypercohomology (SchemeBetti.space x) n

/-- The original canonical analytic atlas supplies contractible neighborhoods. -/
theorem stronglyLocallyContractibleSpace (d : ℕ) [SmoothOfRelativeDimension d x] :
    StronglyLocallyContractibleSpace (ComplexPoints x) := by
  let : StronglyLocallyContractibleSpace (Fin d → ℂ) :=
    normedSpace_stronglyLocallyContractible (Fin d → ℂ)
  exact chartedSpace_stronglyLocallyContractible (Fin d → ℂ) (ComplexPoints x)

/-- The constant-sheaf map uses the original rational singular cochain sheaves. -/
def singularSheafComparison := SingularCochains.comparison (SchemeBetti.space x)

/-- It is a full sheaf quasi-isomorphism on the actual canonical point space. -/
theorem singularSheafComparison_quasiIso (d : ℕ) [SmoothOfRelativeDimension d x] :
    QuasiIso (singularSheafComparison (x := x)) := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact SingularCochains.comparison_quasiIso (SchemeBetti.space x)

/-- The original rational Betti group maps to actual derived sections of the original constant sheaf. -/
def singularCohomologyToConstantSheafDerived (d : ℕ) [SmoothOfRelativeDimension d x] (n : ℕ) :
    SchemeBetti.Cohomology x n ⟶
      ((SheafHypercohomology.globalSections ℚ (SchemeBetti.space x)).rightDerived n).obj
        (SingularCochains.constantSheaf (SchemeBetti.space x)) := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact SingularCochains.cohomologyToConstantSheafDerived (SchemeBetti.space x) n

/-- The geometric local hypothesis is proved; global topology hypotheses remain explicit. -/
theorem singularCohomologyToConstantSheafDerived_isIso [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (d : ℕ) [SmoothOfRelativeDimension d x] (n : ℕ) :
    IsIso (singularCohomologyToConstantSheafDerived (x := x) d n) := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact SingularCochains.cohomologyToConstantSheafDerived_isIso (SchemeBetti.space x) n

/-- All-degree rational Betti cohomology identifies the existing derived constant-sheaf target. -/
def singularCohomologyIsoConstantSheafDerived [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (d : ℕ) [SmoothOfRelativeDimension d x] (n : ℕ) :
    SchemeBetti.Cohomology x n ≅
      ((SheafHypercohomology.globalSections ℚ (SchemeBetti.space x)).rightDerived n).obj
        (SingularCochains.constantSheaf (SchemeBetti.space x)) := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact SingularCochains.cohomologyIsoConstantSheafDerived (SchemeBetti.space x) n

@[simp]
theorem singularCohomologyIsoConstantSheafDerived_hom [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (d : ℕ) [SmoothOfRelativeDimension d x] (n : ℕ) :
    (singularCohomologyIsoConstantSheafDerived (x := x) d n).hom =
      singularCohomologyToConstantSheafDerived (x := x) d n := rfl

end AlgebraicGeometry.Scheme.ComplexPoints
