module

public import HodgeConjecture.Cycles.ProjectiveLinePrincipalDegree
public import HodgeConjecture.Cycles.SchemeLocalOrder
public import HodgeConjecture.Cycles.FunctionFieldTransport
public import HodgeConjecture.Geometry.ProjectiveLineProperties

@[expose] public section

/-!
# Actual affine-chart orders for the projective-line degree calculation

The polynomial prime is an actual point of the polynomial spectrum, and
its actual stalk is the corresponding localization. The canonical generic
stalk field is identified with `RatFunc k`, preserving the original
polynomial algebra map. Thus the existing scheme divisor order equals the
proved normalized-factor order, through actual stalk and function-field
maps.

Selected local proof adaptations from AxiomMath/Stacks, revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Chow/ProjectiveLineDivisorDegree/SpecOrder.lean`,
Apache-2.0. See `third_party/axiom-stacks/LICENSE`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.SchemeCycles.ProjectiveLineDegree

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

universe u

section Spec

variable (A : CommRingCat.{u}) [IsDomain A]

/-- The native field algebra, bundled before specializing the commutative-ring object. -/
@[instance_reducible]
def specFunctionFieldAlgebra : Algebra A (Spec A).functionField := inferInstance

theorem specFunctionFieldIsFractionRing : IsFractionRing A (Spec A).functionField := inferInstance

instance specStalkAlgebra (x : Spec A) : Algebra A ((Spec A).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra A x

instance specPointIsPrime (x : Spec A) : x.asIdeal.IsPrime := x.isPrime

instance specStalkIsLocalization (x : Spec A) :
    IsLocalization.AtPrime ((Spec A).presheaf.stalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A x

/-- The canonical equivalence to any fraction field, preserving actual ring elements. -/
def specFunctionFieldEquiv (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    (Spec A).functionField ≃+* K :=
  (IsLocalization.algEquiv (nonZeroDivisors A) (Spec A).functionField K).toRingEquiv

theorem specFunctionFieldEquiv_algebraMap (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] (a : A) :
    specFunctionFieldEquiv A K (algebraMap A (Spec A).functionField a) = algebraMap A K a :=
  (IsLocalization.algEquiv (nonZeroDivisors A) (Spec A).functionField K).commutes a

/-- The canonical polynomial-to-stalk-to-generic-field square, on the actual affine scheme. -/
theorem spec_stalk_functionField_isScalarTower (x : Spec A) :
    IsScalarTower A ((Spec A).presheaf.stalk x) (Spec A).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change (StructureSheaf.toStalk A (genericPoint (Spec A))).hom a =
    ((Spec A).presheaf.stalkSpecializes
      ((genericPoint_spec (Spec A)).specializes (Set.mem_univ x))).hom
        ((StructureSheaf.toStalk A x).hom a)
  exact congrArg (fun g : CommRingCat.of A ⟶ _ ↦ g.hom a)
    (StructureSheaf.toStalk_stalkSpecializes (R := A)
      ((genericPoint_spec (Spec A)).specializes (Set.mem_univ x))).symm

variable [IsPrincipalIdealRing A]

/-- The actual polynomial-spectrum point cut out by an irreducible element. -/
def irreduciblePoint {p : A} (hp : Irreducible p) : Spec A :=
  ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime⟩

@[simp]
theorem irreduciblePoint_asIdeal {p : A} (hp : Irreducible p) :
    (irreduciblePoint A hp).asIdeal = Ideal.span {p} := rfl

instance irreduciblePoint_isMaximal {p : A} (hp : Irreducible p) :
    (irreduciblePoint A hp).asIdeal.IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hp

/-- This point has an actual one-dimensional stalk. -/
def irreducibleDivisorPoint (hA : ¬IsField A) {p : A} (hp : Irreducible p) :
    DivisorPoint (Spec A) :=
  ⟨irreduciblePoint A hp, by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (irreduciblePoint A hp).asIdeal,
      IsPrincipalIdealRing.height_eq_one_of_isMaximal _ hA]
    rfl⟩

end Spec

section Polynomial

variable (k : Type u) [Field k] [DecidableEq k]

abbrev polynomialSpectrum : Scheme.{u} := Spec (.of (Polynomial k))

/-- The actual affine-line function field, in its canonical rational-function coordinates. -/
def polynomialFunctionFieldEquiv : (polynomialSpectrum k).functionField ≃+* RatFunc k :=
  specFunctionFieldEquiv (.of (Polynomial k)) (RatFunc k)

/-- At every actual polynomial prime, the existing signed scheme order is the factor-count order. -/
theorem polynomialDivisorOrder_eq_finiteOrder {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (f : (polynomialSpectrum k).functionFieldˣ) :
    divisorOrder (polynomialSpectrum k)
        (irreducibleDivisorPoint (.of (Polynomial k)) (Polynomial.not_isField k) hp) f =
      finiteOrder p (polynomialFunctionFieldEquiv k (f : (polynomialSpectrum k).functionField)) := by
  let A := CommRingCat.of (Polynomial k)
  let x : Spec A := irreduciblePoint A hp
  let : x.asIdeal.IsPrime := x.isPrime
  let L := (Spec A).presheaf.stalk x
  let : Algebra (Polynomial k) L := specStalkAlgebra A x
  let : IsLocalization.AtPrime L x.asIdeal := specStalkIsLocalization A x
  let : Algebra (Polynomial k) (Spec A).functionField := specFunctionFieldAlgebra A
  let : IsFractionRing (Polynomial k) (Spec A).functionField := specFunctionFieldIsFractionRing A
  let : IsScalarTower (Polynomial k) L (Spec A).functionField :=
    spec_stalk_functionField_isScalarTower A x
  let : Ring.KrullDimLE 1 L :=
    divisorPoint_stalkKrullDimLE (Spec A)
      (irreducibleDivisorPoint A (Polynomial.not_isField k) hp)
  change localOrder L f = _
  exact localOrder_polynomialLocalization_eq_finiteOrder hp hpm x.asIdeal rfl L
    (Spec A).functionField f

end Polynomial

end

end HodgeConjecture.SchemeCycles.ProjectiveLineDegree
