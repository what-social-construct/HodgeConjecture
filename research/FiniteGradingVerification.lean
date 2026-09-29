import HodgeConjecture.Cycles.FiniteGrading
import HodgeConjecture.Cycles.FieldSupportDimension
import Lean.Util.CollectAxioms

/-!
SP102 focused checks for actual finite residue-field algebraicity and the
canonical grading of the existing finite pushforward. Run with
`lake env lean research/FiniteGradingVerification.lean`.

Both structural scalar actions are the existing ones, and the middle field
map is literally the scheme residue-field map. Full cardinal transcendence
degrees are compared before conversion to natural numbers. Local finite
type is only used for the existing canonical dimension functions. Their
proved compatibility is passed directly to SP101's existing graded map;
there is no new cycle carrier, pushforward wrapper, or supplied grading gap.
The exact five-API registry checks the standard-three Lean axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles

noncomputable section

universe u v

#check residueFieldMap_isAlgebraic_of_isFinite
#check residueFieldBase_trdeg_eq_of_isFinite
#check DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite
#check supportDegree_imageSubscheme_ofLocallyOfFiniteType
#check finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

section ActualResidueMap

example (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    algebraMap (Y.residueField (f.base x)) (X.residueField x) =
      (f.residueFieldMap x).hom := rfl

example (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : IsDominant f := inferInstance
  fail_if_success have _ : IsEtale f := inferInstance
  fail_if_success
    have _ : Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  exact residueFieldMap_isAlgebraic_of_isFinite f x

example (x : X) (a : X.residueField x) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsAlgebraic (Y.residueField (f.base x)) a := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI := residueFieldMap_isAlgebraic_of_isFinite f x
  exact Algebra.IsAlgebraic.isAlgebraic a

example [IsEtale f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) :=
  residueFieldMap_isAlgebraic_of_isFinite f x

end ActualResidueMap

variable (k : Type u) [Field k] (p : Y ⟶ Spec (CommRingCat.of k))

section StructuralScalars

example (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    algebraMap k (Y.residueField (f.base x)) = residueFieldBaseMap k p (f.base x) ∧
      algebraMap k (X.residueField x) = residueFieldBaseMap k (f ≫ p) x := ⟨rfl, rfl⟩

example (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower k (Y.residueField (f.base x)) (X.residueField x) := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (residueFieldBaseMap_comp k p f x).symm

example (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Algebra.trdeg k (Y.residueField (f.base x)) = Algebra.trdeg k (X.residueField x) := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  fail_if_success have _ : LocallyOfFiniteType p := inferInstance
  fail_if_success have _ : FiniteDimensional k (X.residueField x) := inferInstance
  fail_if_success have _ : PerfectField k := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  exact residueFieldBase_trdeg_eq_of_isFinite k p f x

example (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    (Algebra.trdeg k (Y.residueField (f.base x))).toNat =
      (Algebra.trdeg k (X.residueField x)).toNat :=
  congrArg Cardinal.toNat (residueFieldBase_trdeg_eq_of_isFinite k p f x)

end StructuralScalars

section CanonicalGrading

variable [LocallyOfFiniteType p]

local notation "δX" => DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)
local notation "δY" => DimensionFunction.ofLocallyOfFiniteType k Y p
local notation "hδ" => supportDegree_imageSubscheme_ofLocallyOfFiniteType k p f

example : LocallyOfFiniteType (f ≫ p) := inferInstance

example (x : X) : δX x = δY (f.base x) := by
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsIntegral Y := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : IsEtale f := inferInstance
  exact DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p f x

example (x : X) : Order.height x = Order.height (f.base x) := by
  rw [point_height_eq_ofLocallyOfFiniteType k X (f ≫ p),
    point_height_eq_ofLocallyOfFiniteType k Y p,
    DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite]

example (W : IntegralClosedSubscheme X) :
    supportDegree δY (imageSubscheme f W) = supportDegree δX W :=
  supportDegree_imageSubscheme_ofLocallyOfFiniteType k p f W

example (R : Type v) [Semiring R] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R δX n) :
    finitePushforward R f c ∈ cyclesOfDegree R δY n := by
  fail_if_success have _ : Nontrivial R := inferInstance
  fail_if_success have _ : IsIntegral X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  exact finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType k R p f n c hc

example (R : Type v) [Semiring R] (n : ℤ) (c : cyclesOfDegree R δX n) :
    (gradedFinitePushforward R δX δY f hδ n c).val = finitePushforward R f c.val :=
  gradedFinitePushforward_val R δX δY f hδ n c

example (n : ℤ) (W : IntegralClosedSubscheme X) (hW : supportDegree δX W = n) :
    (gradedFinitePushforward ℚ δX δY f hδ n
      ⟨Finsupp.single W (-3 / 2 : ℚ),
        single_mem_cyclesOfDegree ℚ δX n W (-3 / 2) hW⟩).val =
      (-3 / 2 : ℚ) • (finitePushforwardDegree f W • fundamentalCycle ℚ (imageSubscheme f W)) :=
  finitePushforward_single f ℚ W (-3 / 2)

example (n : ℤ) (c : Cycles X (PUnit : Type)) (hc : c ∈ cyclesOfDegree _ δX n) :
    finitePushforward (PUnit : Type) f c ∈ cyclesOfDegree _ δY n :=
  finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType k (PUnit : Type) p f n c hc

example (n : ℤ) (c : cyclesOfDegree ℤ δX n) :
    gradedFinitePushforward ℚ δX δY f hδ n (cyclesOfDegreeRationalize δX n c) =
      cyclesOfDegreeRationalize δY n (gradedFinitePushforward ℤ δX δY f hδ n c) :=
  gradedFinitePushforward_rationalize δX δY f hδ n c

example (R : Type v) [Semiring R] (n : ℤ)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W) :
    gradedFinitePushforward R δX δY f hδ n = gradedFinitePushforward R δX δY f hdeg n := rfl

example [IsEtale f] (R : Type v) [Semiring R] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R δX n) :
    finitePushforward R f c ∈ cyclesOfDegree R δY n :=
  finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType k R p f n c hc

example [IsClosedImmersion f] (R : Type v) [Semiring R] (n : ℤ) :
    gradedFinitePushforward R δX δY f hδ n =
      gradedClosedImmersionPushforwardWithCoefficients R δX δY f
        (fun W => by simpa only [imageSubscheme_eq_closedImageSubscheme] using hδ W) n :=
  gradedFinitePushforward_eq_closedImmersionPushforward R δX δY f hδ n

end CanonicalGrading

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.residueFieldMap_isAlgebraic_of_isFinite,
    `HodgeConjecture.SchemeCycles.residueFieldBase_trdeg_eq_of_isFinite,
    `HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite,
    `HodgeConjecture.SchemeCycles.supportDegree_imageSubscheme_ofLocallyOfFiniteType,
    `HodgeConjecture.SchemeCycles.finitePushforward_mem_cyclesOfDegree_ofLocallyOfFiniteType]
  unless declarations.length == 5 && declarations.eraseDups.length == 5 do
    throwError "Expected exactly five distinct SP102 public declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP102 audit registry: five distinct public declarations"
