module

public import HodgeConjecture.Cycles.FinitePushforwardCoefficients
public import HodgeConjecture.Cycles.FiniteSchemeLength
public import HodgeConjecture.Cycles.FiniteGrading
public import HodgeConjecture.Cycles.OpenSupport
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

/-!
# Finite pullback with actual scheme-fiber multiplicities

The coefficient at a source point is the original coefficient at its image
times the length of the actual local fiber ring. Finiteness of the morphism
makes the resulting cycle finitely supported. No degree formula or relation
preservation is assumed in this construction.

For finite flat maps this is the relative-dimension-zero prescription of
Stacks 02RB. The operation is defined for every finite morphism; rational
equivalence and functorial pullback require additional geometric arguments.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The multiplicity is the length of the actual local scheme-fiber ring.
For finite morphisms this ring is Artinian, so its length is finite. -/
def finiteFiberMultiplicity (x : X) : ℕ :=
  (Module.length ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
    ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))).toNat

/-- The degree at a target point is the dimension of the actual fiber's
global sections over the target residue field. -/
def finiteFiberDegree (y : Y) : ℕ :=
  letI := globalSectionBaseAlgebra (Y.residueField y) (f.fiberToSpecResidueField y)
  Module.finrank (Y.residueField y) Γ(f.fiber y, ⊤)

/-- The actual local fiber length is finite for a finite morphism. -/
theorem finiteFiberMultiplicity_length_ne_top [IsFinite f] (x : X) :
    Module.length ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
      ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) ≠ ⊤ := by
  letI : IsFinite (f.fiberToSpecResidueField (f.base x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact finiteScheme_stalk_length_ne_top (Y.residueField (f.base x))
    (f.fiberToSpecResidueField (f.base x)) (f.asFiber x)

/-- Each actual source point contributes a positive multiplicity. -/
theorem finiteFiberMultiplicity_pos [IsFinite f] (x : X) :
    0 < finiteFiberMultiplicity f x := by
  apply Nat.pos_of_ne_zero
  intro h
  exact (ENat.toNat_eq_zero.mp h).elim Module.length_pos.ne'
    (finiteFiberMultiplicity_length_ne_top f x)

/-- An open immersion has local fiber multiplicity one at every source
point, through its actual open fiber over a field. -/
theorem finiteFiberMultiplicity_of_isOpenImmersion [IsOpenImmersion f] (x : X) :
    finiteFiberMultiplicity f x = 1 := by
  let F := f.fiber (f.base x)
  let p := f.fiberToSpecResidueField (f.base x)
  letI : IsOpenImmersion p := MorphismProperty.pullback_snd _ _ inferInstance
  letI : Nonempty F := ⟨f.asFiber x⟩
  letI : IsIntegral F := isIntegral_of_isOpenImmersion p
  have hx : f.asFiber x = genericPoint F :=
    p.isOpenEmbedding.injective (Subsingleton.elim _ _)
  unfold finiteFiberMultiplicity
  rw [hx]
  change (Module.length F.functionField F.functionField).toNat = 1
  rw [Module.length_eq_one]
  rfl

theorem finiteFiberPullback_support_finite (R : Type v) [Semiring R]
    [IsFinite f] (c : Cycles Y R) :
    (Function.support (fun W : IntegralClosedSubscheme X ↦
      c (pointSupport Y (f.base (ambientGenericPoint W))) *
        (finiteFiberMultiplicity f (ambientGenericPoint W) : R))).Finite := by
  classical
  have hs : (f.base ⁻¹' (ambientGenericPoint '' (c.support : Set _))).Finite :=
    (c.support.finite_toSet.image ambientGenericPoint).preimage' (fun y _ ↦ by
      change {x : X | f.base x = y}.Finite
      exact Set.finite_coe_iff.mp (finiteFiber_finite f y))
  apply (hs.image (pointSupport X)).subset
  intro W hW
  have hc : c (pointSupport Y (f.base (ambientGenericPoint W))) ≠ 0 :=
    left_ne_zero_of_mul hW
  refine ⟨ambientGenericPoint W, ?_, pointSupport_ambientGenericPoint W⟩
  exact ⟨pointSupport Y (f.base (ambientGenericPoint W)),
    Finsupp.mem_support_iff.mpr hc, ambientGenericPoint_pointSupport Y _⟩

/-- Finite fiber pullback on the original cycle module. Flatness is needed
for its geometric Chow properties, not to make this coefficient map finite. -/
def finiteFiberPullback (R : Type v) [Semiring R] [IsFinite f] :
    Cycles Y R →ₗ[R] Cycles X R where
  toFun c := Finsupp.ofSupportFinite
    (fun W ↦ c (pointSupport Y (f.base (ambientGenericPoint W))) *
      (finiteFiberMultiplicity f (ambientGenericPoint W) : R))
    (finiteFiberPullback_support_finite f R c)
  map_add' c d := by ext W; exact add_mul _ _ _
  map_smul' r c := by ext W; exact mul_assoc _ _ _

/-- Pullback uses the original support and the actual local fiber length. -/
@[simp]
theorem finiteFiberPullback_apply (R : Type v) [Semiring R] [IsFinite f]
    (c : Cycles Y R) (W : IntegralClosedSubscheme X) :
    finiteFiberPullback f R c W =
      c (pointSupport Y (f.base (ambientGenericPoint W))) *
        (finiteFiberMultiplicity f (ambientGenericPoint W) : R) := rfl

/-- The point coefficient is pulled back with its actual fiber multiplicity. -/
@[simp]
theorem finiteFiberPullback_apply_pointSupport (R : Type v) [Semiring R] [IsFinite f]
    (c : Cycles Y R) (x : X) :
    finiteFiberPullback f R c (pointSupport X x) =
      c (pointSupport Y (f.base x)) * (finiteFiberMultiplicity f x : R) := by
  simp only [finiteFiberPullback_apply, ambientGenericPoint_pointSupport]

/-- On a finite open immersion the new coefficient construction is the
existing ideal-comap restriction map, not an independently chosen operation. -/
theorem finiteFiberPullback_eq_openRestriction (R : Type v) [Semiring R]
    [IsFinite f] [IsOpenImmersion f] : finiteFiberPullback f R = openRestriction R f := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro W
  rw [finiteFiberPullback_apply, finiteFiberMultiplicity_of_isOpenImmersion,
    Nat.cast_one, mul_one, openRestriction_apply]
  rfl

/-- Identity finite fiber pullback is the identity on actual cycles. -/
@[simp]
theorem finiteFiberPullback_id (R : Type v) [Semiring R] (S : Scheme.{u}) :
    finiteFiberPullback (𝟙 S) R = LinearMap.id := by
  rw [finiteFiberPullback_eq_openRestriction]
  exact openRestriction_id R

/-- Integer-to-rational coefficient extension commutes with the same
finite fiber pullback. -/
theorem finiteFiberPullback_rationalize [IsFinite f] (c : Cycles Y ℤ) :
    finiteFiberPullback f ℚ (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) c) =
      Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) (finiteFiberPullback f ℤ c) := by
  ext W
  simp [finiteFiberPullback_apply, Finsupp.mapRange_apply]

/-- The same finite pullback preserves the existing canonical field grading.
The residue extension is algebraic for every finite morphism. -/
theorem finiteFiberPullback_mem_cyclesOfDegree
    (k : Type u) [Field k] (R : Type v) [Semiring R] [IsFinite f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (n : ℤ) (c : Cycles Y R)
    (hc : c ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k Y p) n) :
    finiteFiberPullback f R c ∈
      cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)) n := by
  rw [mem_cyclesOfDegree_iff] at hc ⊢
  intro W hW
  rw [finiteFiberPullback_apply] at hW
  rw [supportDegree, DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k p f]
  simpa only [supportDegree, ambientGenericPoint_pointSupport] using
    hc _ (left_ne_zero_of_mul hW)

/-- Restrict the original finite fiber pullback to the original homogeneous
submodules, with its grading preservation proved. -/
def gradedFiniteFiberPullback
    (k : Type u) [Field k] (R : Type v) [Semiring R] [IsFinite f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℤ) :
    cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k Y p) n →ₗ[R]
      cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p)) n :=
  { toFun := fun c ↦ ⟨finiteFiberPullback f R c.val,
      finiteFiberPullback_mem_cyclesOfDegree f k R p n c.val c.property⟩
    map_add' := fun c d ↦ Subtype.ext ((finiteFiberPullback f R).map_add c.val d.val)
    map_smul' := fun r c ↦ Subtype.ext ((finiteFiberPullback f R).map_smul r c.val) }

/-- Graded pullback retains the literal underlying finite cycle map. -/
@[simp]
theorem gradedFiniteFiberPullback_val
    (k : Type u) [Field k] (R : Type v) [Semiring R] [IsFinite f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (n : ℤ)
    (c : cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k Y p) n) :
    (gradedFiniteFiberPullback f k R p n c).val = finiteFiberPullback f R c.val := rfl

end

end HodgeConjecture.SchemeCycles
