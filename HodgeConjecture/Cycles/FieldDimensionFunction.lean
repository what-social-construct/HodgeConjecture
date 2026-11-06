module

public import HodgeConjecture.Cycles.ChartResidueDegree

@[expose] public section

/-!
# The structural dimension function over a field

On any scheme locally of finite type over a field, the finite structural
residue degree defines an actual dimension function. A specialization pair
lies in an affine neighbourhood of its specialized point. The actual
open embedding reflects specialization and transfers the ambient cover
into that chart, where the affine strictness and unit-step laws are proved. The chart
residue-degree comparison transfers both laws back to the actual scheme.

The construction agrees with the existing affine function and its values
are preserved by actual open immersions over the structural field. No
affineness, quasi-compactness, integrality or global dimension bound is
assumed. Identification with global point-closure and carrier dimensions
is a separate comparison, not a consequence of the two defining laws alone.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- A specialization pair lies in one actual affine open neighbourhood
of the specialized point, without finiteness or base assumptions. -/
theorem exists_isAffineOpen_mem_of_le (X : Scheme.{u}) {x y : X} (hxy : x ≤ y) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
  exact ⟨U, hU, hxU, (Scheme.le_iff_specializes.mp hxy).mem_open U.isOpen hxU⟩

theorem residueDegree_dimensionLaws
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    let d : X → ℤ := fun x ↦
      letI := residueFieldBaseAlgebra k p x
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ)
    StrictMono d ∧ ∀ {x y : X}, x ⋖ y → d y = d x + 1 := by
  dsimp only
  constructor
  · intro x y hxy
    obtain ⟨U, hU, hxU, hyU⟩ := exists_isAffineOpen_mem_of_le X hxy.le
    letI : IsAffine (U : Scheme) := hU
    have hxyU : @LT.lt (U : Scheme) (specializationPreorder (U : Scheme)).toLT
        ⟨x, hxU⟩ ⟨y, hyU⟩ := by
      change (y ⤳ x) ∧ ¬ (x ⤳ y) at hxy
      change ((⟨y, hyU⟩ : (U : Scheme)) ⤳ ⟨x, hxU⟩) ∧
        ¬ ((⟨x, hxU⟩ : (U : Scheme)) ⤳ ⟨y, hyU⟩)
      exact ⟨U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hxy.1,
        fun h ↦ hxy.2 (U.ι.isOpenEmbedding.isInducing.specializes_iff.mpr h)⟩
    have h := (DimensionFunction.ofAffineLocallyOfFiniteType k U (U.ι ≫ p)).strictMono hxyU
    simpa only [affineChart_dimension_eq_schemeResidueField_trdeg k p U.ι, Scheme.Opens.ι_apply] using h
  · intro x y hxy
    obtain ⟨U, hU, hxU, hyU⟩ := exists_isAffineOpen_mem_of_le X hxy.le
    letI : IsAffine (U : Scheme) := hU
    have hxyU : @CovBy (U : Scheme) (specializationPreorder (U : Scheme)).toLT
        ⟨x, hxU⟩ ⟨y, hyU⟩ := by
      constructor
      · change ((⟨y, hyU⟩ : (U : Scheme)) ⤳ ⟨x, hxU⟩) ∧
          ¬ ((⟨x, hxU⟩ : (U : Scheme)) ⤳ ⟨y, hyU⟩)
        have hl := hxy.lt
        change (y ⤳ x) ∧ ¬ (x ⤳ y) at hl
        exact ⟨U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hl.1,
          fun h ↦ hl.2 (U.ι.isOpenEmbedding.isInducing.specializes_iff.mpr h)⟩
      · intro z hxz hzy
        apply hxy.2
        · change ((z.val : X) ⤳ x) ∧ ¬ (x ⤳ z.val)
          change (z ⤳ (⟨x, hxU⟩ : (U : Scheme))) ∧ ¬ ((⟨x, hxU⟩ : (U : Scheme)) ⤳ z) at hxz
          exact ⟨U.ι.isOpenEmbedding.isInducing.specializes_iff.mpr hxz.1,
            fun h ↦ hxz.2 (U.ι.isOpenEmbedding.isInducing.specializes_iff.mp h)⟩
        · change (y ⤳ (z.val : X)) ∧ ¬ (z.val ⤳ y)
          change ((⟨y, hyU⟩ : (U : Scheme)) ⤳ z) ∧ ¬ (z ⤳ (⟨y, hyU⟩ : (U : Scheme))) at hzy
          exact ⟨U.ι.isOpenEmbedding.isInducing.specializes_iff.mpr hzy.1,
            fun h ↦ hzy.2 (U.ι.isOpenEmbedding.isInducing.specializes_iff.mp h)⟩
    have h := (DimensionFunction.ofAffineLocallyOfFiniteType k U (U.ι ≫ p)).map_covBy hxyU
    simpa only [affineChart_dimension_eq_schemeResidueField_trdeg k p U.ι, Scheme.Opens.ι_apply] using h

/-- The actual structural residue-degree dimension function on a scheme
locally of finite type over a field, with both defining laws proved. -/
def DimensionFunction.ofLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] : DimensionFunction X where
  toFun x :=
    letI := residueFieldBaseAlgebra k p x
    (Algebra.trdeg k (X.residueField x)).toNat
  strictMono := (residueDegree_dimensionLaws k X p).1
  map_covBy := (residueDegree_dimensionLaws k X p).2

/-- Evaluation retains the actual scheme residue field and the scalar
action of the supplied structural morphism. SP51 proves this degree finite. -/
@[simp]
theorem DimensionFunction.ofLocallyOfFiniteType_apply
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    ofLocallyOfFiniteType k X p x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := rfl

/-- The field-normalized dimension function is nonnegative at every point. -/
theorem DimensionFunction.ofLocallyOfFiniteType_nonneg
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    0 ≤ ofLocallyOfFiniteType k X p x := Int.natCast_nonneg _

/-- On an affine scheme the global construction is the same existing
dimension-function object, not a second independent grading. -/
theorem DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ofLocallyOfFiniteType k X p = ofAffineLocallyOfFiniteType k X p := by
  unfold ofLocallyOfFiniteType ofAffineLocallyOfFiniteType
  congr 1
  funext x
  exact (ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k X p x).symm

/-- Actual open immersions preserve the constructed dimension values,
with the source structural map obtained by composition. -/
theorem DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    ofLocallyOfFiniteType k X (f ≫ p) x =
      ofLocallyOfFiniteType k Y p (f.base x) := by
  rw [ofLocallyOfFiniteType_apply, ofLocallyOfFiniteType_apply,
    residueFieldBase_trdeg_eq_of_isOpenImmersion k p f x]

end

end HodgeConjecture.SchemeCycles
