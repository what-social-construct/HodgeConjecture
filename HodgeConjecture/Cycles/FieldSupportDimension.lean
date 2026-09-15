import HodgeConjecture.Cycles.FieldDimensionFunction

/-!
# Global dimension values and actual closed carriers

The structural dimension function on a scheme locally of finite type
over a field equals actual point height. Nonnegative strictness bounds
height above; one actual affine neighbourhood, its finite height and
the affine normalization give the reverse bound. This does not require
a finite subcover or a global bound on the dimension of the scheme.

The existing point-closure and integral-carrier comparisons then identify
support degree and fundamental-cycle homogeneity with actual dimension.
Open immersions over the field preserve point height in this setting.
No new dimension function, scalar action, carrier or cycle module is
introduced. Target codimension conversion is a separate comparison.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

private theorem point_height_le_of_nonnegative_dimensionFunction
    (X : Scheme.{u}) (δ : DimensionFunction X) (hn : ∀ x, 0 ≤ δ x) (x : X) :
    Order.height x ≤ ((δ x).toNat : ℕ∞) := by
  have hmono : StrictMono (fun y : X ↦ (δ y).toNat) := by
    intro a b hab
    have hd := δ.strictMono hab
    have ha := hn a
    have hb := hn b
    change (δ a).toNat < (δ b).toNat
    omega
  simpa only [Order.height_nat] using
    Order.height_le_height_apply_of_strictMono (fun y : X ↦ (δ y).toNat) hmono x

private theorem point_height_le_of_openImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    Order.height x ≤ Order.height (f.base x) := by
  apply Order.height_le_height_apply_of_strictMono (fun y : X ↦ f.base y)
  intro a b hab
  change (b ⤳ a) ∧ ¬ (a ⤳ b) at hab
  change (f.base b ⤳ f.base a) ∧ ¬ (f.base a ⤳ f.base b)
  exact ⟨f.isOpenEmbedding.isInducing.specializes_iff.mpr hab.1,
    fun h ↦ hab.2 (f.isOpenEmbedding.isInducing.specializes_iff.mp h)⟩

/-- Actual point height is the finite structural dimension value, with
no affineness or quasi-compactness assumption on the ambient scheme. -/
theorem point_height_eq_ofLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    Order.height x = ((DimensionFunction.ofLocallyOfFiniteType k X p x).toNat : ℕ∞) := by
  apply le_antisymm
  · exact point_height_le_of_nonnegative_dimensionFunction X
      (DimensionFunction.ofLocallyOfFiniteType k X p)
      (DimensionFunction.ofLocallyOfFiniteType_nonneg k X p) x
  · obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_of_le X (le_refl x)
    letI : IsAffine (U : Scheme) := hU
    let u : (U : Scheme) := ⟨x, hxU⟩
    have hδ : DimensionFunction.ofLocallyOfFiniteType k X p x =
        ((@Order.height (U : Scheme) (specializationPreorder (U : Scheme)) u).toNat : ℤ) := by
      calc
        _ = DimensionFunction.ofLocallyOfFiniteType k U (U.ι ≫ p) u :=
          (DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion k p U.ι u).symm
        _ = _ := by
          rw [DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType,
            DimensionFunction.ofAffineLocallyOfFiniteType_apply]
    have hfin := point_height_ne_top (U : Scheme)
      (affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType k U (U.ι ≫ p)) u
    rw [hδ, Int.toNat_natCast, ENat.coe_toNat hfin]
    exact point_height_le_of_openImmersion U.ι u

/-- Point heights are finite even when no global dimension bound is
available for the locally finite-type scheme. -/
theorem point_height_ne_top_of_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    Order.height x ≠ ⊤ := by
  rw [point_height_eq_ofLocallyOfFiniteType k X p x]
  simp

/-- The already constructed global function equals literal integer
point height; no replacement grading is defined. -/
theorem DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    ofLocallyOfFiniteType k X p x = ((Order.height x).toNat : ℤ) := by
  rw [point_height_eq_ofLocallyOfFiniteType k X p x, ENat.toNat_coe]
  exact (Int.toNat_of_nonneg (ofLocallyOfFiniteType_nonneg k X p x)).symm

/-- The actual reduced closure of a point has the constructed finite
dimension value, in the full extended dimension type. -/
theorem pointSupport_dimension_eq_ofLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    topologicalKrullDim (pointSupport X x).val.subscheme =
      ((DimensionFunction.ofLocallyOfFiniteType k X p x).toNat : WithBot ℕ∞) := by
  rw [← point_height_eq_supportDim, point_height_eq_ofLocallyOfFiniteType k X p x]
  rfl

/-- The existing degree of any actual integral closed carrier detects
its actual dimension, without a global finiteness assumption. -/
theorem supportDegree_ofLocallyOfFiniteType_eq_iff
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  have h := pointSupport_dimension_eq_ofLocallyOfFiniteType k X p (ambientGenericPoint W)
  rw [pointSupport_ambientGenericPoint] at h
  rw [h, supportDegree, DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight]
  simp only [Int.toNat_natCast]
  norm_cast

/-- Over nontrivial coefficients, homogeneous fundamental cycles in the
existing cycle module are exactly the actual carriers of that dimension. -/
theorem fundamentalCycle_mem_ofLocallyOfFiniteType_iff
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type v) [Semiring R] [Nontrivial R]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈
        cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  rw [fundamentalCycle_mem_cyclesOfDegree_iff, supportDegree_ofLocallyOfFiniteType_eq_iff]

/-- Actual open immersions preserve point height over a field in the
locally finite-type setting; this is not an unrestricted scheme claim. -/
theorem point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    Order.height x = Order.height (f.base x) := by
  rw [point_height_eq_ofLocallyOfFiniteType k X (f ≫ p),
    point_height_eq_ofLocallyOfFiniteType k Y p,
    DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion]

end

end HodgeConjecture.SchemeCycles
