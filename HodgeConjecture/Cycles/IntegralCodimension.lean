import HodgeConjecture.Cycles.FieldSupportDimension

/-!
# Actual codimension and dimension on integral schemes over a field

For an integral scheme locally of finite type over a field, the finite
height of its generic point bounds ambient dimension and point coheight.
Induction on finite coheight, using the already proved cover law, identifies
actual chain codimension with the drop in the existing dimension function.
The support and finite-cycle comparisons reuse the existing carriers and
homogeneous submodules. No replacement codimension, grading, catenarity
input or Chow quotient is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

/-- The generic point identifies the actual dimension of an integral
locally finite-type scheme with its finite structural dimension value. -/
theorem integral_topologicalKrullDim_eq_ofLocallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    topologicalKrullDim X =
      ((DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X)).toNat : WithBot ℕ∞) := by
  rw [← genericPoint_height_eq_topologicalKrullDim X,
    point_height_eq_ofLocallyOfFiniteType k X p]
  rfl

/-- Integral ambient geometry gives finite actual point coheight without
an affineness or quasi-compactness assumption. -/
theorem point_coheight_ne_top_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    Order.coheight x ≠ ⊤ := by
  have hdim : topologicalKrullDim X < ⊤ := by
    rw [integral_topologicalKrullDim_eq_ofLocallyOfFiniteType k X p]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  have h := (Order.coheight_le_krullDim x).trans_lt
    ((topologicalKrullDim_eq_pointKrullDim X) ▸ hdim)
  exact (WithBot.coe_lt_coe.mp h).ne

private theorem coheight_add_dimensionFunction_eq_of_eq_nat
    (X : Scheme.{u}) [IsIntegral X] (δ : DimensionFunction X)
    (n : ℕ) (x : X) (hx : Order.coheight x = (n : ℕ∞)) :
    (n : ℤ) + δ x = δ (genericPoint X) := by
  induction n generalizing x with
  | zero =>
      have hmax : IsMax x := Order.coheight_eq_zero.mp (by simpa using hx)
      have hxη : x ≤ genericPoint X :=
        Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
      have hηx : genericPoint X ≤ x := hmax hxη
      have heq : x = genericPoint X :=
        ((Scheme.le_iff_specializes.mp hηx).antisymm
          (Scheme.le_iff_specializes.mp hxη)).eq
      simp [heq]
  | succ n ih =>
      have hx' : Order.coheight x = (n : ℕ∞) + 1 := by simpa using hx
      obtain ⟨_, ⟨y, hxy, hy⟩, hbound⟩ :=
        (Order.coheight_eq_coe_add_one_iff (n := n)).mp hx'
      have hcover : x ⋖ y := by
        refine ⟨hxy, ?_⟩
        intro z hxz hzy
        have hpos := Order.coheight_add_one_le hzy
        rw [hy] at hpos
        have hlt : (n : ℕ∞) < (n : ℕ∞) + 1 := by
          exact_mod_cast Nat.lt_succ_self n
        exact (not_le_of_gt hlt) (hpos.trans (hbound z hxz))
      have hi := ih y hy
      have hd := δ.map_covBy hcover
      push_cast
      omega

/-- Finite actual coheight measures the drop from the generic dimension
value, using the proved cover law rather than a supplied chain formula. -/
theorem point_coheight_add_dimension_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    ((Order.coheight x).toNat : ℤ) + DimensionFunction.ofLocallyOfFiniteType k X p x =
      DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) :=
  coheight_add_dimensionFunction_eq_of_eq_nat X
    (DimensionFunction.ofLocallyOfFiniteType k X p) (Order.coheight x).toNat x
    (ENat.coe_toNat (point_coheight_ne_top_of_integral_locallyOfFiniteType k X p x)).symm

/-- The existing chain codimension of an actual integral closed carrier
is finite in the integral locally finite-type field setting. -/
theorem supportCodimension_ne_top_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) : supportCodimension W ≠ ⊤ := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight]
  exact point_coheight_ne_top_of_integral_locallyOfFiniteType k X p (ambientGenericPoint W)

/-- Actual chain codimension plus the existing carrier degree equals
the generic dimension value. Codimension is not defined by subtraction. -/
theorem supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    ((supportCodimension W).toNat : ℤ) +
        supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W =
      DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight, supportDegree]
  exact point_coheight_add_dimension_of_integral_locallyOfFiniteType k X p (ambientGenericPoint W)

/-- The same formula in the full extended dimension type, for the
actual closed carrier and actual ambient scheme. -/
theorem supportCodimension_add_dimension_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    (supportCodimension W : WithBot ℕ∞) + topologicalKrullDim W.val.subscheme =
      topologicalKrullDim X := by
  have hsum := supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType k X p W
  rw [supportDegree] at hsum
  have hW := DimensionFunction.ofLocallyOfFiniteType_nonneg k X p (ambientGenericPoint W)
  have hX := DimensionFunction.ofLocallyOfFiniteType_nonneg k X p (genericPoint X)
  have hn : (supportCodimension W).toNat +
        (DimensionFunction.ofLocallyOfFiniteType k X p (ambientGenericPoint W)).toNat =
      (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X)).toNat := by omega
  have hdim := pointSupport_dimension_eq_ofLocallyOfFiniteType k X p (ambientGenericPoint W)
  rw [pointSupport_ambientGenericPoint] at hdim
  rw [hdim, integral_topologicalKrullDim_eq_ofLocallyOfFiniteType k X p,
    ← ENat.coe_toNat (supportCodimension_ne_top_of_integral_locallyOfFiniteType k X p W)]
  exact_mod_cast hn

/-- Degree d-n detects actual codimension n for every natural n; the
subtraction is in the integers, without an assumed bound n ≤ d. -/
theorem supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W =
        DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ) ↔
      supportCodimension W = (n : ℕ∞) := by
  have hsum := supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType k X p W
  have hfin := supportCodimension_ne_top_of_integral_locallyOfFiniteType k X p W
  constructor
  · intro h
    have hn : (supportCodimension W).toNat = n := by omega
    rw [← ENat.coe_toNat hfin, hn]
  · intro h
    have hn : (supportCodimension W).toNat = n := by rw [h]; simp
    omega

/-- A nonzero coefficient-one generator lies in degree d-n exactly
when its existing actual carrier has chain codimension n. -/
theorem fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type v) [Semiring R] [Nontrivial R]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R
        (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) ↔
      supportCodimension W = (n : ℕ∞) := by
  rw [fundamentalCycle_mem_cyclesOfDegree_iff,
    supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType]

/-- The existing homogeneous submodule is exactly finite cycles whose
nonzero coefficients have actual codimension n. No new cycle type is made. -/
theorem mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type v) [Semiring R] (n : ℕ) (c : Cycles X R) :
    c ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) ↔
      ∀ W : IntegralClosedSubscheme X, c W ≠ 0 → supportCodimension W = (n : ℕ∞) := by
  simp only [mem_cyclesOfDegree_iff,
    supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType]

end

end HodgeConjecture.SchemeCycles
