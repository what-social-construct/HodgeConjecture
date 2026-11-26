module

public import HodgeConjecture.Geometry.ProjectiveLineSquare
public import HodgeConjecture.Cycles.ProjectiveLineChow
public import HodgeConjecture.Cycles.FiniteFlatChowDegree
public import HodgeConjecture.Cycles.FinitePushforwardComposition
public import HodgeConjecture.Cycles.FiberMultiplicityLocal
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

/-!
# Original ordinary Chow maps for the connected projective-line square

The source retains the structural grading of the actual composite with
squaring. Its comparison with the old projective-line Chow quotient keeps
every actual cycle representative. Finite pushforward preserves the
coefficient degree over an algebraically closed field; the original
geometric push--pull theorem then computes the degree of flat pullback.
The local multiplicities at zero and infinity are derived from the actual
singleton fibers and the geometric rank, rather than supplied as weights.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareChow

open AlgebraicGeometry CategoryTheory TopologicalSpace SchemeCycles
open ProjectiveLineSquare ProjectiveLineCycles

universe u

variable (k : Type u) [Field k]

abbrev baseStructure := projectiveLine k ↘ Spec (.of k)
abbrev sourceStructure := square k ≫ baseStructure k

abbrev sourceDimension :=
  DimensionFunction.ofLocallyOfFiniteType k (projectiveLine k) (sourceStructure k)

/-- The exact original downstairs quotient. -/
abbrev BaseChow := RationalChowGroup (dimensionFunction k) 0

/-- The exact original quotient for the actual source structure map. -/
abbrev CoverChow := RationalChowGroup (sourceDimension k) 0

private theorem dimensionFunction_congr {X : Scheme.{u}}
    (p q : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (h : p = q) :
    DimensionFunction.ofLocallyOfFiniteType k X p =
      DimensionFunction.ofLocallyOfFiniteType k X q := by
  cases h
  rfl

theorem sourceDimension_eq : sourceDimension k = dimensionFunction k := by
  exact dimensionFunction_congr k (sourceStructure k) (baseStructure k) (over_base k)

/-- Only the proved grading equality is transported; representatives are unchanged. -/
def chowEquiv : CoverChow k ≃ₗ[ℚ] BaseChow k :=
  LinearEquiv.cast (R := ℚ)
    (M := fun δ : DimensionFunction (projectiveLine k) ↦ RationalChowGroup δ 0)
    (sourceDimension_eq k)

def baseCycle (c : cyclesOfDegree ℚ (sourceDimension k) 0) :
    cyclesOfDegree ℚ (dimensionFunction k) 0 :=
  ⟨c.val, by rw [← sourceDimension_eq k]; exact c.property⟩

def coverCycle (c : cyclesOfDegree ℚ (dimensionFunction k) 0) :
    cyclesOfDegree ℚ (sourceDimension k) 0 :=
  ⟨c.val, by rw [sourceDimension_eq k]; exact c.property⟩

private theorem cast_classMap {X : Scheme.{u}} [IsNoetherian X]
    {δ ε : DimensionFunction X} (h : δ = ε) (c : cyclesOfDegree ℚ δ 0) :
    LinearEquiv.cast (R := ℚ)
        (M := fun d : DimensionFunction X ↦ RationalChowGroup d 0) h
        (rationalClassMap δ 0 c) =
      rationalClassMap ε 0 ⟨c.val, by cases h; exact c.property⟩ := by
  cases h
  rfl

private theorem cast_symm_classMap {X : Scheme.{u}} [IsNoetherian X]
    {δ ε : DimensionFunction X} (h : δ = ε) (c : cyclesOfDegree ℚ ε 0) :
    (LinearEquiv.cast (R := ℚ)
        (M := fun d : DimensionFunction X ↦ RationalChowGroup d 0) h).symm
        (rationalClassMap ε 0 c) =
      rationalClassMap δ 0 ⟨c.val, by cases h; exact c.property⟩ := by
  cases h
  rfl

private theorem cast_degree_classMap {X : Scheme.{u}} [IsNoetherian X]
    {δ ε : DimensionFunction X} (h : ε = δ)
    (D : RationalChowGroup δ 0 →ₗ[ℚ] ℚ) (d : Cycles X ℚ →ₗ[ℚ] ℚ)
    (hD : ∀ c : cyclesOfDegree ℚ δ 0, D (rationalClassMap δ 0 c) = d c.val)
    (c : cyclesOfDegree ℚ ε 0) :
    D (LinearEquiv.cast (R := ℚ)
      (M := fun g : DimensionFunction X ↦ RationalChowGroup g 0) h
      (rationalClassMap ε 0 c)) = d c.val := by
  cases h
  exact hD c

private theorem cast_cycle_mem {X : Scheme.{u}} {δ ε : DimensionFunction X}
    (h : ε = δ) (c : cyclesOfDegree ℚ ε 0) : c.val ∈ cyclesOfDegree ℚ δ 0 := by
  cases h
  exact c.property

@[simp] theorem chowEquiv_classMap (c : cyclesOfDegree ℚ (sourceDimension k) 0) :
    chowEquiv k (rationalClassMap (sourceDimension k) 0 c) =
      rationalClassMap (dimensionFunction k) 0 (baseCycle k c) := by
  exact cast_classMap (sourceDimension_eq k) c

@[simp] theorem chowEquiv_symm_classMap (c : cyclesOfDegree ℚ (dimensionFunction k) 0) :
    (chowEquiv k).symm (rationalClassMap (dimensionFunction k) 0 c) =
      rationalClassMap (sourceDimension k) 0 (coverCycle k c) := by
  exact cast_symm_classMap (sourceDimension_eq k) c

/-- The original finite flat pullback, on its exact original source and target quotients. -/
def actualPull : BaseChow k →ₗ[ℚ] CoverChow k :=
  rationalChowFiniteFlatPullback k (baseStructure k) (square k) 0

/-- The original degree-weighted finite pushforward. -/
def actualPush : CoverChow k →ₗ[ℚ] BaseChow k :=
  rationalChowFinitePushforward k (baseStructure k) (square k) 0

/-- Positive rank is computed from the original chart algebra. -/
theorem push_pull (z : BaseChow k) : actualPush k (actualPull k z) = 2 • z := by
  exact rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq
    k (baseStructure k) (square k) 0 2 (square_finrank k) z

/-- Nonnegative structural dimension makes every zero-dimensional point closed. -/
theorem isClosed_of_dimension_zero (x : projectiveLine k)
    (hx : dimensionFunction k x = 0) : IsClosed ({x} : Set (projectiveLine k)) := by
  apply isClosed_of_closure_subset
  intro y hy
  apply Set.mem_singleton_iff.mpr
  have hle : y ≤ x := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
  by_contra hne
  have hnot : ¬ x ≤ y := by
    intro hge
    exact hne (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq)
  have hlt := (dimensionFunction k).strictMono (lt_iff_le_not_ge.mpr ⟨hle, hnot⟩)
  have hn := DimensionFunction.ofLocallyOfFiniteType_nonneg k (projectiveLine k)
    (baseStructure k) y
  change 0 ≤ dimensionFunction k y at hn
  rw [hx] at hlt
  omega

private theorem residueFieldDegree_eq_one_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    residueFieldDegree f x = 1 := by
  let : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (Y.residueField (f.base x)) (X.residueField x) = 1
  apply finrank_eq_one (1 : X.residueField x) one_ne_zero
  intro w
  obtain ⟨c, hc⟩ := (residueFieldMap_bijective_of_surjectiveOnStalks f x).surjective w
  exact ⟨c, (mul_one _).trans hc⟩

private theorem multiplicity_eq_one_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) : finiteFiberMultiplicity f x = 1 := by
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  let : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hm :
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    Algebra.FormallyUnramified.map_maximalIdeal
      (R := Y.presheaf.stalk (f.base x)) (S := X.presheaf.stalk x)
  rw [finiteFiberMultiplicity_eq_length_quotient, hm]
  change (Module.length (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x))).toNat = 1
  rw [Module.length_eq_of_surjective
    (IsLocalRing.residue_surjective (R := X.presheaf.stalk x)), Module.length_eq_one]
  rfl

variable [hAlgClosed : IsAlgClosed k]

include hAlgClosed

/-- The actual square-map residue extension at a closed point has degree one.
This uses its actual rational-point section and the unchanged scalar tower. -/
theorem residueFieldDegree_eq_one (x : projectiveLine k)
    (hx : IsClosed ({x} : Set (projectiveLine k))) :
    residueFieldDegree (square k) x = 1 := by
  let s := pointOfClosedPoint (baseStructure k) x hx
  have hs : s ≫ baseStructure k = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id (baseStructure k) s hs
  have hsf : (s ≫ square k) ≫ baseStructure k = 𝟙 _ := by
    rw [Category.assoc, over_base, hs]
  let : IsClosedImmersion (s ≫ square k) :=
    isClosedImmersion_of_comp_eq_id (baseStructure k) (s ≫ square k) hsf
  have h := residueFieldDegree_comp_of_source_surjectiveOnStalks
    s (square k) (IsLocalRing.closedPoint k)
  rw [residueFieldDegree_eq_one_of_surjectiveOnStalks] at h
  simpa only [s, pointOfClosedPoint_apply] using h.symm

theorem finitePushforwardDegree_eq_one (W : IntegralClosedSubscheme (projectiveLine k))
    (hW : supportDegree (dimensionFunction k) W = 0) :
    finitePushforwardDegree (square k) W = 1 := by
  rw [finitePushforwardDegree_eq_residueFieldDegree]
  exact residueFieldDegree_eq_one k _ (isClosed_of_dimension_zero k _ hW)

/-- The unchanged coefficient sum of any original zero-cycle is preserved. -/
theorem coefficientSum_push (c : Cycles (projectiveLine k) ℚ)
    (hc : c ∈ cyclesOfDegree ℚ (dimensionFunction k) 0) :
    coefficientSum k ℚ (finitePushforward ℚ (square k) c) =
      coefficientSum k ℚ c := by
  classical
  let L : Cycles (projectiveLine k) ℚ →ₗ[ℚ] ℚ :=
    (coefficientSum k ℚ).comp (finitePushforward ℚ (square k)) - coefficientSum k ℚ
  have hle : cyclesOfDegree ℚ (dimensionFunction k) 0 ≤ LinearMap.ker L := by
    change Finsupp.supported ℚ ℚ {W | supportDegree (dimensionFunction k) W = 0} ≤ _
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨W, hW, rfl⟩
    change coefficientSum k ℚ (finitePushforward ℚ (square k) (Finsupp.single W 1)) -
      coefficientSum k ℚ (Finsupp.single W 1) = 0
    rw [finitePushforward_single, finitePushforwardDegree_eq_one k W hW]
    simp [fundamentalCycle]
  have h := hle hc
  exact sub_eq_zero.mp h

/-- Finite pushforward preserves actual ordinary Chow degree over the algebraically closed base. -/
theorem degree_push (z : CoverChow k) :
    rationalChowDegree k (actualPush k z) =
      rationalChowDegree k (chowEquiv k z) := by
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective (sourceDimension k) 0 z
  have hcast : rationalChowDegree k
      (chowEquiv k (rationalClassMap (sourceDimension k) 0 c)) =
      coefficientSum k ℚ c.val :=
    cast_degree_classMap (sourceDimension_eq k) (rationalChowDegree k)
      (coefficientSum k ℚ) (fun _ => rfl) c
  have hc := cast_cycle_mem (sourceDimension_eq k) c
  calc
    rationalChowDegree k (actualPush k (rationalClassMap (sourceDimension k) 0 c)) =
        coefficientSum k ℚ (finitePushforward ℚ (square k) c.val) := rfl
    _ = coefficientSum k ℚ c.val := coefficientSum_push k c.val hc
    _ = _ := hcast.symm

/-- The degree of actual flat pullback doubles, derived from geometric rank two. -/
theorem degree_pull (z : BaseChow k) :
    rationalChowDegree k (chowEquiv k (actualPull k z)) =
      2 * rationalChowDegree k z := by
  rw [← degree_push, push_pull, map_nsmul]
  simp [two_mul]

private theorem multiplicity_eq_two_of_singleton (y : projectiveLine k)
    (hy : square k y = y) (hu : ∀ x, square k x = y → x = y)
    (hc : IsClosed ({y} : Set (projectiveLine k))) :
    finiteFiberMultiplicity (square k) y = 2 := by
  let : Unique {x : projectiveLine k // (square k).base x = y} :=
    ⟨⟨⟨y, hy⟩⟩, fun x => Subtype.ext (hu x.val x.property)⟩
  have h := finiteFiberDegree_eq_sum (square k) y
  rw [finiteFiberDegree_eq_finrank, square_finrank, finsum_unique] at h
  change 2 = residueFieldDegree (square k) y * finiteFiberMultiplicity (square k) y at h
  rw [residueFieldDegree_eq_one k y hc, one_mul] at h
  exact h.symm

omit [IsAlgClosed k] in
/-- Zero is an actual nongeneric point of the connected source scheme. -/
theorem zero_ne_genericPoint :
    projectiveLineZero k ≠ genericPoint (projectiveLine k) := by
  intro h
  apply zero_notMem_yChart k
  rw [h]
  exact ⟨genericPoint (Spec (.of (Polynomial k))),
    genericPoint_eq_of_isOpenImmersion (projectiveLineYChart k)⟩

/-- The actual local scheme fiber over zero has length two. -/
theorem zero_finiteFiberMultiplicity :
    finiteFiberMultiplicity (square k) (projectiveLineZero k) = 2 := by
  apply multiplicity_eq_two_of_singleton k _ (zero_fixed k)
    (fun x hx => (square_eq_zero_iff k x).mp hx)
  exact isClosed_of_dimension_zero k _
    (dimensionFunction_eq_zero_of_ne_genericPoint k _ (zero_ne_genericPoint k))

/-- The second actual branch fiber, in the original infinity chart, also has length two. -/
theorem infinity_finiteFiberMultiplicity :
    finiteFiberMultiplicity (square k) (projectiveLineInfinity k) = 2 := by
  apply multiplicity_eq_two_of_singleton k _ (infinity_fixed k)
    (fun x hx => (square_eq_infinity_iff k x).mp hx)
  exact isClosed_of_dimension_zero k _
    (dimensionFunction_eq_zero_of_ne_genericPoint k _ (Infinity.ne_genericPoint k))

/-- The actual branch multiplicity obstructs formal unramifiedness. -/
theorem square_not_formallyUnramified : ¬ FormallyUnramified (square k) := by
  intro h
  let := h
  have hm := multiplicity_eq_one_of_formallyUnramified (square k) (projectiveLineZero k)
  rw [zero_finiteFiberMultiplicity] at hm
  exact (by decide : (2 : ℕ) ≠ 1) hm

/-- This finite flat connected degree-two map is genuinely branched. -/
theorem square_not_etale : ¬ Etale (square k) := by
  intro h
  let := h
  exact square_not_formallyUnramified k inferInstance

omit hAlgClosed in
private theorem finiteFiberPullback_point_of_singleton (y : projectiveLine k)
    (hy : square k y = y) (hu : ∀ x, square k x = y → x = y)
    (hm : finiteFiberMultiplicity (square k) y = 2) :
    finiteFiberPullback (square k) ℚ (fundamentalCycle ℚ (pointSupport (projectiveLine k) y)) =
      2 • fundamentalCycle ℚ (pointSupport (projectiveLine k) y) := by
  classical
  have hp (x : projectiveLine k) :
      finiteFiberPullback (square k) ℚ
          (fundamentalCycle ℚ (pointSupport (projectiveLine k) y))
          (pointSupport (projectiveLine k) x) =
        (2 • fundamentalCycle ℚ (pointSupport (projectiveLine k) y))
          (pointSupport (projectiveLine k) x) := by
    rw [finiteFiberPullback_apply_pointSupport]
    by_cases h : x = y
    · subst x
      simp [hy, hm, fundamentalCycle]
    · have hxy : pointSupport (projectiveLine k) x ≠ pointSupport (projectiveLine k) y :=
        fun he => h ((pointEquivIntegralClosedSubscheme (projectiveLine k)).injective he)
      have hfy : pointSupport (projectiveLine k) (square k x) ≠
          pointSupport (projectiveLine k) y := by
        intro he
        exact h (hu x ((pointEquivIntegralClosedSubscheme (projectiveLine k)).injective he))
      simp [fundamentalCycle, hxy, hfy]
  ext W
  simpa only [pointSupport_ambientGenericPoint] using hp (ambientGenericPoint W)

/-- The original flat pullback of infinity is its double, on the unchanged actual point cycle. -/
theorem chowEquiv_pull_infinity :
    chowEquiv k (actualPull k (Infinity.rationalClass k)) =
      (2 : ℚ) • Infinity.rationalClass k := by
  change chowEquiv k (rationalClassMap (sourceDimension k) 0
    (gradedFiniteFiberPullback (square k) k ℚ (baseStructure k) 0
      (pointCycle k ℚ (projectiveLineInfinity k) (Infinity.ne_genericPoint k)))) = _
  rw [chowEquiv_classMap]
  change rationalClassMap (dimensionFunction k) 0
      (baseCycle k (gradedFiniteFiberPullback (square k) k ℚ (baseStructure k) 0
        (pointCycle k ℚ (projectiveLineInfinity k) (Infinity.ne_genericPoint k)))) =
    (2 : ℚ) • rationalClassMap (dimensionFunction k) 0
      (pointCycle k ℚ (projectiveLineInfinity k) (Infinity.ne_genericPoint k))
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  simpa only [baseCycle, gradedFiniteFiberPullback_val, pointCycle, SetLike.val_smul,
    Submodule.coe_add,
    two_smul] using finiteFiberPullback_point_of_singleton k _ (infinity_fixed k)
      (fun x hx => (square_eq_infinity_iff k x).mp hx) (infinity_finiteFiberMultiplicity k)

end HodgeConjecture.ProjectiveLineSquareChow

end
