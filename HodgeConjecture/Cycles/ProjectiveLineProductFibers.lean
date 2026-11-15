module

public import HodgeConjecture.Cycles.PointSupport
public import HodgeConjecture.Geometry.ProjectiveLineProduct
public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

/-!
# Geometric fibers of the projective-line product

The inverse images of reduced point closures under the two projections of
`P¹ × P¹` are actual closed subschemes. The ideal-sheaf pullback agrees with
the scheme-theoretic fiber product, and its support is the inverse image of
the point closure. Integrality and codimension one are separate obligations
before these fibers define homogeneous Chow classes.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineProductFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace SchemeCycles

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The scheme-theoretic inverse image of a reduced point closure under the
first projection. -/
def firstFiberIdeal (x : projectiveLine k) :
    (projectiveLineProduct k).IdealSheafData :=
  ((pointSupport (projectiveLine k) x).val).comap (projectiveLineProductFst k)

/-- The scheme-theoretic inverse image of a reduced point closure under the
second projection. -/
def secondFiberIdeal (x : projectiveLine k) :
    (projectiveLineProduct k).IdealSheafData :=
  ((pointSupport (projectiveLine k) x).val).comap (projectiveLineProductSnd k)

/-- The actual closed fiber subscheme of the first projection. -/
abbrev firstFiberScheme (x : projectiveLine k) : Scheme.{u} :=
  (firstFiberIdeal k x).subscheme

/-- The actual closed fiber subscheme of the second projection. -/
abbrev secondFiberScheme (x : projectiveLine k) : Scheme.{u} :=
  (secondFiberIdeal k x).subscheme

/-- The first fiber's closed immersion into the product. -/
abbrev firstFiberInclusion (x : projectiveLine k) :
    firstFiberScheme k x ⟶ projectiveLineProduct k :=
  (firstFiberIdeal k x).subschemeι

/-- The second fiber's closed immersion into the product. -/
abbrev secondFiberInclusion (x : projectiveLine k) :
    secondFiberScheme k x ⟶ projectiveLineProduct k :=
  (secondFiberIdeal k x).subschemeι

instance firstFiberInclusion_isClosedImmersion (x : projectiveLine k) :
    IsClosedImmersion (firstFiberInclusion k x) := inferInstance

instance secondFiberInclusion_isClosedImmersion (x : projectiveLine k) :
    IsClosedImmersion (secondFiberInclusion k x) := inferInstance

/-- The first closed fiber is the actual scheme-theoretic pullback of the
reduced point closure. -/
def firstFiberIso (x : projectiveLine k) :
    firstFiberScheme k x ≅
      pullback (projectiveLineProductFst k)
        (pointSupport (projectiveLine k) x).val.subschemeι :=
  (pointSupport (projectiveLine k) x).val.comapIso (projectiveLineProductFst k)

/-- The second closed fiber is the actual scheme-theoretic pullback of the
reduced point closure. -/
def secondFiberIso (x : projectiveLine k) :
    secondFiberScheme k x ≅
      pullback (projectiveLineProductSnd k)
        (pointSupport (projectiveLine k) x).val.subschemeι :=
  (pointSupport (projectiveLine k) x).val.comapIso (projectiveLineProductSnd k)

/-- The first fiber has exactly the inverse-image support of the reduced
point closure. -/
theorem mem_firstFiber_support (x : projectiveLine k)
    (y : projectiveLineProduct k) :
    y ∈ (firstFiberIdeal k x).support ↔
      (projectiveLineProductFst k).base y ∈ closure ({x} : Set (projectiveLine k)) := by
  change y ∈ ((pointSupport (projectiveLine k) x).val.comap
    (projectiveLineProductFst k)).support ↔ _
  rw [Scheme.IdealSheafData.support_comap, pointSupport_support]
  rfl

/-- The second fiber has exactly the inverse-image support of the reduced
point closure. -/
theorem mem_secondFiber_support (x : projectiveLine k)
    (y : projectiveLineProduct k) :
    y ∈ (secondFiberIdeal k x).support ↔
      (projectiveLineProductSnd k).base y ∈ closure ({x} : Set (projectiveLine k)) := by
  change y ∈ ((pointSupport (projectiveLine k) x).val.comap
    (projectiveLineProductSnd k)).support ↔ _
  rw [Scheme.IdealSheafData.support_comap, pointSupport_support]
  rfl

/-- Infinity is closed because it is the complement of the first affine
chart. -/
theorem infinity_isClosed :
    IsClosed ({projectiveLineInfinity k} : Set (projectiveLine k)) := by
  rw [← compl_range_projectiveLineXChart]
  exact (projectiveLineXChart k).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The first infinity fiber has precisely the points whose first
projection is infinity. -/
theorem mem_firstInfinityFiber_support (y : projectiveLineProduct k) :
    y ∈ (firstFiberIdeal k (projectiveLineInfinity k)).support ↔
      (projectiveLineProductFst k).base y = projectiveLineInfinity k := by
  rw [mem_firstFiber_support, (infinity_isClosed k).closure_eq]
  rfl

/-- The second infinity fiber has precisely the points whose second
projection is infinity. -/
theorem mem_secondInfinityFiber_support (y : projectiveLineProduct k) :
    y ∈ (secondFiberIdeal k (projectiveLineInfinity k)).support ↔
      (projectiveLineProductSnd k).base y = projectiveLineInfinity k := by
  rw [mem_secondFiber_support, (infinity_isClosed k).closure_eq]
  rfl

end

end HodgeConjecture.ProjectiveLineProductFibers
