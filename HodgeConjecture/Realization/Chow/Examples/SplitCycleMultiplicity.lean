module

public import HodgeConjecture.Realization.Chow.Examples.SplitCycleOperations
public import HodgeConjecture.Correspondence.Examples.SplitProductGeometry
public import HodgeConjecture.Correspondence.Examples.SplitPointMultiplicity

@[expose] public section

/-!
# Geometric coefficients of split cycle operations

The coefficients in flat pullback are lengths of actual fiber stalks over
the actual ambient stalks. The coefficients in proper pushforward are
degrees of actual residue-field extensions to scheme-theoretic images.
Both are one for finite split point schemes.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

namespace SplitZeroCycles

open SplitPointGeometry Classical
open scoped BigOperators

variable (K : Type u) [Field K]
variable {S I : Type u} [Finite S] [Finite I]

/-- The actual local length defining the coefficient of a fiber point in
flat pullback. Scalars act through the scheme-theoretic fiber inclusion. -/
def pointFiberMultiplicity (f : S → I) (i : I)
    (x : (Limits.pullback (mapOfFunction K f) (pointInclusion K I i) : Scheme)) : ℕ∞ :=
  let p := Limits.pullback.fst (mapOfFunction K f) (pointInclusion K I i)
  letI : Algebra ((scheme K S).presheaf.stalk (p.base x))
      ((Limits.pullback (mapOfFunction K f) (pointInclusion K I i) : Scheme).presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  Module.length ((scheme K S).presheaf.stalk (p.base x))
    ((Limits.pullback (mapOfFunction K f) (pointInclusion K I i) : Scheme).presheaf.stalk x)

omit [Finite I] in
@[simp]
theorem pointFiberMultiplicity_eq_one (f : S → I) (i : I)
    (x : (Limits.pullback (mapOfFunction K f) (pointInclusion K I i) : Scheme)) :
    pointFiberMultiplicity K f i x = 1 :=
  stalkMap_length_of_isOpenImmersion K S
    (Limits.pullback.fst (mapOfFunction K f) (pointInclusion K I i)) x

/-- The actual residue-field extension degree of an integral component over
its scheme-theoretic image, with scalars supplied by the actual residue map. -/
def imageDegree (f : S → I) (W : IntegralClosedSubscheme K S) (x : W.val.subscheme) : ℕ :=
  let g := imageIntegralSubschemeMap K f W
  letI : Algebra ((imageIntegralSubscheme K f W).val.subscheme.residueField (g.base x))
      (W.val.subscheme.residueField x) := (g.residueFieldMap x).hom.toAlgebra
  Module.finrank ((imageIntegralSubscheme K f W).val.subscheme.residueField (g.base x))
    (W.val.subscheme.residueField x)

omit [Finite I] in
@[simp]
theorem imageDegree_eq_one (f : S → I) (W : IntegralClosedSubscheme K S)
    (x : W.val.subscheme) : imageDegree K f W x = 1 :=
  residueFieldMap_finrank_of_isIso (imageIntegralSubschemeMap K f W) x

variable (R : Type v) [CommRing R]

/-- The fundamental cycle of the actual inverse-image subscheme, expressed
on its point generators with their actual ambient-stalk module lengths. -/
def fiberCycle [Fintype S] (f : S → I) (i : I) : Cycles K S R :=
  ∑ s : {s // f s = i},
    (pointFiberMultiplicity K f i
      ((pointFiberIso K f i).hom.base (labelEquivScheme K {s // f s = i} s))).toNat •
        pointCycle K S R s.val

theorem fiberCycle_eq_sum [Fintype S] (f : S → I) (i : I) :
    fiberCycle K R f i = ∑ s : {s // f s = i}, pointCycle K S R s.val := by
  simp [fiberCycle]

/-- The previously constructed flat pullback has exactly the conventional
fundamental-cycle coefficients of the actual scheme-theoretic fiber. -/
theorem pullback_pointCycle_eq_fiberCycle [Fintype S] (f : S → I) (i : I) :
    pullback K R f (pointCycle K I R i) = fiberCycle K R f i := by
  rw [pullback_pointCycle, fiberCycle_eq_sum, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

omit [Finite I] in
/-- The previously constructed proper pushforward has exactly the degree
of the actual residue-field extension as its coefficient on each generator. -/
theorem pushforward_single_eq_imageDegree (f : S → I)
    (W : IntegralClosedSubscheme K S) (x : W.val.subscheme) :
    pushforward K R f (Finsupp.single W 1) =
      imageDegree K f W x • Finsupp.single (imageIntegralSubscheme K f W) 1 := by
  simp [pushforward]

end SplitZeroCycles

end

end HodgeConjecture
