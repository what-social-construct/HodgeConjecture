module

public import HodgeConjecture.Realization.Betti.Examples.SplitHodgeStructure
public import HodgeConjecture.Realization.Chow.Examples.SplitOrdinaryChow
public import HodgeConjecture.Correspondence.Examples.SplitFiniteCover
public import HodgeConjecture.Geometry.AffineComplexPoints
public import HodgeConjecture.Realization.HodgeClasses
public import HodgeConjecture.Realization.Transfer
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Native degree-zero transfer for the actual finite split cover

The maps are singular pullback and the sum over actual complex-point fibers.
Their degree formula is proved from the independently classified points. For
the split projection its degree agrees with the original geometric rank.

The ordinary Chow comparison retains the original cycle representatives and
commutes with the original finite Chow maps. The Hodge target and its full
basis come from the separately computed complexification and point evaluation,
before any choice of cycles for an aggregate certificate.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SplitComplexPoints

open AlgebraicGeometry CategoryTheory

variable (I : Type) [Finite I]

/-- The native analytic scheme-point topology is the existing regular-function
evaluation topology on the same original algebra-valued points. -/
def schemePointHomeomorph :
    Scheme.ComplexPoints (SplitPointGeometry.toBase ℂ I) ≃ₜ Point I :=
  AffineComplexPoints.homeomorph (I → ℂ)

variable {I} {S : Type} [Finite S]

/-- This comparison preserves the map induced by the actual scheme morphism. -/
theorem schemePointHomeomorph_symm_map (f : S → I) (p : Point S) :
    Scheme.ComplexPoints.map (SplitPointGeometry.mapOfFunction ℂ f)
      (SplitPointGeometry.mapOfFunction_toBase ℂ f)
      ((schemePointHomeomorph S).symm p) =
        (schemePointHomeomorph I).symm (map f p) := by
  apply Scheme.ComplexPoints.ext
  exact schemeMorphism_map f p

/-- Naturality on the original scheme-valued points, with no relabeling of
the geometric morphism. -/
theorem schemePointHomeomorph_map (f : S → I)
    (p : Scheme.ComplexPoints (SplitPointGeometry.toBase ℂ S)) :
    schemePointHomeomorph I
      (Scheme.ComplexPoints.map (SplitPointGeometry.mapOfFunction ℂ f)
        (SplitPointGeometry.mapOfFunction_toBase ℂ f) p) =
      map f (schemePointHomeomorph S p) := by
  apply (schemePointHomeomorph I).symm.injective
  simpa only [Homeomorph.symm_apply_apply] using
    schemePointHomeomorph_symm_map f (schemePointHomeomorph S p)

end HodgeConjecture.SplitComplexPoints

namespace HodgeConjecture.SplitBetti

open Classical
open scoped BigOperators

variable {I S : Type} [Finite I] [Fintype S]

/-- A constant number of points in every actual fiber gives the native
singular push--pull degree formula. -/
theorem pushforward_pullback_of_card (f : S → I) (d : ℕ)
    (hf : ∀ i, (Finset.univ.filter (fun s : S ↦ f s = i)).card = d)
    (h : Cohomology I) :
    pushforward f (pullback f h) = (d : ℚ) • h := by
  apply (coordinates I).injective
  ext i
  simp only [coordinates_pushforward, coordinates_pullback, map_smul,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ s, if f s = i then coordinates I h (f s) else 0) =
        ∑ s, if f s = i then coordinates I h i else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : f s = i <;> simp [hs]
    _ = (d : ℚ) * coordinates I h i := by
      rw [← Finset.sum_filter]
      simp [hf i, nsmul_eq_mul]

/-- The same native degree law with cardinality of the point-fiber subtype. -/
theorem pushforward_pullback_of_fiberCard (f : S → I) (d : ℕ)
    (hf : ∀ i, Fintype.card {s : S // f s = i} = d)
    (h : Cohomology I) :
    pushforward f (pullback f h) = (d : ℚ) • h := by
  apply pushforward_pullback_of_card f d
  intro i
  simpa only [Fintype.card_subtype] using hf i

/-- Positive constant fibers supply rational transfer on native singular
cohomology; injectivity is a consequence of this proved degree identity. -/
def rationalDegreeTransfer (f : S → I) (d : ℕ) (hd : d ≠ 0)
    (hf : ∀ i, (Finset.univ.filter (fun s : S ↦ f s = i)).card = d) :
    RationalDegreeTransfer (Cohomology S) (Cohomology I) where
  pull := (pullback f).toLinearMap
  push := pushforward f
  degree := d
  degree_ne_zero := hd
  push_comp_pull := by
    apply LinearMap.ext
    intro h
    exact pushforward_pullback_of_card f d hf h

variable (I) [Fintype I] (J : Type) [Fintype J]

/-- Every fiber of the original projection has exactly one point per sheet. -/
theorem projection_fiber_card (i : I) :
    (Finset.univ.filter (fun s : I × J ↦ s.1 = i)).card = Fintype.card J := by
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun s ↦ s.val.2
      invFun := fun j ↦ ⟨(i, j), rfl⟩
      left_inv := by
        rintro ⟨⟨i', j⟩, h⟩
        cases h
        rfl
      right_inv := fun _ ↦ rfl }

/-- Transfer for the actual finite étale projection of split schemes. -/
def projectionTransfer [Nonempty J] :
    RationalDegreeTransfer (Cohomology (I × J)) (Cohomology I) :=
  rationalDegreeTransfer Prod.fst (Fintype.card J) Fintype.card_ne_zero
    (projection_fiber_card I J)

/-- The cohomological degree is the rank of the same original scheme morphism. -/
theorem projectionTransfer_degree_eq_finrank [Nonempty J]
    (x : SplitPointGeometry.scheme ℂ I) :
    (projectionTransfer I J).degree =
      (SplitPointGeometry.coverProjection ℂ I J).finrank x := by
  change Fintype.card J = _
  exact (SplitPointGeometry.coverProjection_finrank ℂ I J x).symm

/-- The native transfer of the concrete degree-two cover from four points
to two points. -/
abbrev twoSheetTransfer :
    RationalDegreeTransfer (Cohomology (Fin 2 × Fin 2)) (Cohomology (Fin 2)) :=
  projectionTransfer (Fin 2) (Fin 2)

@[simp]
theorem twoSheetTransfer_degree : twoSheetTransfer.degree = 2 := by
  change Fintype.card (Fin 2) = 2
  exact Fintype.card_fin 2

end HodgeConjecture.SplitBetti

namespace HodgeConjecture.SplitOrdinaryBetti

open Classical AlgebraicGeometry CategoryTheory

variable (I : Type) [Finite I]

/-- The cycle class of the actual ordinary Chow group. Its comparison retains
the original integral supports and rational cycle coefficients. -/
def cycleClass : SplitZeroCycles.OrdinaryChow ℂ I ≃ₗ[ℚ] SplitBetti.Cohomology I :=
  (SplitZeroCycles.ordinaryChowEquiv ℂ I).trans (SplitBetti.cycleClass I)

/-- The actual reduced point cycle realizes as its characteristic singular
zero-cocycle, with its original normalization. -/
theorem coordinates_cycleClass_ordinaryPointClass (j i : I) :
    SplitBetti.coordinates I
      (cycleClass I (SplitZeroCycles.ordinaryPointClass ℂ I j)) i =
      if j = i then 1 else 0 := by
  change SplitBetti.coordinates I
    (SplitBetti.cycleClass I (SplitZeroCycles.ordinaryChowEquiv ℂ I
      (SplitZeroCycles.ordinaryPointClass ℂ I j))) i = _
  rw [SplitZeroCycles.ordinaryChowEquiv_ordinaryPointClass]
  exact SplitBetti.cycleClass_pointCycle I j i

/-- The independent degree-zero Hodge subspace on native singular cohomology,
together with the cycle map from the ordinary structural Chow group. -/
def hodgeModel : RationalHodgeCycleClassModel
    (SplitZeroCycles.OrdinaryChow ℂ I) (SplitBetti.Cohomology I) where
  hodgeClasses := SplitHodgeStructure.rationalHodgeClasses I
  cycleClass := (cycleClass I).toLinearMap
  cycleClass_lands := by
    intro h _
    exact SplitHodgeStructure.all_hodge I h

/-- This equivalence uses the independently established Hodge computation,
without using the cycle map or its range. -/
def fullHodgeEquiv : (hodgeModel I).hodgeClasses ≃ₗ[ℚ] SplitBetti.Cohomology I :=
  LinearEquiv.ofBijective (hodgeModel I).hodgeClasses.subtype
    ⟨Subtype.val_injective, fun h ↦
      ⟨⟨h, SplitHodgeStructure.all_hodge I h⟩, rfl⟩⟩

/-- Evaluation on the actual classified complex points gives coordinates
on the entire fixed Hodge target. -/
def fullHodgeCoordinates : (hodgeModel I).hodgeClasses ≃ₗ[ℚ] (I → ℚ) :=
  (fullHodgeEquiv I).trans (SplitBetti.coordinates I)

/-- The full target basis is fixed before any aggregate cycles are chosen. -/
def fullHodgeBasis : Module.Basis I ℚ (hodgeModel I).hodgeClasses :=
  Module.Basis.ofEquivFun (fullHodgeCoordinates I)

theorem fullHodgeBasis_coordinates :
    (fullHodgeBasis I).equivFun = fullHodgeCoordinates I :=
  Module.Basis.equivFun_ofEquivFun (fullHodgeCoordinates I)

theorem coordinates_fullHodgeBasis (j i : I) :
    SplitBetti.coordinates I (fullHodgeBasis I j : SplitBetti.Cohomology I) i =
      if j = i then 1 else 0 := by
  change fullHodgeCoordinates I (fullHodgeBasis I j) i = _
  rw [← fullHodgeBasis_coordinates]
  simp

/-- Ordinary point classes have the normalization of the independently fixed
full Hodge basis. -/
theorem cycleClass_ordinaryPointClass (j : I) :
    cycleClass I (SplitZeroCycles.ordinaryPointClass ℂ I j) =
      (fullHodgeBasis I j : SplitBetti.Cohomology I) := by
  apply (SplitBetti.coordinates I).injective
  ext i
  rw [coordinates_cycleClass_ordinaryPointClass, coordinates_fullHodgeBasis]

variable (p : SplitPointGeometry.scheme ℂ I ⟶ Spec (CommRingCat.of ℂ))
  [LocallyOfFiniteType p]

/-- The same cycle map with an explicit structure morphism, so that the
sources of the original Chow maps remain exact rather than identified by fiat. -/
def cycleClassOfStructure :
    SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType ℂ
        (SplitPointGeometry.scheme ℂ I) p) 0 ≃ₗ[ℚ] SplitBetti.Cohomology I :=
  (SplitZeroCycles.ordinaryChowEquivOfStructure ℂ I p).trans (SplitBetti.cycleClass I)

variable {I} {S : Type} [Finite S]

/-- The comparison square for the original ordinary finite flat pullback. -/
theorem cycleClassOfStructure_finiteFlatPullback (f : S → I)
    (z : SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType ℂ
        (SplitPointGeometry.scheme ℂ I) p) 0) :
    cycleClassOfStructure S (SplitPointGeometry.mapOfFunction ℂ f ≫ p)
      (SchemeCycles.rationalChowFiniteFlatPullback ℂ p
        (SplitPointGeometry.mapOfFunction ℂ f) 0 z) =
      SplitBetti.pullback f (cycleClassOfStructure I p z) := by
  simp only [cycleClassOfStructure, LinearEquiv.trans_apply,
    SplitZeroCycles.ordinaryChowEquivOfStructure_finiteFlatPullback,
    SplitBetti.cycleClass_pullback]

/-- The comparison square for the original ordinary finite pushforward. -/
theorem cycleClassOfStructure_finitePushforward [Fintype S] (f : S → I)
    (z : SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType ℂ
        (SplitPointGeometry.scheme ℂ S) (SplitPointGeometry.mapOfFunction ℂ f ≫ p)) 0) :
    cycleClassOfStructure I p
      (SchemeCycles.rationalChowFinitePushforward ℂ p
        (SplitPointGeometry.mapOfFunction ℂ f) 0 z) =
      SplitBetti.pushforward f
        (cycleClassOfStructure S (SplitPointGeometry.mapOfFunction ℂ f ≫ p) z) := by
  simp only [cycleClassOfStructure, LinearEquiv.trans_apply,
    SplitZeroCycles.ordinaryChowEquivOfStructure_finitePushforward,
    SplitBetti.cycleClass_pushforward]

omit p in
/-- Canonical ordinary finite flat pullback commutes with the native singular
pullback of the identical original geometric morphism. -/
theorem cycleClass_pullback (f : S → I) (z : SplitZeroCycles.OrdinaryChow ℂ I) :
    cycleClass S (SplitZeroCycles.ordinaryChowPullback ℂ f z) =
      SplitBetti.pullback f (cycleClass I z) := by
  simp only [cycleClass, LinearEquiv.trans_apply,
    SplitZeroCycles.ordinaryChowEquiv_pullback, SplitBetti.cycleClass_pullback]

omit p in
/-- Canonical ordinary finite pushforward commutes with native singular
transfer on the identical original geometric morphism. -/
theorem cycleClass_pushforward [Fintype S] (f : S → I)
    (z : SplitZeroCycles.OrdinaryChow ℂ S) :
    cycleClass I (SplitZeroCycles.ordinaryChowPushforward ℂ f z) =
      SplitBetti.pushforward f (cycleClass S z) := by
  simp only [cycleClass, LinearEquiv.trans_apply,
    SplitZeroCycles.ordinaryChowEquiv_pushforward, SplitBetti.cycleClass_pushforward]

omit p in
/-- The pushforward comparison in the exact linear-map form used by transfer
coverage certificates. -/
theorem cycleClass_pushforward_comp [Fintype S] (f : S → I) :
    (hodgeModel I).cycleClass.comp (SplitZeroCycles.ordinaryChowPushforward ℂ f) =
      (SplitBetti.pushforward f).comp (cycleClass S).toLinearMap := by
  apply LinearMap.ext
  intro z
  exact cycleClass_pushforward f z

end HodgeConjecture.SplitOrdinaryBetti

end
