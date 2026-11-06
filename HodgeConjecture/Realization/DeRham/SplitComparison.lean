module

public import HodgeConjecture.Realization.DeRham.FiniteUnramifiedTrace
public import HodgeConjecture.Realization.Betti.Examples.SplitHodgeStructure

@[expose] public section

/-!
# De Rham trace and the existing split Chow–Betti comparison

The algebraic target is the kernel of the actual Kähler derivation of the
coordinate algebra. Its coordinates come from vanishing of differentials
of a finite product of fields. Trace is fiberwise algebra trace, and the
comparison is evaluation followed by the existing tensor complexification
of genuine rational singular cohomology. Cycle classes are defined before
the comparison, and both pullback and pushforward squares are proved.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitDeRham

open Classical
open scoped BigOperators TensorProduct

noncomputable section

variable (k : Type) [Field k] (I : Type) [Finite I]

/-- Degree-zero affine de Rham cohomology of the original split coordinate ring. -/
abbrev Cohomology := AffineDeRham.H0 k (I → k)

/-- Coordinates come from the vanishing of the actual Kähler differential module. -/
def coordinates : Cohomology k I ≃ₐ[k] (I → k) :=
  AffineDeRham.unramifiedCoordinates k (I → k)

theorem coordinates_apply (a : Cohomology k I) (i : I) : coordinates k I a i = a.val i := rfl

variable {I} {S : Type} [Finite S]

/-- Pullback uses the coordinate-ring map of the same actual split-scheme morphism. -/
def pullback (f : S → I) : Cohomology k I →ₐ[k] Cohomology k S :=
  AffineDeRham.map k (SplitPointGeometry.precompose k f)

@[simp]
theorem coordinates_pullback (f : S → I) (a : Cohomology k I) (s : S) :
    coordinates k S (pullback k f a) s = coordinates k I a (f s) := rfl

/-- The trace sums the values on the actual finite fibers. -/
def pushforward [Fintype S] (f : S → I) : Cohomology k S →ₗ[k] Cohomology k I :=
  (coordinates k I).symm.toLinearMap.comp
    ((finiteFiberSum k f).comp (coordinates k S).toLinearMap)

@[simp]
theorem coordinates_pushforward [Fintype S] (f : S → I)
    (a : Cohomology k S) (i : I) :
    coordinates k I (pushforward k f a) i =
      ∑ s, if f s = i then coordinates k S a s else 0 := rfl

/-- On a split projection this is the ordinary algebra trace on every base component. -/
theorem pushforward_projection_eq_algebraTrace (J : Type) [Fintype J]
    [Fintype I] (a : Cohomology k (I × J)) (i : I) :
    coordinates k I (pushforward k (Prod.fst : I × J → I) a) i =
      Algebra.trace k (J → k) (fun j ↦ coordinates k (I × J) a (i, j)) := by
  rw [coordinates_pushforward, AffineDeRham.algebraTrace_pi]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- Constant fiber cardinality gives the degree identity, including degree zero. -/
theorem pushforward_pullback [Fintype S] (f : S → I) (d : ℕ)
    (hdegree : ∀ i, (Finset.univ.filter fun s ↦ f s = i).card = d)
    (a : Cohomology k I) :
    pushforward k f (pullback k f a) = d • a := by
  apply (coordinates k I).injective
  ext i
  simp only [coordinates_pushforward, coordinates_pullback,
    map_nsmul, Pi.smul_apply]
  have hterm : (fun s ↦ if f s = i then coordinates k I a (f s) else 0) =
      (fun s ↦ if f s = i then coordinates k I a i else 0) := by
    funext s
    split_ifs with h
    · rw [h]
    · rfl
  rw [hterm]
  simp only [Finset.sum_ite, Finset.sum_const, add_zero,
    hdegree i, smul_zero]

variable (I)

/-- A cycle is sent to its actual point coefficients as a closed regular function. -/
def cycleClass : SplitZeroCycles.Chow ℂ I ℚ →ₗ[ℚ] Cohomology ℂ I where
  toFun z := (coordinates ℂ I).symm (fun i ↦ (SplitZeroCycles.chowCoordinates ℂ I ℚ z i : ℂ))
  map_add' z w := by
    apply (coordinates ℂ I).injective
    ext i
    simp
  map_smul' r z := by
    apply (coordinates ℂ I).injective
    ext i
    have hc : coordinates ℂ I (algebraMap ℚ (Cohomology ℂ I) r) i = (r : ℂ) :=
      congrFun (RingHom.map_rat_algebraMap (coordinates ℂ I).toRingHom r) i
    simp [Algebra.smul_def, hc]

@[simp]
theorem coordinates_cycleClass (z : SplitZeroCycles.Chow ℂ I ℚ) (i : I) :
    coordinates ℂ I (cycleClass I z) i = (SplitZeroCycles.chowCoordinates ℂ I ℚ z i : ℂ) :=
  rfl

/-- Evaluation identifies actual algebraic degree-zero classes with the existing
tensor complexification of rational singular cohomology. -/
def bettiComparison : Cohomology ℂ I ≃ₗ[ℂ] SplitHodgeStructure.Complexification I :=
  (coordinates ℂ I).toLinearEquiv.trans (SplitHodgeStructure.complexCoordinates I).symm

@[simp]
theorem complexCoordinates_bettiComparison (a : Cohomology ℂ I) :
    SplitHodgeStructure.complexCoordinates I (bettiComparison I a) = coordinates ℂ I a := by
  simp [bettiComparison]

@[simp]
theorem coordinates_bettiComparison_symm (a : SplitHodgeStructure.Complexification I) :
    coordinates ℂ I ((bettiComparison I).symm a) =
      SplitHodgeStructure.complexCoordinates I a := by
  simp [bettiComparison]

/-- The normalized Chow–de Rham–Betti square, with genuine tensor scalar extension. -/
theorem bettiComparison_cycleClass (z : SplitZeroCycles.Chow ℂ I ℚ) :
    bettiComparison I (cycleClass I z) =
      SplitHodgeStructure.rationalEmbedding I (SplitBetti.cycleClass I z) := by
  apply (SplitHodgeStructure.complexCoordinates I).injective
  ext i
  simp only [complexCoordinates_bettiComparison,
    SplitHodgeStructure.complexCoordinates_rationalEmbedding,
    coordinates_cycleClass, SplitBetti.coordinates_cycleClass]

variable {I}

/-- Cycle class commutes with the original geometric Chow pullback. -/
theorem cycleClass_pullback (f : S → I) (z : SplitZeroCycles.Chow ℂ I ℚ) :
    cycleClass S (SplitZeroCycles.chowPullback ℂ ℚ f z) =
      pullback ℂ f (cycleClass I z) := by
  apply (coordinates ℂ S).injective
  ext s
  simp only [coordinates_cycleClass, coordinates_pullback,
    SplitZeroCycles.chowCoordinates_pullback]

/-- Cycle class commutes with the original geometric Chow pushforward. -/
theorem cycleClass_pushforward [Fintype S] (f : S → I)
    (z : SplitZeroCycles.Chow ℂ S ℚ) :
    cycleClass I (SplitZeroCycles.chowPushforward ℂ ℚ f z) =
      pushforward ℂ f (cycleClass S z) := by
  apply (coordinates ℂ I).injective
  ext i
  simp only [coordinates_cycleClass, SplitZeroCycles.chowCoordinates_pushforward,
    coordinates_pushforward, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

/-- Pullbacks intertwine after extending the original singular map to complex coefficients. -/
theorem bettiComparison_pullback (f : S → I) (a : Cohomology ℂ I) :
    bettiComparison S (pullback ℂ f a) =
      SplitHodgeStructure.complexifyMap (SplitBetti.pullback f).toLinearMap
        (bettiComparison I a) := by
  obtain ⟨z, rfl⟩ := (bettiComparison I).symm.surjective a
  induction z using TensorProduct.inductionOn with
  | tmul c h =>
      apply (SplitHodgeStructure.complexCoordinates S).injective
      ext s
      simp only [complexCoordinates_bettiComparison, coordinates_pullback,
        coordinates_bettiComparison_symm, SplitHodgeStructure.complexCoordinates_tmul,
        SplitHodgeStructure.complexifyMap_tmul, LinearEquiv.apply_symm_apply,
        AlgHom.toLinearMap_apply, SplitBetti.coordinates_pullback]
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

/-- Trace intertwines with the scalar extension of the original singular transfer. -/
theorem bettiComparison_pushforward [Fintype S] (f : S → I) (a : Cohomology ℂ S) :
    bettiComparison I (pushforward ℂ f a) =
      SplitHodgeStructure.complexifyMap (SplitBetti.pushforward f)
        (bettiComparison S a) := by
  obtain ⟨z, rfl⟩ := (bettiComparison S).symm.surjective a
  induction z using TensorProduct.inductionOn with
  | tmul c h =>
      apply (SplitHodgeStructure.complexCoordinates I).injective
      ext i
      simp only [complexCoordinates_bettiComparison, coordinates_pushforward,
        coordinates_bettiComparison_symm, SplitHodgeStructure.complexCoordinates_tmul,
        SplitHodgeStructure.complexifyMap_tmul, LinearEquiv.apply_symm_apply,
        SplitBetti.coordinates_pushforward, Rat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

/-- The independently defined cycle class preserves the actual Chow intersection product. -/
theorem cycleClass_intersection (z w : SplitZeroCycles.Chow ℂ I ℚ) :
    cycleClass I (SplitZeroCycles.chowIntersection ℂ ℚ z w) =
      cycleClass I z * cycleClass I w := by
  apply (coordinates ℂ I).injective
  ext i
  simp only [coordinates_cycleClass, map_mul, Pi.mul_apply,
    SplitZeroCycles.chowCoordinates_intersection, Rat.cast_mul]

/-- A reduced point has its normalized characteristic de Rham class. -/
theorem cycleClass_pointCycle (i j : I) :
    coordinates ℂ I
      (cycleClass I (SplitZeroCycles.classMap ℂ I ℚ (SplitZeroCycles.pointCycle ℂ I ℚ i))) j =
        if i = j then 1 else 0 := by
  simp only [coordinates_cycleClass, SplitZeroCycles.chowCoordinates_pointCycle]
  simp only [Pi.single_apply]
  by_cases h : i = j <;> simp_all [eq_comm]

end

end HodgeConjecture.SplitDeRham
