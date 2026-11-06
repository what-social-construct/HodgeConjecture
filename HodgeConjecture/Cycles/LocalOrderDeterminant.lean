module

public import HodgeConjecture.CommutativeAlgebra.LatticeIndex
public import HodgeConjecture.Cycles.LocalOrder
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section

/-!
# Determinants and relative lattice lengths

The determinant comparison of Stacks Project, Tag 02MI:
https://stacks.math.columbia.edu/tag/02MI

The index is the difference of actual finite quotient lengths. Independence
from the lattice reduces the calculation to the coordinate lattice. We
check diagonal maps by clearing denominators and transvections by conjugation
to their inverses, then use Mathlib's generation theorem for invertible matrices.
The local order is the existing signed, length-based order in this repository.
-/

set_option autoImplicit false
namespace HodgeConjecture.SchemeCycles

noncomputable section

open HodgeConjecture.CommutativeAlgebra

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (n : Type*) [Fintype n] [DecidableEq n]

private def coordinateEmbedding : (n → R) →ₗ[R] (n → K) :=
  LinearMap.pi (fun i => (Algebra.linearMap R K).comp (LinearMap.proj i))

omit [IsDomain R] [Fintype n] [DecidableEq n] in
private theorem coordinateEmbedding_injective : Function.Injective (coordinateEmbedding R K n) := by
  intro x y h
  ext i
  exact IsFractionRing.injective R K (congrFun h i)

private def coordinateLattice : Submodule R (n → K) := (LinearMap.range (coordinateEmbedding R K n))

private instance coordinateLattice_isLattice : Submodule.IsLattice K (coordinateLattice R K n) where
  fg := by
    rw [coordinateLattice, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := n → R)).map _
  span_eq_top := by
    apply top_unique
    rw [← (Pi.basisFun K n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    change algebraMap R K ((Pi.single i 1 : n → R) j) = (Pi.basisFun K n) i j
    by_cases h : i = j
    · subst j; simp
    · simp [Pi.basisFun_apply, Ne.symm h]

private def diagMap (d : n → K) : (n → K) →ₗ[K] (n → K) :=
  LinearMap.pi (fun i => d i • LinearMap.proj i)

private def diagEquiv (d : n → K) (hd : ∀ i, d i ≠ 0) : (n → K) ≃ₗ[K] (n → K) :=
  LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfNeZero K K (d i) (hd i))

private def diagRingMap (c : n → R) : (n → R) →ₗ[R] (n → R) :=
  LinearMap.pi (fun i => c i • LinearMap.proj i)

omit [IsDomain R] [Fintype n] [DecidableEq n] in
private theorem diagRingMap_range (c : n → R) :
    (LinearMap.range (diagRingMap R n c)) = Submodule.pi Set.univ (fun i => (Ideal.span {c i} : Submodule R R)) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_const,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact fun i => ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext (fun i => (hy i).symm)⟩

omit [IsDomain R] [IsFractionRing R K] [Fintype n] [DecidableEq n] in
private theorem coordinateLattice_diag_image (c : n → R) :
    (coordinateLattice R K n).map ((diagMap K n (fun i => algebraMap R K (c i))).restrictScalars R) =
      ((LinearMap.range (diagRingMap R n c))).map (coordinateEmbedding R K n) := by
  have hc : ((diagMap K n (fun i => algebraMap R K (c i))).restrictScalars R).comp
      (coordinateEmbedding R K n) =
      (coordinateEmbedding R K n).comp (diagRingMap R n c) := by
    apply LinearMap.ext
    intro x
    ext i
    exact (map_mul (algebraMap R K) (c i) (x i)).symm
  rw [coordinateLattice, ← LinearMap.range_comp, hc, LinearMap.range_comp]

omit [IsDomain R] in
private theorem coordinateLattice_diag_quotient_length (c : n → R) :
    submoduleQuotientLength (coordinateLattice R K n)
      ((coordinateLattice R K n).map
        ((diagMap K n (fun i => algebraMap R K (c i))).restrictScalars R)) =
      ∑ i, Module.length R (R ⧸ Ideal.span {c i}) := by
  rw [coordinateLattice_diag_image, coordinateLattice,
    submoduleQuotientLength_range _ (coordinateEmbedding_injective R K n), diagRingMap_range]
  rw [(Submodule.quotientPi (fun i => (Ideal.span {c i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype]

omit [IsDomain R] [IsFractionRing R K] [Fintype n] [DecidableEq n] in
private theorem coordinateLattice_diag_le (c : n → R) :
    (coordinateLattice R K n).map
      ((diagMap K n (fun i => algebraMap R K (c i))).restrictScalars R) ≤
        coordinateLattice R K n := by
  rw [coordinateLattice_diag_image, coordinateLattice]
  exact Submodule.map_le_iff_le_comap.mpr (by intro x hx; exact ⟨x, rfl⟩)

private def orderHom [IsNoetherianRing R] [Ring.KrullDimLE 1 R] : Kˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (localOrder R f)
  map_one' := localOrder_one R
  map_mul' := localOrder_mul R

private theorem det_diagEquiv (d : n → K) (hd : ∀ i, d i ≠ 0) :
    LinearEquiv.det (diagEquiv K n d hd) = ∏ i, Units.mk0 (d i) (hd i) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have he : (diagEquiv K n d hd).toLinearMap = Matrix.toLin' (Matrix.diagonal d) := by
    apply LinearMap.ext
    intro x
    ext i
    simp [diagEquiv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [he, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

private theorem index_integral_diag (c : n → R) (hc : ∀ i, c i ≠ 0) :
    latticeIndexHom R K (n → K) (coordinateLattice R K n)
      (diagEquiv K n (fun i => algebraMap R K (c i))
        (fun i => (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (hc i))) =
    orderHom R K (LinearEquiv.det (diagEquiv K n (fun i => algebraMap R K (c i))
        (fun i => (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (hc i)))) := by
  change Multiplicative.ofAdd (latticeIndex _ _) = _
  rw [show ((diagEquiv K n (fun i => algebraMap R K (c i)) _).restrictScalars R).toLinearMap =
    (diagMap K n (fun i => algebraMap R K (c i))).restrictScalars R from rfl,
    latticeIndex_of_le _ _ (coordinateLattice_diag_le R K n c),
    coordinateLattice_diag_quotient_length, det_diagEquiv, map_prod]
  have hlen : (∑ i, Module.length R (R ⧸ Ideal.span {c i})).toNat =
      ∑ i, (Module.length R (R ⧸ Ideal.span {c i})).toNat := by
    have hsum : ∑ i, Module.length R (R ⧸ Ideal.span {c i}) =
        ((∑ i, (Module.length R (R ⧸ Ideal.span {c i})).toNat : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun i _ => (ENat.coe_toNat
        (principalQuotient_length_ne_top R (c i) (hc i))).symm)
    rw [hsum, ENat.toNat_coe]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_ofAdd, hlen, Nat.cast_sum,
    toAdd_prod, orderHom, MonoidHom.coe_mk, OneHom.coe_mk]
  exact Finset.sum_congr rfl (fun i _ => (localOrder_algebraMap (K := K) R (c i) (hc i)).symm)

private theorem index_diag (d : n → K) (hd : ∀ i, d i ≠ 0) :
    latticeIndexHom R K (n → K) (coordinateLattice R K n) (diagEquiv K n d hd) =
      orderHom R K (LinearEquiv.det (diagEquiv K n d hd)) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) d
  choose a ha using hb
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.property
  have hbK : algebraMap R K (b : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  have haK (i : n) : algebraMap R K (a i) ≠ 0 := by
    rw [ha i, Algebra.smul_def]
    exact mul_ne_zero hbK (hd i)
  have ha0 (i : n) : a i ≠ 0 := fun h => haK i (by rw [h, map_zero])
  let eA := diagEquiv K n (fun i => algebraMap R K (a i)) (fun i => haK i)
  let eB := diagEquiv K n (fun _ => algebraMap R K (b : R)) (fun _ => hbK)
  have he : diagEquiv K n d hd * eB = eA := by
    apply LinearEquiv.ext
    intro x
    ext i
    change d i * (algebraMap R K (b : R) * x i) = algebraMap R K (a i) * x i
    rw [ha i, Algebra.smul_def]
    ring
  let H := latticeIndexHom R K (n → K) (coordinateLattice R K n)
  let J := (orderHom R K).comp (LinearEquiv.det : ((n → K) ≃ₗ[K] (n → K)) →* Kˣ)
  have hA : H eA = J eA := index_integral_diag R K n a ha0
  have hB : H eB = J eB := index_integral_diag R K n (fun _ => (b : R)) (fun _ => hb0)
  have h := hA
  rw [← he, map_mul, map_mul, hB] at h
  exact mul_right_cancel h

def matrixEquiv (A : Matrix n n K) (hA : A.det ≠ 0) : (n → K) ≃ₗ[K] (n → K) :=
  (Matrix.toLin' A).equivOfDetNeZero (by rw [LinearMap.det_toLin']; exact hA)

@[simp] theorem matrixEquiv_coe (A : Matrix n n K) (hA : A.det ≠ 0) :
    (matrixEquiv K n A hA).toLinearMap = Matrix.toLin' A := by
  simp [matrixEquiv]

private theorem matrixEquiv_mul (A B : Matrix n n K) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    matrixEquiv K n (A * B) (by simpa using mul_ne_zero hA hB) =
      matrixEquiv K n A hA * matrixEquiv K n B hB := by
  apply LinearEquiv.toLinearMap_injective
  simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem matrixEquiv_one : matrixEquiv K n 1 (by simp) = 1 := by
  apply LinearEquiv.toLinearMap_injective
  simp

private theorem hom_transvection_eq_one
    (H : ((n → K) ≃ₗ[K] (n → K)) →* Multiplicative ℤ)
    (t : Matrix.TransvectionStruct n K) :
    H (matrixEquiv K n t.toMatrix (by simp)) = 1 := by
  let s : n → K := fun i => if i = t.i then -1 else 1
  have hs (i : n) : s i ≠ 0 := by dsimp [s]; split_ifs <;> simp
  have hS : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  let u : Matrix.TransvectionStruct n K := ⟨t.i, t.j, t.hij, -t.c⟩
  have hSS : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]; dsimp [s]; split_ifs <;> simp
    · simp [h]
  have hTT : t.toMatrix * u.toMatrix = 1 := by
    simp [u, Matrix.TransvectionStruct.toMatrix,
      Matrix.transvection_mul_transvection_same _ _ t.hij]
  have hconj : (Matrix.diagonal s * t.toMatrix) * Matrix.diagonal s = u.toMatrix := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : a = b
    · subst b
      have hnot : ¬(t.i = a ∧ t.j = a) := fun h => t.hij (h.1.trans h.2.symm)
      simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply,
        Matrix.one_apply_eq, Matrix.single]
      dsimp [s]
      split_ifs <;> ring
    · have hnot : ¬a = b := hab
      change s a * (Matrix.transvection t.i t.j t.c a b) * s b =
        Matrix.transvection t.i t.j (-t.c) a b
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, if_neg hnot,
        zero_add, Matrix.single]
      by_cases hsingle : t.i = a ∧ t.j = b
      · rcases hsingle with ⟨rfl, rfl⟩
        simp [s, Ne.symm t.hij]
      · simp [hsingle]
  let S := matrixEquiv K n (Matrix.diagonal s) hS
  let T := matrixEquiv K n t.toMatrix (by simp)
  let U := matrixEquiv K n u.toMatrix (by simp)
  have hSS' : S * S = 1 := by
    rw [← matrixEquiv_mul]; simp only [hSS, matrixEquiv_one]
  have hTT' : T * U = 1 := by
    rw [← matrixEquiv_mul]; simp only [hTT, matrixEquiv_one]
  have hconj' : (S * T) * S = U := by
    rw [← matrixEquiv_mul, ← matrixEquiv_mul]; simp only [hconj]; rfl
  have h1 := congrArg (fun e => Multiplicative.toAdd (H e)) hSS'
  have h2 := congrArg (fun e => Multiplicative.toAdd (H e)) hTT'
  have h3 := congrArg (fun e => Multiplicative.toAdd (H e)) hconj'
  simp only [map_mul, map_one] at h1 h2 h3
  change (H S).toAdd + (H S).toAdd = 0 at h1
  change (H T).toAdd + (H U).toAdd = 0 at h2
  change ((H S).toAdd + (H T).toAdd) + (H S).toAdd = (H U).toAdd at h3
  apply Multiplicative.toAdd.injective
  change (H T).toAdd = 0
  omega

private theorem index_matrix (A : Matrix n n K) (hA : A.det ≠ 0) :
    latticeIndexHom R K (n → K) (coordinateLattice R K n) (matrixEquiv K n A hA) =
      orderHom R K (LinearEquiv.det (matrixEquiv K n A hA)) := by
  let H := latticeIndexHom R K (n → K) (coordinateLattice R K n)
  let J := (orderHom R K).comp (LinearEquiv.det : ((n → K) ≃ₗ[K] (n → K)) →* Kˣ)
  suffices ∀ hA : A.det ≠ 0, H (matrixEquiv K n A hA) = J (matrixEquiv K n A hA) from this hA
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => ∀ hA : A.det ≠ 0, H (matrixEquiv K n A hA) = J (matrixEquiv K n A hA)) A hA
  · intro d hd hdet
    have hd0 : ∀ i, d i ≠ 0 := by
      simpa [Matrix.det_diagonal, Finset.prod_ne_zero_iff] using hd
    have he : matrixEquiv K n (Matrix.diagonal d) hdet = diagEquiv K n d hd0 := by
      apply LinearEquiv.toLinearMap_injective
      rw [matrixEquiv_coe]
      apply LinearMap.ext
      intro x
      ext i
      simp [diagEquiv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    rw [he]
    exact index_diag R K n d hd0
  · intro t ht
    have hdet : LinearEquiv.det (matrixEquiv K n t.toMatrix ht) = 1 := by
      apply Units.ext
      simp
    change H _ = orderHom R K _
    rw [hdet, map_one]
    exact hom_transvection_eq_one K n H t
  · intro A B hA hB ihA ihB hAB
    rw [matrixEquiv_mul K n A B hA hB, map_mul, map_mul, ihA, ihB]

private theorem index_coordinate (e : (n → K) ≃ₗ[K] (n → K)) :
    latticeIndex (coordinateLattice R K n)
      ((coordinateLattice R K n).map (e.restrictScalars R).toLinearMap) =
      localOrder R (LinearEquiv.det e) := by
  let A := LinearMap.toMatrix' e.toLinearMap
  have hA : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have he : matrixEquiv K n A hA = e := by
    apply LinearEquiv.toLinearMap_injective
    simp [A]
  have h := index_matrix R K n A hA
  rw [he] at h
  exact h

variable (V : Type*) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [FiniteDimensional K V]

/-- The signed relative length of any lattice and its image is the local order of
its determinant (Stacks, Tag 02MI). No freeness or normality is assumed. -/
theorem latticeIndex_eq_localOrder_det (M : Submodule R V) [Submodule.IsLattice K M]
    (f : V ≃ₗ[K] V) :
    latticeIndex M (M.map (f.restrictScalars R).toLinearMap) =
      localOrder R (LinearEquiv.det f) := by
  let e := (Module.finBasis K V).equivFun
  let N := M.map (e.restrictScalars R).toLinearMap
  let g := (e.symm.trans f).trans e
  letI := lattice_map_isLattice R K V e M
  have hg : N.map (g.restrictScalars R).toLinearMap =
      (M.map (f.restrictScalars R).toLinearMap).map (e.restrictScalars R).toLinearMap := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    apply LinearMap.ext
    intro x
    simp [g]
  calc
    latticeIndex M (M.map (f.restrictScalars R).toLinearMap) =
        latticeIndex N (N.map (g.restrictScalars R).toLinearMap) := by
      rw [hg]; exact (latticeIndex_map (e.restrictScalars R) _ _).symm
    _ = latticeIndex (coordinateLattice R K (Fin (Module.finrank K V)))
        ((coordinateLattice R K (Fin (Module.finrank K V))).map (g.restrictScalars R).toLinearMap) :=
      latticeIndex_independent R K _ g N _
    _ = localOrder R (LinearEquiv.det g) := index_coordinate R K _ g
    _ = localOrder R (LinearEquiv.det f) := by rw [LinearEquiv.det_conj]

/-- For an automorphism preserving a lattice, its determinant order is the actual
cokernel length. The lattice need not be free over the base ring. -/
theorem localOrder_det_eq_quotient_length (M : Submodule R V) [Submodule.IsLattice K M]
    (f : V ≃ₗ[K] V) (h : M.map (f.restrictScalars R).toLinearMap ≤ M) :
    localOrder R (LinearEquiv.det f) =
      ((submoduleQuotientLength M (M.map (f.restrictScalars R).toLinearMap)).toNat : ℤ) := by
  rw [← latticeIndex_eq_localOrder_det R K V M f, latticeIndex_of_le _ _ h]

end

end HodgeConjecture.SchemeCycles
