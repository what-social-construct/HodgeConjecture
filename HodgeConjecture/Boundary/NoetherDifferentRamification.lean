module

public import HodgeConjecture.Boundary.HeightOneDifferent
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

@[expose] public section

/-!
# The collision Noether different detects the unramified locus

For an essentially finite-type algebra `R → S`, the zero locus of the
Noether different attached to multiplication `S ⊗[R] S → S` is the support
of the module of Kähler differentials.  Equivalently, a prime contains the
collision Noether different exactly when the algebra is not unramified there.

This is the affine algebra statement of Stacks Project, Lemma 49.6.8
(Tag `0BVU`, in Section 49.6, Tag `0BVK`).  The determinant trick is used
below in the form of Mathlib's finite-module Cayley–Hamilton theorem.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra
open scoped TensorProduct

noncomputable section

universe u

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

private abbrev collisionKernel : Ideal (S ⊗[R] S) :=
  KaehlerDifferential.ideal R S

/-- The collision Noether different annihilates relative Kähler differentials. -/
theorem collisionNoetherDifferentIdeal_le_kaehlerDifferential_annihilator :
    collisionNoetherDifferentIdeal R S ≤ Module.annihilator S Ω[S⁄R] := by
  intro d hd
  change d ∈
    (RingHom.ker (collisionMultiplication R S).toRingHom).annihilator.map
      (collisionMultiplication R S).toRingHom at hd
  rw [Ideal.mem_map_iff_of_surjective _
    (collisionMultiplication_surjective R S)] at hd
  obtain ⟨t, ht, rfl⟩ := hd
  rw [Module.mem_annihilator]
  intro ω
  obtain ⟨x, rfl⟩ :=
    (collisionKernel R S).toCotangent_surjective ω
  letI : LinearMap.CompatibleSMul
      (collisionKernel R S) (collisionKernel R S).Cotangent
      S (S ⊗[R] S) := by
    dsimp only [collisionKernel]
    change LinearMap.CompatibleSMul
      { x // x ∈ KaehlerDifferential.ideal R S }
      Ω[S⁄R] S (S ⊗[R] S)
    infer_instance
  rw [← LinearMap.map_smul_of_tower (collisionKernel R S).toCotangent,
    Ideal.toCotangent_eq_zero, pow_two]
  let μ : S ⊗[R] S →+* S :=
    (collisionMultiplication R S).toRingHom
  have hdiff : algebraMap S (S ⊗[R] S) (μ t) - t ∈ collisionKernel R S := by
    change _ ∈ RingHom.ker μ
    rw [RingHom.mem_ker]
    simp [μ, collisionMultiplication, CollisionFoundations.diagonalMultiplication]
  have htann : ∀ y ∈ collisionKernel R S, t * y = 0 := by
    simpa [Submodule.mem_annihilator, mul_comm, collisionKernel, collisionMultiplication, CollisionFoundations.diagonalMultiplication] using ht
  convert Ideal.mul_mem_mul hdiff x.2 using 1
  simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
  rw [sub_mul, htann x x.2, sub_zero]

private theorem map_eval_eq_pow_of_monic_of_coeff_mem_kernel_powers
    (μ : S ⊗[R] S →+* S)
    (p : Polynomial (S ⊗[R] S)) (hp : p.Monic)
    (hcoeff : ∀ k, p.coeff k ∈ RingHom.ker μ ^ (p.natDegree - k))
    (c : S ⊗[R] S) :
    μ (Polynomial.eval c p) = μ c ^ p.natDegree := by
  rw [← Polynomial.eval₂_hom, Polynomial.eval₂_eq_eval_map,
    show p.map μ = Polynomial.X ^ p.natDegree by
    ext k
    rw [Polynomial.coeff_map]
    by_cases hk : k < p.natDegree
    · have hpos : p.natDegree - k ≠ 0 :=
        Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
      have hker : p.coeff k ∈ RingHom.ker μ :=
        (Ideal.pow_le_self hpos) (hcoeff k)
      rw [RingHom.mem_ker.mp hker]
      simp [Polynomial.coeff_X_pow, ne_of_lt hk]
    · have hle : p.natDegree ≤ k := Nat.le_of_not_gt hk
      rcases hle.eq_or_lt with rfl | hlt
      · simp [hp.coeff_natDegree]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
        simp [Polynomial.coeff_X_pow, ne_of_gt hlt]]
  simp

/--
The annihilator of relative Kähler differentials lies in the radical of the
collision Noether different.
-/
theorem kaehlerDifferential_annihilator_le_collisionNoetherDifferentIdeal_radical
    [EssFiniteType R S] :
    Module.annihilator S Ω[S⁄R] ≤
      (collisionNoetherDifferentIdeal R S).radical := by
  intro d hd
  let C := S ⊗[R] S
  let I : Ideal C := collisionKernel R S
  let μ : C →+* S := (collisionMultiplication R S).toRingHom
  let c : C := algebraMap S C d
  letI : Module.Finite C I := Module.Finite.iff_fg.mpr <| by
    simpa [C, I, collisionKernel, Submodule.FG, Ideal.FG, Ideal.submodule_span_eq] using KaehlerDifferential.ideal_fg R S
  let f : Module.End C I := algebraMap C (Module.End C I) c
  have hrange : LinearMap.range f ≤ I • (⊤ : Submodule C I) := by
    rintro y ⟨x, rfl⟩
    rw [Submodule.mem_smul_top_iff]
    change c * (x : C) ∈ I * I
    have hzero : d • I.toCotangent x = 0 :=
      Module.mem_annihilator.mp hd _
    letI : LinearMap.CompatibleSMul I I.Cotangent S C := by
      dsimp only [I, C, collisionKernel]
      change LinearMap.CompatibleSMul
        { x // x ∈ KaehlerDifferential.ideal R S }
        Ω[S⁄R] S (S ⊗[R] S)
      infer_instance
    rw [← LinearMap.map_smul_of_tower I.toCotangent,
      Ideal.toCotangent_eq_zero, pow_two] at hzero
    simpa [C, I, c, collisionKernel, Submodule.coe_smul_of_tower,
      Algebra.smul_def] using hzero
  obtain ⟨p, hpmonic, _, hpcoeff, hpaeval⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
      C f I hrange
  let e : C := Polynomial.eval c p
  have heann : e ∈ I.annihilator := by
    rw [Submodule.mem_annihilator]
    intro x hx
    have happ : ((Polynomial.aeval f) p) ⟨x, hx⟩ = 0 := by
      rw [hpaeval]
      rfl
    simpa [e, f, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      Module.algebraMap_end_apply, smul_eq_mul] using happ
  have hemap : μ e = d ^ p.natDegree := by
    calc
      μ e = μ c ^ p.natDegree :=
        map_eval_eq_pow_of_monic_of_coeff_mem_kernel_powers
          R S μ p hpmonic hpcoeff c
      _ = d ^ p.natDegree := by
        simp [μ, c, C, collisionMultiplication,
          CollisionFoundations.diagonalMultiplication]
  refine Ideal.mem_radical_iff.mpr ⟨p.natDegree, ?_⟩
  rw [← hemap]
  exact Ideal.mem_map_of_mem μ heann

/--
The collision Noether different and the annihilator of relative Kähler
differentials have the same zero locus.
-/
theorem collisionNoetherDifferentIdeal_le_prime_iff_kaehlerDifferential_annihilator_le
    [EssFiniteType R S] (P : Ideal S) [P.IsPrime] :
    collisionNoetherDifferentIdeal R S ≤ P ↔
      Module.annihilator S Ω[S⁄R] ≤ P := by
  constructor
  · intro hD
    exact
      (kaehlerDifferential_annihilator_le_collisionNoetherDifferentIdeal_radical
        R S).trans ((inferInstance : P.IsPrime).radical_le_iff.mpr hD)
  · exact fun hΩ ↦
      (collisionNoetherDifferentIdeal_le_kaehlerDifferential_annihilator R S).trans hΩ

/--
Stacks Project, Lemma 49.6.8 (Tag `0BVU`; section Tag `0BVK`), for the
collision presentation.
-/
theorem collisionDifferentDetectsRamificationAt_of_essFiniteType
    [EssFiniteType R S] (P : Ideal S) [P.IsPrime] :
    CollisionDifferentDetectsRamificationAt R S P := by
  unfold CollisionDifferentDetectsRamificationAt
  rw [collisionNoetherDifferentIdeal_le_prime_iff_kaehlerDifferential_annihilator_le
      R S P]
  change Module.annihilator S Ω[S⁄R] ≤ P ↔
    ¬ (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S
  rw [Algebra.unramifiedLocus_eq_compl_support]
  simp only [Set.mem_compl_iff, not_not]
  exact (Module.mem_support_iff_of_finite
    (R := S) (M := Ω[S⁄R]) (p := ⟨P, inferInstance⟩)).symm

end

end HodgeConjecture
