module

public import HodgeConjecture.CommutativeAlgebra.DeRham.Differential
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

@[expose] public noncomputable section

/-!
# Actual wedge products and the de Rham Leibniz rule

Multiplication in the existing exterior algebra restricts to the exterior
powers of actual Kähler differentials. The constructed de Rham differential
satisfies its full signed Leibniz rule, so products of closed forms are
closed and a product with an exact factor is exact after the indicated
sign/degree transport. No cohomology class or product law is assumed.

Selected proof adaptation from AxiomMath/Stacks at revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`:
`LinearAlgebra/ExteriorPower/Wedge.lean`, `RingTheory/DeRham/WedgeLeibniz.lean`
and the scalar Leibniz proof in `RingTheory/DeRham/PolynomialQuasiIso.lean`,
all under `StacksFrontier/`. Apache-2.0; see `third_party/axiom-stacks/LICENSE`.
Only the actual exterior products and Leibniz proofs are retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open Function

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Reindexing an exterior power -/

/-- The identification `⋀[R]^m M ≃ₗ[R] ⋀[R]^n M` of exterior powers of equal degrees `m = n`, the
identity on the underlying elements of the exterior algebra. -/
def degCongr {m n : ℕ} (h : m = n) : ⋀[R]^m M ≃ₗ[R] ⋀[R]^n M :=
  LinearEquiv.ofEq _ _ (by rw [h])

/-- `exteriorPower.degCongr` is the identity on the underlying elements of the exterior algebra. -/
@[simp]
theorem coe_degCongr {m n : ℕ} (h : m = n) (x : ⋀[R]^m M) :
    ((degCongr h x : ⋀[R]^n M) : ExteriorAlgebra R M) = (x : ExteriorAlgebra R M) := rfl

/-- The unit `1` of the exterior algebra, as the canonical generator of the zeroth exterior power —
the empty wedge. -/
def unitDegZero (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    ⋀[R]^0 M := ιMulti R 0 Fin.elim0

/-- `exteriorPower.unitDegZero R M` is the unit `1` of the exterior algebra. -/
@[simp]
theorem coe_unitDegZero (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    ((unitDegZero R M : ⋀[R]^0 M) : ExteriorAlgebra R M) = 1 := by
  rw [unitDegZero, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]

/-- A vector sits in the first exterior power. -/
theorem ι_mem_degreeOne (x : M) : ExteriorAlgebra.ι R x ∈ ⋀[R]^1 M := by
  simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι R) x

/-- A sign scales an element of an exterior power by the same sign in the exterior algebra. -/
@[simp]
theorem coe_neg_one_pow_smul (n m : ℕ) (x : ⋀[R]^m M) :
    (((-1 : R) ^ n • x : ⋀[R]^m M) : ExteriorAlgebra R M) =
      (-1) ^ n * (x : ExteriorAlgebra R M) := by
  rw [SetLike.val_smul, Algebra.smul_def]
  simp

/-- Left wedge multiplication by an actual vector in degree one. -/
def wedgeLeft (e : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M where
  toFun x := ⟨ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M), by
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_degreeOne e) x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' c x := Subtype.ext (by simp)

@[simp]
theorem coe_wedgeLeft (e : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft e n x : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M) := rfl

@[simp]
theorem wedgeLeft_ιMulti (e : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft e n (ιMulti R n v) = ιMulti R (n + 1) (Fin.cons e v) := by
  apply Subtype.ext
  rw [coe_wedgeLeft, ιMulti_apply_coe, ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

/-! ### The wedge product -/

/-- The wedge product `⋀^p M × ⋀^q M → ⋀^{p+q} M`, as an `R`-bilinear map: the product of the
exterior algebra restricted to its graded pieces. -/
def wedgeMul (p q : ℕ) : ⋀[R]^p M →ₗ[R] ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) M :=
  LinearMap.mk₂ R
    (fun x y ↦ ⟨(x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M),
      SetLike.mul_mem_graded x.2 y.2⟩)
    (fun x₁ x₂ y ↦ Subtype.ext (by simpa using add_mul (x₁ : ExteriorAlgebra R M) x₂ y))
    (fun c x y ↦ Subtype.ext (by simp))
    (fun x y₁ y₂ ↦ Subtype.ext (by simpa using mul_add (x : ExteriorAlgebra R M) y₁ y₂))
    (fun c x y ↦ Subtype.ext (by simp))

/-- The wedge product of `x` and `y` is their product in the exterior algebra. -/
@[simp]
theorem wedgeMul_apply_coe (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    ((wedgeMul p q x y : ⋀[R]^(p + q) M) : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M) := rfl

/-- The wedge of two generators concatenates the two families of vectors. -/
theorem wedgeMul_ιMulti (p q : ℕ) (u : Fin p → M) (v : Fin q → M) :
    wedgeMul p q (ιMulti R p u) (ιMulti R q v) = ιMulti R (p + q) (Fin.append u v) :=
  Subtype.ext (by
    simp only [wedgeMul_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti])

/-- The maps `⋀^n φ` induced by a linear map `φ` are multiplicative for the wedge product. -/
theorem wedgeMul_map {N : Type*} [AddCommGroup N] [Module R N] (p q : ℕ) (φ : M →ₗ[R] N)
    (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    map (p + q) φ (wedgeMul p q x y) = wedgeMul p q (map p φ x) (map q φ y) :=
  Subtype.ext (by simp only [wedgeMul_apply_coe, coe_map, map_mul])

/-- Wedging with a vector `e` on the left, `⋀^n M → ⋀^{n+1} M`, is the wedge product with `e` as an
element of `⋀^1 M`, reindexed from `⋀^{1+n} M` to `⋀^{n+1} M`. -/
theorem wedgeLeft_eq_wedgeMul (e : M) (n : ℕ) (x : ⋀[R]^n M) :
    wedgeLeft e n x =
      degCongr (Nat.add_comm 1 n) (wedgeMul 1 n ⟨ExteriorAlgebra.ι R e, ι_mem_degreeOne e⟩ x) :=
  Subtype.ext (by rw [coe_wedgeLeft, coe_degCongr, wedgeMul_apply_coe])

/-! ### Graded commutativity -/

/-- Elements of degrees `p` and `q` of the exterior algebra commute up to the sign `(-1)^{p q}`. -/
theorem mul_comm_of_mem {p q : ℕ} {a b : ExteriorAlgebra R M}
    (ha : a ∈ ⋀[R]^p M) (hb : b ∈ ⋀[R]^q M) :
    a * b = (-1) ^ (p * q) * (b * a) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha hb
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, Units.smul_def, zsmul_eq_mul,
        Nat.mul_comm q p]
      simp
  | zero_left => simp
  | zero_right => simp
  | add_left a₁ a₂ b _ _ _ h₁ h₂ => rw [add_mul, h₁, h₂, mul_add, mul_add]
  | add_right a b₁ b₂ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂, mul_add]
  | smul_left c a b _ _ h => rw [smul_mul_assoc, h, mul_smul_comm, mul_smul_comm]
  | smul_right c a b _ _ h => rw [mul_smul_comm, h, smul_mul_assoc, mul_smul_comm]

/-- Graded commutativity of the wedge product in the exterior algebra:
`x ∧ y = (-1)^{p q} y ∧ x`. -/
theorem coe_wedgeMul_comm (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    ((wedgeMul p q x y : ⋀[R]^(p + q) M) : ExteriorAlgebra R M) =
      (-1) ^ (p * q) * ((wedgeMul q p y x : ⋀[R]^(q + p) M) : ExteriorAlgebra R M) :=
  mul_comm_of_mem x.2 y.2

/-- Graded commutativity of the wedge product, `ω ∧ η = (-1)^{p q} η ∧ ω`, in the exterior power
`⋀^{p+q} M`. -/
theorem wedgeMul_comm (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    wedgeMul p q x y =
      (-1 : R) ^ (p * q) • degCongr (Nat.add_comm q p) (wedgeMul q p y x) := by
  exact Subtype.ext (by rw [coe_neg_one_pow_smul, coe_degCongr, coe_wedgeMul_comm p q x y])

/-! ### Associativity -/

/-- The wedge product is associative, in the exterior algebra. -/
theorem coe_wedgeMul_assoc (p q r : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) (z : ⋀[R]^r M) :
    ((wedgeMul (p + q) r (wedgeMul p q x y) z : ⋀[R]^(p + q + r) M) : ExteriorAlgebra R M) =
      ((wedgeMul p (q + r) x (wedgeMul q r y z) : ⋀[R]^(p + (q + r)) M) :
        ExteriorAlgebra R M) :=
  mul_assoc (x : ExteriorAlgebra R M) y z

/-- The wedge product is associative, in the exterior power `⋀^{p+q+r} M`. -/
theorem wedgeMul_assoc (p q r : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) (z : ⋀[R]^r M) :
    wedgeMul (p + q) r (wedgeMul p q x y) z =
      degCongr (Nat.add_assoc p q r).symm (wedgeMul p (q + r) x (wedgeMul q r y z)) :=
  Subtype.ext (by rw [coe_degCongr, coe_wedgeMul_assoc])

/-- Every degree-one form has zero square in the actual exterior algebra. -/
theorem wedgeMul_one_self (ω : ⋀[R]^1 M) : wedgeMul 1 1 ω ω = 0 := by
  have hω : ω = ιMulti R 1 (fun _ ↦ oneEquiv R M ω) := by
    apply (oneEquiv R M).injective
    rw [oneEquiv_ιMulti]
  have hcoe (v : M) : (ιMulti R 1 (fun _ ↦ v) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R v := by
    rw [ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    simp
  apply Subtype.ext
  rw [wedgeMul_apply_coe, hω, hcoe]
  exact ExteriorAlgebra.ι_sq_zero _

end exteriorPower

namespace KaehlerDifferential

section Generators

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The wedges `d b₁ ∧ ⋯ ∧ d b_p` of differentials of elements of `B` span `Ω^p_{B/A}` over `B`:
they are the wedges of the `B`-spanning set `Set.range (D A B)` of `Ω[B⁄A]`. -/
private lemma span_range_ιMulti_D_eq_top (p : ℕ) :
    Submodule.span B (Set.range fun c : Fin p → B ↦
      exteriorPower.ιMulti B p fun i ↦ D A B (c i)) = ⊤ := by
  have himg : exteriorPower.ιMulti B p ''
        {a : Fin p → Ω[B⁄A] | Set.range a ⊆ Set.range (D A B)} =
      Set.range fun c : Fin p → B ↦ exteriorPower.ιMulti B p fun i ↦ D A B (c i) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      choose c hc using fun i ↦ ha (Set.mem_range_self i)
      exact ⟨c, congrArg _ (funext hc)⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, Set.range_subset_iff.2 fun i ↦ ⟨c i, rfl⟩, rfl⟩
  rw [← himg, exteriorPower.ιMulti_span_of_span B p (Ω[B⁄A])
    (KaehlerDifferential.span_range_derivation A B)]

open Pointwise in
/-- The elements `b₀ · d b₁ ∧ ⋯ ∧ d b_p` span `Ω^p_{B/A}` already as an `A`-module, not merely as
a `B`-module: they are `B • {d b₁ ∧ ⋯ ∧ d b_p}`, and multiplying a `B`-spanning set by all of `B`
produces an `A`-spanning set. -/
private lemma span_range_smul_ιMulti_D_eq_top (p : ℕ) :
    Submodule.span A (Set.range fun b : Fin (p + 1) → B ↦
      b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) = ⊤ := by
  have hset : (Set.univ : Set B) • (Set.range fun c : Fin p → B ↦
        exteriorPower.ιMulti B p fun i ↦ D A B (c i)) =
      Set.range fun b : Fin (p + 1) → B ↦
        b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, -, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨Fin.cons x c, by simp⟩
    · rintro _ ⟨b, rfl⟩
      exact Set.smul_mem_smul (Set.mem_univ _) ⟨fun i ↦ b i.succ, rfl⟩
  rw [← hset, Submodule.span_smul_of_span_eq_top Submodule.span_univ,
    span_range_ιMulti_D_eq_top, Submodule.restrictScalars_top]


end Generators

section Leibniz

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The Leibniz rule for the de Rham differential: `d (b ξ) = d b ∧ ξ + b dξ`. -/
theorem deRhamDifferential_smul (p : ℕ) (b : B) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential (A := A) p (b • ξ) =
      exteriorPower.wedgeLeft (D A B b) p ξ + b • deRhamDifferential (A := A) p ξ := by
  refine LinearMap.congr_fun (LinearMap.ext_on
    (span_range_smul_ιMulti_D_eq_top (A := A) (B := B) p)
    (f := (deRhamDifferential (A := A) p) ∘ₗ
      (DistribSMul.toLinearMap A (⋀[B]^p (Ω[B⁄A])) b))
    (g := (exteriorPower.wedgeLeft (D A B b) p).restrictScalars A +
      (DistribSMul.toLinearMap A (⋀[B]^(p + 1) (Ω[B⁄A])) b) ∘ₗ deRhamDifferential (A := A) p)
    ?_) ξ
  rintro _ ⟨v, rfl⟩
  have htail : (fun i : Fin p ↦ D A B (Function.update v 0 (b * v 0) i.succ)) =
      fun i : Fin p ↦ D A B (v i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  have hupd : (fun i ↦ D A B (Function.update v 0 (b * v 0) i)) =
      Function.update (fun j ↦ D A B (v j)) 0 (D A B (b * v 0)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have hcons : (Fin.cons (D A B b) (fun i ↦ D A B (v i.succ)) : Fin (p + 1) → Ω[B⁄A]) =
      Function.update (fun j ↦ D A B (v j)) 0 (D A B b) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp
  have hleft : deRhamDifferential (A := A) p
      ((b * v 0) • exteriorPower.ιMulti B p fun i ↦ D A B (v i.succ)) =
      b • exteriorPower.ιMulti B (p + 1) (fun j ↦ D A B (v j)) +
        v 0 • exteriorPower.ιMulti B (p + 1)
          (Function.update (fun j ↦ D A B (v j)) 0 (D A B b)) := by
    have h := deRhamDifferential_smul_ιMulti_D (A := A) p (Function.update v 0 (b * v 0))
    rw [Function.update_self, htail, hupd] at h
    rw [h, Derivation.leibniz, (exteriorPower.ιMulti B (p + 1)).map_update_add,
      (exteriorPower.ιMulti B (p + 1)).map_update_smul,
      (exteriorPower.ιMulti B (p + 1)).map_update_smul,
      Function.update_eq_self 0 (fun j ↦ D A B (v j))]
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.add_apply, LinearMap.coe_restrictScalars,
    DistribSMul.toLinearMap_apply, smul_smul, hleft, map_smul,
    exteriorPower.wedgeLeft_ιMulti, hcons, deRhamDifferential_smul_ιMulti_D]
  abel

/-- The de Rham differential anticommutes with wedging by an exact one-form. -/
theorem deRhamDifferential_wedgeLeft_D (p : ℕ) (b : B) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential (A := A) (p + 1) (exteriorPower.wedgeLeft (D A B b) p ξ) =
      -exteriorPower.wedgeLeft (D A B b) (p + 1) (deRhamDifferential (A := A) p ξ) := by
  have h := deRhamDifferential_comp_self (A := A) p (b • ξ)
  rw [deRhamDifferential_smul, map_add, deRhamDifferential_smul,
    deRhamDifferential_comp_self p ξ, smul_zero, add_zero] at h
  exact (eq_sub_of_add_eq h).trans (zero_sub _)

end Leibniz

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### Transporting the de Rham differential across an equality of degrees -/

/-- The de Rham differential of two forms with the same underlying element of the exterior
algebra, in two degrees that are equal, agree in the exterior algebra.  This is the transport
that keeps the Leibniz induction free of `HEq`. -/
theorem coe_deRhamDifferential_congr {m n : ℕ} (h : m = n)
    {x : ⋀[R]^m (Ω[R⁄A])} {y : ⋀[R]^n (Ω[R⁄A])}
    (hxy : (x : ExteriorAlgebra R (Ω[R⁄A])) = (y : ExteriorAlgebra R (Ω[R⁄A]))) :
    ((deRhamDifferential (A := A) m x : ⋀[R]^(m + 1) (Ω[R⁄A])) :
        ExteriorAlgebra R (Ω[R⁄A])) =
      ((deRhamDifferential (A := A) n y : ⋀[R]^(n + 1) (Ω[R⁄A])) :
        ExteriorAlgebra R (Ω[R⁄A])) := by
  subst h
  rw [Subtype.coe_injective hxy]

/-! ### The full Leibniz rule -/

/-- **The full Leibniz rule for the de Rham differential**,
`d(ω ∧ η) = dω ∧ η + (-1)^{deg ω} ω ∧ dη`, read in the exterior algebra: the three products are
the multiplication of `ExteriorAlgebra R (Ω[R⁄A])`, in which the degree bookkeeping disappears.

The library had this only for `ω` a one-form `d b`
(`KaehlerDifferential.deRhamDifferential_wedgeLeft_D`); the proof here is the induction on the
degree of `ω` described in the implementation notes of this file. -/
theorem coe_deRhamDifferential_wedgeMul (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A]))
    (η : ⋀[R]^q (Ω[R⁄A])) :
    ((deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) :
          ⋀[R]^(p + q + 1) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
      ((deRhamDifferential (A := A) p ω : ⋀[R]^(p + 1) (Ω[R⁄A])) :
          ExteriorAlgebra R (Ω[R⁄A])) * (η : ExteriorAlgebra R (Ω[R⁄A])) +
        (-1) ^ p * ((ω : ExteriorAlgebra R (Ω[R⁄A])) *
          ((deRhamDifferential (A := A) q η : ⋀[R]^(q + 1) (Ω[R⁄A])) :
            ExteriorAlgebra R (Ω[R⁄A]))) := by
  induction p generalizing q with
  | zero =>
      have hω : ω ∈ (⊤ : Submodule A (⋀[R]^0 (Ω[R⁄A]))) := Submodule.mem_top
      rw [← span_range_smul_ιMulti_D_eq_top (A := A) (B := R) 0] at hω
      induction hω using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          dsimp only
          have hone : ((exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ) :
              ⋀[R]^0 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) = 1 := by
            rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
          have hcoe : ((b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ) :
                ⋀[R]^0 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              algebraMap R (ExteriorAlgebra R (Ω[R⁄A])) (b 0) := by
            rw [SetLike.val_smul, hone, Algebra.smul_def, mul_one]
          have hd : ((deRhamDifferential (A := A) 0
                (b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ)) :
              ⋀[R]^1 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              ExteriorAlgebra.ι R (D A R (b 0)) := by
            rw [deRhamDifferential_smul_ιMulti_D 0 b, exteriorPower.ιMulti_apply_coe,
              ExteriorAlgebra.ιMulti_succ_apply]
            simp
          have hleft := coe_deRhamDifferential_congr (A := A) (Nat.zero_add q)
            (x := exteriorPower.wedgeMul 0 q
              (b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ)) η)
            (y := b 0 • η)
            (by rw [exteriorPower.wedgeMul_apply_coe, hcoe, SetLike.val_smul, Algebra.smul_def])
          rw [hleft, deRhamDifferential_smul, Submodule.coe_add, exteriorPower.coe_wedgeLeft,
            SetLike.val_smul, hd, hcoe, pow_zero, one_mul, Algebra.smul_def]
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, map_add, map_add, Submodule.coe_add,
            Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul, mul_add]
          abel
      | smul c x _ hx =>
          have hws : exteriorPower.wedgeMul 0 q (c • x) η =
              c • exteriorPower.wedgeMul 0 q x η := by
            rw [← algebraMap_smul R c x, map_smul, LinearMap.smul_apply,
              algebraMap_smul]
          rw [hws, map_smul, map_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
            Submodule.coe_smul_of_tower, hx, smul_mul_assoc, smul_add, smul_mul_assoc,
            mul_smul_comm]
  | succ p ih =>
      have hω : ω ∈ (⊤ : Submodule A (⋀[R]^(p + 1) (Ω[R⁄A]))) := Submodule.mem_top
      rw [← span_range_smul_ιMulti_D_eq_top (A := A) (B := R) (p + 1)] at hω
      induction hω using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          dsimp only
          -- peel off the leading one-form `d (b 1)`
          set ξ : ⋀[R]^p (Ω[R⁄A]) :=
            b 0 • exteriorPower.ιMulti R p fun i : Fin p ↦ D A R (b i.succ.succ) with hξ
          have hpeel : b 0 • (exteriorPower.ιMulti R (p + 1)
                fun i : Fin (p + 1) ↦ D A R (b i.succ)) =
              exteriorPower.wedgeLeft (D A R (b 1)) p ξ := by
            rw [hξ, map_smul, exteriorPower.wedgeLeft_ιMulti]
            congr 1
            refine (exteriorPower.ιMulti R (p + 1)).congr_arg ?_
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j; rfl
          rw [hpeel]
          have hassoc : ((exteriorPower.wedgeMul (p + 1) q
                  (exteriorPower.wedgeLeft (D A R (b 1)) p ξ) η :
                ⋀[R]^(p + 1 + q) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              ((exteriorPower.wedgeLeft (D A R (b 1)) (p + q)
                  (exteriorPower.wedgeMul p q ξ η) :
                ⋀[R]^(p + q + 1) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) := by
            rw [exteriorPower.wedgeMul_apply_coe, exteriorPower.coe_wedgeLeft,
              exteriorPower.coe_wedgeLeft, exteriorPower.wedgeMul_apply_coe, mul_assoc]
          rw [coe_deRhamDifferential_congr (A := A) (Nat.succ_add p q) hassoc,
            deRhamDifferential_wedgeLeft_D, Submodule.coe_neg, exteriorPower.coe_wedgeLeft,
            ih q ξ η, deRhamDifferential_wedgeLeft_D, Submodule.coe_neg,
            exteriorPower.coe_wedgeLeft, exteriorPower.coe_wedgeLeft, pow_succ]
          have hcen (z : ExteriorAlgebra R (Ω[R⁄A])) :
              ExteriorAlgebra.ι R (D A R (b 1)) * ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ p * z) =
                (-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ p *
                  (ExteriorAlgebra.ι R (D A R (b 1)) * z) := by
            rw [← mul_assoc, ← ((Commute.neg_one_left
              (ExteriorAlgebra.ι R (D A R (b 1)))).pow_left p).eq, mul_assoc]
          simp only [mul_add, mul_assoc, hcen, neg_mul, mul_neg, mul_one]
          abel
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, map_add, map_add, Submodule.coe_add,
            Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul, mul_add]
          abel
      | smul c x _ hx =>
          have hws : exteriorPower.wedgeMul (p + 1) q (c • x) η =
              c • exteriorPower.wedgeMul (p + 1) q x η := by
            rw [← algebraMap_smul R c x, map_smul, LinearMap.smul_apply,
              algebraMap_smul]
          rw [hws, map_smul, map_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
            Submodule.coe_smul_of_tower, hx, smul_mul_assoc, smul_add, smul_mul_assoc,
            mul_smul_comm]

/-- **The full Leibniz rule for the de Rham differential**,
`d(ω ∧ η) = dω ∧ η + (-1)^{deg ω} ω ∧ dη`, with all three terms transported into the single
exterior power `⋀^{p+q+1} (Ω[R⁄A])`.  Only `dω ∧ η` needs a transport: it is built in degree
`(p+1)+q`, which is the degree `(p+q)+1` of the other two but not by definitional unfolding. -/
theorem deRhamDifferential_wedgeMul (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A]))
    (η : ⋀[R]^q (Ω[R⁄A])) :
    deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) =
      exteriorPower.degCongr (Nat.succ_add p q)
          (exteriorPower.wedgeMul (p + 1) q (deRhamDifferential (A := A) p ω) η) +
        (-1 : R) ^ p • exteriorPower.wedgeMul p (q + 1) ω
          (deRhamDifferential (A := A) q η) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, exteriorPower.coe_degCongr, exteriorPower.wedgeMul_apply_coe,
    SetLike.val_smul, exteriorPower.wedgeMul_apply_coe, Algebra.smul_def,
    coe_deRhamDifferential_wedgeMul p q ω η]
  simp

/-- Products of actual closed forms are closed, in every pair of degrees. -/
theorem deRhamDifferential_wedgeMul_eq_zero_of_closed (p q : ℕ)
    (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A]))
    (hω : deRhamDifferential (A := A) p ω = 0)
    (hη : deRhamDifferential (A := A) q η = 0) :
    deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) = 0 := by
  rw [deRhamDifferential_wedgeMul, hω, hη]
  simp

/-- The actual primitive for an exact left factor times a closed right factor,
with its necessary degree transport displayed. -/
theorem deRhamDifferential_wedgeMul_of_right_closed (p q : ℕ)
    (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A]))
    (hη : deRhamDifferential (A := A) q η = 0) :
    deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) =
      exteriorPower.degCongr (Nat.succ_add p q)
        (exteriorPower.wedgeMul (p + 1) q (deRhamDifferential (A := A) p ω) η) := by
  rw [deRhamDifferential_wedgeMul, hη]
  simp

/-- The actual primitive formula for a closed left factor times an exact right factor. -/
theorem deRhamDifferential_wedgeMul_of_left_closed (p q : ℕ)
    (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A]))
    (hω : deRhamDifferential (A := A) p ω = 0) :
    deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) =
      (-1 : R) ^ p • exteriorPower.wedgeMul p (q + 1) ω
        (deRhamDifferential (A := A) q η) := by
  rw [deRhamDifferential_wedgeMul, hω]
  simp

end KaehlerDifferential

end
