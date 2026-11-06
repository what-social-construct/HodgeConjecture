module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# The affine algebraic de Rham differential

Proof adaptation from AxiomMath/Stacks, revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/RingTheory/DeRham/Basic.lean` (construction and square-zero
proof only), Apache-2.0. See `third_party/axiom-stacks/LICENSE`.

For every commutative algebra, construct the actual differential on exterior
powers of its Kähler differentials. Its defining rule determines it uniquely,
and consecutive differentials compose to zero. Quotient descent and general
base-change infrastructure are outside this adaptation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace KaehlerDifferential

section Span

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


end Span

end KaehlerDifferential

open ExteriorAlgebra KaehlerDifferential

/-! ### Wedges in the exterior algebra -/

section ExteriorAlgebraAux

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private lemma ι_mul_ι_swap (x y : M) : ι R x * ι R y = -(ι R y * ι R x) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- A vector, viewed in the exterior algebra, lies in the exterior power of degree one. -/
private lemma ι_mem_exteriorPower_one (x : M) : ι R x ∈ ⋀[R]^1 M := by
  simpa only [pow_one] using LinearMap.mem_range_self (ι R) x

/-- An element of degree two commutes with every vector: `⋀[R]^2 M` is spanned by the products
`ι u * ι v`, and moving `ι x` across such a product changes its sign twice. -/
private lemma mul_ι_comm_of_mem_exteriorPower_two {z : ExteriorAlgebra R M} (hz : z ∈ ⋀[R]^2 M)
    (x : M) : z * ι R x = ι R x * z := by
  have hz : z ∈ LinearMap.range (ι R) * LinearMap.range (ι R) := by rw [← pow_two]; exact hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [mul_assoc, ι_mul_ι_swap v x, mul_neg, ← mul_assoc, ι_mul_ι_swap u x, neg_mul, neg_neg,
      mul_assoc]
  · intro y w hy hw
    rw [add_mul, mul_add, hy, hw]

/-- A wedge of length one is the vector itself, read in the exterior algebra. -/
private lemma coe_ιMulti_one (x : M) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R M) = ι R x := by
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp

/-- A wedge of length one is additive in its entry, read in the exterior algebra. -/
private lemma coe_ιMulti_one_add (x y : M) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ x + y) : ExteriorAlgebra R M)
      = (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R M)
        + (exteriorPower.ιMulti R 1 (fun _ ↦ y) : ExteriorAlgebra R M) := by
  rw [coe_ιMulti_one, coe_ιMulti_one, coe_ιMulti_one, map_add]

/-- A wedge of length one is homogeneous in its entry, read in the exterior algebra. -/
private lemma coe_ιMulti_one_smul (c : R) (x : M) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ c • x) : ExteriorAlgebra R M)
      = c • (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R M) := by
  rw [coe_ιMulti_one, coe_ιMulti_one, map_smul]

/-- Prefixing a vector to a wedge multiplies by it, read in the exterior algebra. -/
private lemma coe_ιMulti_cons (n : ℕ) (x : M) (v : Fin n → M) :
    (exteriorPower.ιMulti R (n + 1) (Fin.cons x v) : ExteriorAlgebra R M)
      = ι R x * (exteriorPower.ιMulti R n v : ExteriorAlgebra R M) := by
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

/-- Prefixing a vector, as the `R`-bilinear map sending `(x, y) : M × ⋀[R]^q M` to the wedge
`x ∧ y : ⋀[R]^(q + 1) M`. -/
private noncomputable def wedgeι (q : ℕ) : M →ₗ[R] ⋀[R]^q M →ₗ[R] ⋀[R]^(q + 1) M :=
  LinearMap.mk₂ R (fun x y ↦ ⟨ι R x * (y : ExteriorAlgebra R M), by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_exteriorPower_one x) y.2⟩)
    (fun x₁ x₂ y ↦ Subtype.ext (by push_cast; rw [map_add, add_mul]))
    (fun c x y ↦ Subtype.ext (by push_cast; rw [map_smul, smul_mul_assoc]))
    (fun x y₁ y₂ ↦ Subtype.ext (by push_cast; rw [mul_add]))
    (fun c x y ↦ Subtype.ext (by push_cast; rw [mul_smul_comm]))

/-- `wedgeι` is multiplication by `ι R x`, read in the exterior algebra. -/
private lemma coe_wedgeι (q : ℕ) (x : M) (y : ⋀[R]^q M) :
    (wedgeι q x y : ExteriorAlgebra R M) = ι R x * (y : ExteriorAlgebra R M) := rfl

end ExteriorAlgebraAux

/-! ### The differentials of the de Rham complex -/

namespace DeRhamDifferential

section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The exterior algebra of `Ω[B⁄A]` over `B`: the de Rham complex of `B` over `A` lives in it. -/
private abbrev Ext (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Type _ :=
  ExteriorAlgebra B (Ω[B⁄A])

private lemma ι_mul_ιMulti_eq_zero (n : ℕ) (v : Fin n → Ω[B⁄A]) (i : Fin n) :
    ι B (v i) * ιMulti B n v = 0 := by
  rw [ExteriorAlgebra.ιMulti_apply]
  exact ExteriorAlgebra.ι_mul_prod_list v i

/-- The de Rham differential of a wedge of `n` differentials, as an `A`-multilinear map: the
antisymmetrisation of `d₁` over the `n` slots, written without signs. -/
private noncomputable def G (d1 : Ω[B⁄A] →ₗ[A] Ext A B) :
    ∀ n : ℕ, MultilinearMap A (fun _ : Fin n => Ω[B⁄A]) (Ext A B)
  | 0 => 0
  | (n + 1) =>
    LinearMap.uncurryLeft
      { toFun := fun ω => (LinearMap.mulLeft A (d1 ω)).compMultilinearMap
            (MultilinearMap.restrictScalars A (ExteriorAlgebra.ιMulti B n).toMultilinearMap) -
          (LinearMap.mulLeft A (ι B ω)).compMultilinearMap (G d1 n)
        map_add' := by
          intro ω ω'
          ext v
          simp only [map_add, sub_apply, LinearMap.compMultilinearMap_apply,
            LinearMap.mulLeft_apply, add_apply, add_mul]
          abel
        map_smul' := by
          intro a ω
          ext v
          simp only [map_smul, LinearMap.map_smul_of_tower, sub_apply,
            LinearMap.compMultilinearMap_apply, LinearMap.mulLeft_apply,
            smul_apply, RingHom.id_apply, smul_mul_assoc, smul_sub] }

private lemma G_zero (d1 : Ω[B⁄A] →ₗ[A] Ext A B) (v : Fin 0 → Ω[B⁄A]) : G d1 0 v = 0 := rfl

private lemma G_succ (d1 : Ω[B⁄A] →ₗ[A] Ext A B) (n : ℕ) (v : Fin (n + 1) → Ω[B⁄A]) :
    G d1 (n + 1) v =
      d1 (v 0) * ιMulti B n (Fin.tail v) - ι B (v 0) * G d1 n (Fin.tail v) := rfl

section Fixed

variable (d1 : Ω[B⁄A] →ₗ[A] Ext A B)
  (hsmul : ∀ (c : B) (ω : Ω[B⁄A]), d1 (c • ω) = c • d1 ω + ι B (D A B c) * ι B ω)
  (hD : ∀ b : B, d1 (D A B b) = 0)

include hsmul hD

/-- The differential in degree one lands in degree two: this holds on the generators `d b`, where
the value is `0`, and the Leibniz rule adds the degree-two term `d c ∧ d b'`. -/
private lemma d1_mem (ω : Ω[B⁄A]) : d1 ω ∈ ⋀[B]^2 (Ω[B⁄A]) := by
  have hmem : ω ∈ Submodule.span B (Set.range (D A B)) := by
    rw [KaehlerDifferential.span_range_derivation A B]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; rw [hD]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [hsmul]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
      exact SetLike.mul_mem_graded (ι_mem_exteriorPower_one _) (ι_mem_exteriorPower_one _)

/-- The values of the degree-one differential are central against vectors, having even degree. -/
private lemma d1_mul_ι_comm (ω x : Ω[B⁄A]) : d1 ω * ι B x = ι B x * d1 ω :=
  mul_ι_comm_of_mem_exteriorPower_two (d1_mem d1 hsmul hD ω) x

omit hsmul in
private lemma G_exact (n : ℕ) (b : Fin n → B) : G d1 n (fun i => D A B (b i)) = 0 := by
  induction n with
  | zero => exact G_zero d1 _
  | succ n ih =>
      have ht : Fin.tail (fun i : Fin (n + 1) => D A B (b i)) = fun i => D A B (b i.succ) := rfl
      rw [G_succ, hD, ht, ih fun i => b i.succ, zero_mul, mul_zero, sub_zero]

private lemma d1_mul_ιMulti (n : ℕ) (v : Fin n → Ω[B⁄A]) (k : Fin n) :
    d1 (v k) * ιMulti B n v = ι B (v k) * G d1 n v := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
      have hv : ιMulti B (n + 1) v = ι B (v 0) * ιMulti B n (Fin.tail v) := ιMulti_succ_apply v
      induction k using Fin.cases with
      | zero =>
          rw [hv, G_succ, mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc,
            d1_mul_ι_comm d1 hsmul hD, ExteriorAlgebra.ι_sq_zero, zero_mul, sub_zero]
      | succ j =>
          have hIH := ih (Fin.tail v) j
          have hzero : ι B (Fin.tail v j) * ιMulti B n (Fin.tail v) = 0 :=
            ι_mul_ιMulti_eq_zero n (Fin.tail v) j
          have hvj : v j.succ = Fin.tail v j := rfl
          rw [hvj, hv, G_succ, mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc,
            ← d1_mul_ι_comm d1 hsmul hD, mul_assoc (d1 (v 0)), hzero, mul_zero,
            ι_mul_ι_swap (Fin.tail v j) (v 0), neg_mul, sub_neg_eq_add, zero_add,
            d1_mul_ι_comm d1 hsmul hD, mul_assoc, mul_assoc, hIH]

private lemma G_eq_zero_of_eq (n : ℕ) (v : Fin n → Ω[B⁄A]) (i j : Fin n) (hij : i ≠ j)
    (hv : v i = v j) : G d1 n v = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j =>
              have hvj : v 0 = Fin.tail v j := hv
              rw [G_succ, hvj, d1_mul_ιMulti d1 hsmul hD n (Fin.tail v) j, ← hvj, sub_self]
      | succ i =>
          induction j using Fin.cases with
          | zero =>
              have hvj : v 0 = Fin.tail v i := hv.symm
              rw [G_succ, hvj, d1_mul_ιMulti d1 hsmul hD n (Fin.tail v) i, ← hvj, sub_self]
          | succ j =>
              have hij' : i ≠ j := fun h => hij (by rw [h])
              have hv' : Fin.tail v i = Fin.tail v j := hv
              rw [G_succ, ih (Fin.tail v) i j hij' hv',
                (ExteriorAlgebra.ιMulti B n).map_eq_zero_of_eq _ hv' hij']
              simp

omit hD in
private lemma G_update_smul (n : ℕ) [inst : DecidableEq (Fin n)] (c : B) (v : Fin n → Ω[B⁄A])
    (k : Fin n) :
    G d1 n (Function.update v k (c • v k)) =
      c • G d1 n v + ι B (D A B c) * ιMulti B n v := by
  obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
      have hv : ιMulti B (n + 1) v = ι B (v 0) * ιMulti B n (Fin.tail v) := ιMulti_succ_apply v
      induction k using Fin.cases with
      | zero =>
          have h0 : Function.update v 0 (c • v 0) 0 = c • v 0 := Function.update_self ..
          have ht : Fin.tail (Function.update v 0 (c • v 0)) = Fin.tail v :=
            Fin.tail_update_zero v _
          rw [G_succ, h0, ht, G_succ, hsmul, hv, map_smul, add_mul, smul_mul_assoc,
            smul_mul_assoc, smul_sub, mul_assoc]
          abel
      | succ k =>
          have h0 : Function.update v k.succ (c • v k.succ) 0 = v 0 :=
            Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
          have ht : Fin.tail (Function.update v k.succ (c • v k.succ)) =
              Function.update (Fin.tail v) k (c • Fin.tail v k) := Fin.tail_update_succ v k _
          rw [G_succ, h0, ht, ih (Fin.tail v) k, G_succ, hv,
            (ExteriorAlgebra.ιMulti B n).map_update_smul, Function.update_eq_self, mul_add,
            mul_smul_comm, mul_smul_comm, smul_sub, ← mul_assoc, ← mul_assoc,
            ι_mul_ι_swap (v 0) (D A B c), neg_mul]
          abel

private lemma G_mem (n : ℕ) (v : Fin n → Ω[B⁄A]) : G d1 n v ∈ ⋀[B]^(n + 1) (Ω[B⁄A]) := by
  induction n with
  | zero => rw [G_zero]; exact Submodule.zero_mem _
  | succ n ih =>
      rw [G_succ]
      refine Submodule.sub_mem _ ?_ ?_
      · have hd : (n + 1 + 1) = 2 + n := by omega
        rw [hd]
        exact SetLike.mul_mem_graded (d1_mem d1 hsmul hD _)
          (by simpa using (exteriorPower.ιMulti B n (Fin.tail v)).2)
      · have hd : (n + 1 + 1) = 1 + (n + 1) := by omega
        rw [hd]
        exact SetLike.mul_mem_graded (ι_mem_exteriorPower_one _)
          (ih (Fin.tail v))

end Fixed
/-- The ring map `b ↦ b + ε · d b` from `B` into the square-zero extension `E[ε] = E ⊕ E · ε` of
`E = ⋀_B Ω[B⁄A]`.  It is multiplicative precisely because `d` is a derivation: the coefficient of
`ε` in `jetHom b * jetHom c` is `b · d c + c · d b`, and that is the Leibniz rule. -/
private noncomputable def jetHom (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] TrivSqZeroExt (Ext A B) (Ext A B) where
  toFun b := TrivSqZeroExt.inl (algebraMap B (Ext A B) b) + TrivSqZeroExt.inr (ι B (D A B b))
  map_one' := by simp
  map_mul' b c := TrivSqZeroExt.ext (by simp) (by
    have h : ι B (D A B b) * algebraMap B (Ext A B) c =
        algebraMap B (Ext A B) c * ι B (D A B b) := (Algebra.commutes _ _).symm
    simp [TrivSqZeroExt.snd_mul, Derivation.leibniz, Algebra.smul_def, h])
  map_zero' := by simp
  map_add' b c := TrivSqZeroExt.ext (by simp) (by simp)
  commutes' a := by simp [Algebra.algebraMap_eq_smul_one]

/-- `Jet A B` is the module of first-order jets of the exterior algebra `E = ⋀_B Ω[B⁄A]`: the
square-zero extension `E[ε]` with `B` acting through `jetHom`, so that its underlying `A`-module
is `E × E` while `b • (x, y) = (b x, b y + d b ∧ x)`.  A `B`-multilinear map into `Jet A B` is
therefore the same thing as a pair consisting of an ordinary `B`-multilinear map and a map obeying
the Leibniz rule of the de Rham differential; this is how both differentials constructed below
descend from multilinear algebra over `B`.  It is a synonym for `TrivSqZeroExt` rather than that
type itself because the `B`-action wanted here is the twisted one, not the one coming from the
`B`-algebra structure of `E`. -/
private def Jet (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Type _ :=
  TrivSqZeroExt (Ext A B) (Ext A B)

namespace Jet

/-- The jet with value `x` and derivative `y`. -/
private def mk (x y : Ext A B) : Jet A B := (x, y)

/-- The value of a jet. -/
private def val : Jet A B → Ext A B := TrivSqZeroExt.fst

/-- The derivative of a jet. -/
private def der : Jet A B → Ext A B := TrivSqZeroExt.snd

private lemma ext {z w : Jet A B} (hv : val z = val w) (hd : der z = der w) : z = w :=
  TrivSqZeroExt.ext hv hd

@[instance_reducible] private noncomputable def addCommGroup : AddCommGroup (Jet A B) :=
  inferInstanceAs (AddCommGroup (TrivSqZeroExt (Ext A B) (Ext A B)))

attribute [local instance] Jet.addCommGroup

@[instance_reducible] private noncomputable def moduleA : Module A (Jet A B) :=
  inferInstanceAs (Module A (TrivSqZeroExt (Ext A B) (Ext A B)))

attribute [local instance] Jet.moduleA

@[instance_reducible] private noncomputable def moduleB : Module B (Jet A B) :=
  Module.compHom (TrivSqZeroExt (Ext A B) (Ext A B)) (jetHom A B).toRingHom

attribute [local instance] Jet.moduleB

private lemma fst_jetHom_mul (b : B) (w : TrivSqZeroExt (Ext A B) (Ext A B)) :
    (jetHom A B b * w).fst = b • w.fst := by
  simp [jetHom, Algebra.smul_def]

private lemma snd_jetHom_mul (b : B) (w : TrivSqZeroExt (Ext A B) (Ext A B)) :
    (jetHom A B b * w).snd = b • w.snd + ι B (D A B b) * w.fst := by
  simp [jetHom, TrivSqZeroExt.snd_mul, Algebra.smul_def]

private lemma val_mk (x y : Ext A B) : val (mk x y) = x := rfl

private lemma der_mk (x y : Ext A B) : der (mk x y) = y := rfl

private lemma val_add (z w : Jet A B) : val (z + w) = val z + val w := rfl

private lemma der_add (z w : Jet A B) : der (z + w) = der z + der w := rfl

/-- The value of a jet is `B`-linear: the twisted action does not disturb the first component. -/
private lemma val_smul (b : B) (z : Jet A B) : val (b • z) = b • val z :=
  fst_jetHom_mul b z

/-- The Leibniz rule, which is what the twisted `B`-action on the jets says. -/
private lemma der_smul (b : B) (z : Jet A B) :
    der (b • z) = b • der z + ι B (D A B b) * val z :=
  snd_jetHom_mul b z

private theorem isScalarTower : IsScalarTower A B (Jet A B) :=
  ⟨fun a b z => by
    have h : ∀ w : TrivSqZeroExt (Ext A B) (Ext A B),
        jetHom A B (a • b) * w = a • (jetHom A B b * w) := fun w => by
      rw [map_smul]
      apply TrivSqZeroExt.ext <;>
        simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
          TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul,
          MulOpposite.smul_eq_mul_unop, smul_add, smul_mul_assoc]
    exact h z⟩

attribute [local instance] Jet.isScalarTower

/-- The value of a jet, as a `B`-linear map. -/
private noncomputable def valMap : Jet A B →ₗ[B] Ext A B where
  toFun := val
  map_add' := val_add
  map_smul' := val_smul

/-- The derivative of a jet, as an `A`-linear map. -/
private noncomputable def derMap : Jet A B →ₗ[A] Ext A B where
  toFun := der
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Jet

attribute [local instance] Jet.addCommGroup Jet.moduleA Jet.moduleB Jet.isScalarTower

open Jet

/-- The `A`-derivation `b ↦ (d b, 0)` of `B` with values in the jets of `⋀_B Ω[B⁄A]`.  The
universal property of `Ω[B⁄A]` applied to it is what produces the differential in degree one. -/
private noncomputable def jetD : Derivation A B (Jet A B) where
  toFun b := mk (ι B (D A B b)) 0
  map_add' b c := ext (by
      change ι B (D A B (b + c)) = ι B (D A B b) + ι B (D A B c)
      rw [map_add, map_add]) (by
      change (0 : Ext A B) = 0 + 0
      rw [add_zero])
  map_smul' a b := ext (by
      change ι B (D A B (a • b)) = a • ι B (D A B b)
      rw [Derivation.map_smul, LinearMap.map_smul_of_tower]) (by
      change (0 : Ext A B) = a • (0 : Ext A B)
      rw [smul_zero])
  map_one_eq_zero' := ext (by
      change ι B (D A B (1 : B)) = (0 : Ext A B)
      rw [Derivation.map_one_eq_zero, map_zero]) rfl
  leibniz' b c := by
    change mk (ι B (D A B (b * c))) 0 =
      b • (mk (ι B (D A B c)) 0 : Jet A B) + c • (mk (ι B (D A B b)) 0 : Jet A B)
    refine ext ?_ ?_
    · simp only [val_add, val_smul, val_mk, Derivation.leibniz, map_add,
        LinearMap.map_smul_of_tower]
    · simp only [der_add, der_smul, der_mk, val_mk, smul_zero, zero_add]
      exact (ExteriorAlgebra.ι_add_mul_swap _ _).symm

/-- The universal property of `Ω[B⁄A]` applied to `jetD`. -/
private noncomputable def jetLift : Ω[B⁄A] →ₗ[B] Jet A B :=
  Derivation.liftKaehlerDifferential jetD

/-- The de Rham differential in degree one, valued in the exterior algebra:
`d1 (b · d b') = d b ∧ d b'`. -/
private noncomputable def d1 : Ω[B⁄A] →ₗ[A] Ext A B :=
  derMap ∘ₗ jetLift.restrictScalars A

private lemma jetLift_apply_D (b : B) : jetLift (D A B b) = (mk (ι B (D A B b)) 0 : Jet A B) :=
  Derivation.liftKaehlerDifferential_comp_D jetD b

private lemma d1_apply_D (b : B) : d1 (D A B b) = (0 : Ext A B) := by
  show der (jetLift (D A B b)) = 0
  rw [jetLift_apply_D]
  rfl

private lemma val_liftKaehlerDifferential (ω : Ω[B⁄A]) :
    val (jetLift ω) = ι B ω := by
  have h : valMap ∘ₗ jetLift =
      (ι B : Ω[B⁄A] →ₗ[B] Ext A B) := by
    refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B) ?_
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    show val (jetLift (D A B b)) = ι B (D A B b)
    rw [jetLift_apply_D]
    rfl
  exact LinearMap.congr_fun h ω

private lemma d1_apply_smul (c : B) (ω : Ω[B⁄A]) :
    d1 (c • ω) = c • d1 ω + ι B (D A B c) * ι B ω := by
  show der (jetLift (c • ω)) =
    c • der (jetLift ω) + ι B (D A B c) * ι B ω
  rw [map_smul, der_smul, val_liftKaehlerDifferential]

/-- The alternating map `v ↦ (v 0 ∧ ⋯ ∧ v_{p-1}, G v)` with values in the jets.  It is
`B`-multilinear for the twisted action of `B` precisely because `G` obeys `G_update_smul`. -/
private noncomputable def jetAlternating (p : ℕ) : Ω[B⁄A] [⋀^Fin p]→ₗ[B] Jet A B where
  toFun v := mk (ιMulti B p v) (G d1 p v)
  map_update_add' v i x y := ext (by
      change ιMulti B p (Function.update v i (x + y)) =
        ιMulti B p (Function.update v i x) + ιMulti B p (Function.update v i y)
      exact (ExteriorAlgebra.ιMulti B p).map_update_add v i x y) (by
      change G d1 p (Function.update v i (x + y)) =
        G d1 p (Function.update v i x) + G d1 p (Function.update v i y)
      exact (G d1 p).map_update_add v i x y)
  map_update_smul' v i c x := ext (by
      simp only [val_mk, val_smul]
      exact (ExteriorAlgebra.ιMulti B p).map_update_smul v i c x) (by
      have h : Function.update v i (c • x) =
          Function.update (Function.update v i x) i (c • Function.update v i x i) := by
        rw [Function.update_self, Function.update_idem]
      simp only [der_mk, der_smul, val_mk]
      rw [h]
      exact G_update_smul d1 d1_apply_smul p c (Function.update v i x) i)
  map_eq_zero_of_eq' v i j hv hij := ext (by
      change ιMulti B p v = (0 : Ext A B)
      exact (ExteriorAlgebra.ιMulti B p).map_eq_zero_of_eq v hv hij) (by
      change G d1 p v = (0 : Ext A B)
      exact G_eq_zero_of_eq d1 d1_apply_smul d1_apply_D p v i j hij hv)

/-- The de Rham differential in degree `p`, valued in the exterior algebra. -/
private noncomputable def dp (p : ℕ) : ⋀[B]^p (Ω[B⁄A]) →ₗ[A] Ext A B :=
  derMap ∘ₗ (exteriorPower.alternatingMapLinearEquiv (jetAlternating p)).restrictScalars A

private lemma dp_apply_ιMulti (p : ℕ) (v : Fin p → Ω[B⁄A]) :
    dp p (exteriorPower.ιMulti B p v) = G d1 p v := by
  show der (exteriorPower.alternatingMapLinearEquiv (jetAlternating p)
    (exteriorPower.ιMulti B p v)) = G d1 p v
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private lemma val_alternatingMapLinearEquiv (p : ℕ) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    val (exteriorPower.alternatingMapLinearEquiv (jetAlternating p) ξ) = (ξ : Ext A B) := by
  have h : valMap ∘ₗ (exteriorPower.alternatingMapLinearEquiv (jetAlternating p)) =
      (⋀[B]^p (Ω[B⁄A])).subtype := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span B p (Ω[B⁄A])) ?_
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    show val (exteriorPower.alternatingMapLinearEquiv (jetAlternating p)
      (exteriorPower.ιMulti B p v)) = ((exteriorPower.ιMulti B p v : ⋀[B]^p (Ω[B⁄A])) : Ext A B)
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun h ξ

private lemma dp_apply_smul (p : ℕ) (c : B) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    dp p (c • ξ) = c • dp p ξ + ι B (D A B c) * (ξ : Ext A B) := by
  show der (exteriorPower.alternatingMapLinearEquiv (jetAlternating p) (c • ξ)) =
    c • der (exteriorPower.alternatingMapLinearEquiv (jetAlternating p) ξ) +
      ι B (D A B c) * (ξ : Ext A B)
  rw [map_smul, der_smul, val_alternatingMapLinearEquiv]

private lemma dp_mem (p : ℕ) (ξ : ⋀[B]^p (Ω[B⁄A])) : dp p ξ ∈ ⋀[B]^(p + 1) (Ω[B⁄A]) := by
  have hξ : ξ ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B p)) := by
    rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
  induction hξ using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [dp_apply_ιMulti]
      exact G_mem d1 d1_apply_smul d1_apply_D p v
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [dp_apply_smul]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
      have hd : p + 1 = 1 + p := by omega
      rw [hd]
      exact SetLike.mul_mem_graded (ι_mem_exteriorPower_one _) y.2

end

end DeRhamDifferential

namespace KaehlerDifferential

section

open DeRhamDifferential

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The de Rham differential `d : Ω^p_{B/A} → Ω^{p+1}_{B/A}` in degree `p`: the `A`-linear map
with `d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p` for all `b₀, …, b_p ∈ B`, where
`d : B → Ω[B⁄A]` is the universal `A`-derivation.  That rule is
`deRhamDifferential_smul_ιMulti_D` and `deRhamDifferential_unique` says it pins the map down. -/
@[stacks 0FKG "the differential itself"]
public noncomputable def deRhamDifferential (p : ℕ) :
    ⋀[B]^p (Ω[B⁄A]) →ₗ[A] ⋀[B]^(p + 1) (Ω[B⁄A]) :=
  LinearMap.codRestrict (Submodule.restrictScalars A (⋀[B]^(p + 1) (Ω[B⁄A]))) (dp p) (dp_mem p)

private lemma coe_deRhamDifferential (p : ℕ) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    (deRhamDifferential p ξ : Ext A B) = dp p ξ := rfl

/-- The defining rule of the de Rham differential:
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.  The leading scalar `b₀` contributes the
factor `d b₀` through `dp_apply_smul`, and `G_exact` kills the wedge of exact forms. -/
@[stacks 0FKG "the defining rule of `deRhamDifferential`"]
public lemma deRhamDifferential_smul_ιMulti_D (p : ℕ) (b : Fin (p + 1) → B) :
    deRhamDifferential p (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
      exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i) := by
  refine Subtype.ext ?_
  rw [coe_deRhamDifferential]
  show dp p (b 0 • exteriorPower.ιMulti B p fun i => D A B (b i.succ)) =
    ιMulti B (p + 1) fun i => D A B (b i)
  rw [dp_apply_smul, dp_apply_ιMulti, G_exact d1 d1_apply_D p fun i => b i.succ,
    smul_zero, zero_add]
  show ι B (D A B (b 0)) * ιMulti B p (fun i => D A B (b i.succ)) =
    ιMulti B (p + 1) fun i => D A B (b i)
  rw [ιMulti_succ_apply]
  rfl

/-- `deRhamDifferential p` is the only `A`-linear map `Ω^p_{B/A} → Ω^{p+1}_{B/A}` with
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`, because those elements span
`Ω^p_{B/A}` over `A`. -/
@[stacks 0FKG "uniqueness of `deRhamDifferential`"]
public theorem deRhamDifferential_unique (p : ℕ)
    (d : ⋀[B]^p (Ω[B⁄A]) →ₗ[A] ⋀[B]^(p + 1) (Ω[B⁄A]))
    (hd : ∀ b : Fin (p + 1) → B,
      d (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
        exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i)) :
    d = deRhamDifferential p :=
  LinearMap.ext_on (span_range_smul_ιMulti_D_eq_top p) <| by
    rintro _ ⟨b, rfl⟩
    rw [hd b, deRhamDifferential_smul_ιMulti_D p b]

/-- The de Rham differential kills a wedge `d c₁ ∧ ⋯ ∧ d c_p` of exact forms: it is the value of
the defining rule at `1 · d c₁ ∧ ⋯ ∧ d c_p`, a wedge with first factor `d 1 = 0`. -/
private lemma deRhamDifferential_ιMulti_D (p : ℕ) (c : Fin p → B) :
    deRhamDifferential (A := A) p (exteriorPower.ιMulti B p fun i ↦ D A B (c i)) = 0 := by
  have hz := deRhamDifferential_smul_ιMulti_D (A := A) (B := B) p (Fin.cons 1 c)
  simp only [Fin.cons_zero, Fin.cons_succ, one_smul] at hz
  rw [hz]
  exact (exteriorPower.ιMulti B (p + 1)).map_coord_zero (i := 0) (by simp)

/-- **The de Rham differential of `B` over `A` squares to zero.**  The elements
`b₀ · (d b₁ ∧ ⋯ ∧ d b_p)` span `Ω^p_{B/A}` over `A`, and on such an element the defining rule
computes the composite as a wedge whose first factor is `d 1 = 0`. -/
@[stacks 0FKF "the complex property d ∘ d = 0 of the de Rham complex of a ring map, on the \
exterior powers of the Kaehler differentials"]
public theorem deRhamDifferential_comp_self (p : ℕ) (ξ : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential (A := A) (p + 1) (deRhamDifferential p ξ) = 0 := by
  have hmem : ξ ∈ Submodule.span A (Set.range fun b : Fin (p + 1) → B ↦
      b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) := by
    rw [span_range_smul_ιMulti_D_eq_top (A := A) (B := B) p]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      rw [deRhamDifferential_smul_ιMulti_D, deRhamDifferential_ιMulti_D]
  | zero => simp
  | add v w hv hw ihv ihw => rw [map_add, map_add, ihv, ihw, add_zero]
  | smul a v hv ih => rw [map_smul, map_smul, ih, smul_zero]

/-- **Consecutive de Rham differentials compose to zero**, as an equality of `A`-linear maps.
This is the complex property of the de Rham complex of `B` over `A`. -/
@[stacks 0FKF "the complex property d ∘ d = 0 of the de Rham complex of a ring map, as an \
equality of A-linear maps"]
public theorem deRhamDifferential_comp_deRhamDifferential (p : ℕ) :
    (deRhamDifferential (A := A) (B := B) (p + 1)).comp (deRhamDifferential p) = 0 :=
  LinearMap.ext fun ξ ↦ deRhamDifferential_comp_self p ξ

end

end KaehlerDifferential
