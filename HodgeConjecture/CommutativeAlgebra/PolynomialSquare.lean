module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The actual polynomial square map is finite free of rank two

Even and odd coefficient extraction constructs the decomposition
`f(X) = a(X²) + X b(X²)` over any commutative coefficient ring. A genuine
type copy of the target ring prevents its square-map scalar action from
colliding with the original polynomial ring's regular scalar action.
Transport through the original ring isomorphism then proves finiteness,
flatness and rank two for the original endomorphism itself.

The inverse image of the origin retains its nonreduced coordinate quotient
`k[X]/(X²)`, whose vector-space dimension and base-field module length are two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.PolynomialSquare

open Polynomial

universe u

variable (k : Type u) [CommRing k]

/-- The original coordinate-ring homomorphism of the polynomial square map. -/
def squareHom : k[X] →+* k[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ 2)

@[simp] theorem squareHom_C (c : k) : squareHom k (C c) = C c := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem squareHom_X : squareHom k X = X ^ 2 := by
  exact Polynomial.eval₂_X _ _

theorem squareHom_eq_expand (f : k[X]) : squareHom k f = Polynomial.expand k 2 f := rfl

theorem coeff_squareHom_even (f : k[X]) (n : ℕ) :
    (squareHom k f).coeff (2 * n) = f.coeff n := by
  change (Polynomial.expand k 2 f).coeff (2 * n) = _
  exact Polynomial.coeff_expand_mul' (by decide : 0 < 2) f n

theorem coeff_squareHom_odd (f : k[X]) (n : ℕ) :
    (squareHom k f).coeff (2 * n + 1) = 0 := by
  have hn : ¬ 2 ∣ 2 * n + 1 := by
    rintro ⟨d, hd⟩
    omega
  change (Polynomial.expand k 2 f).coeff (2 * n + 1) = _
  rw [Polynomial.coeff_expand (by decide : 0 < 2)]
  simp only [hn, ↓reduceIte]

/-- The two coefficient polynomials are assembled using the original square homomorphism. -/
def assemble (v : Fin 2 → k[X]) : k[X] :=
  squareHom k (v 0) + X * squareHom k (v 1)

theorem coeff_assemble_even (v : Fin 2 → k[X]) (n : ℕ) :
    (assemble k v).coeff (2 * n) = (v 0).coeff n := by
  rw [assemble, coeff_add, coeff_squareHom_even]
  have hx : (X * squareHom k (v 1)).coeff (2 * n) = 0 := by
    cases n with
    | zero => simp
    | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        coeff_X_mul, coeff_squareHom_odd]
  rw [hx, add_zero]

theorem coeff_assemble_odd (v : Fin 2 → k[X]) (n : ℕ) :
    (assemble k v).coeff (2 * n + 1) = (v 1).coeff n := by
  rw [assemble, coeff_add, coeff_squareHom_odd, coeff_X_mul,
    coeff_squareHom_even, zero_add]

/-- Actual even/odd coefficients, with no division by two in the coefficient ring. -/
def coefficients (f : k[X]) : Fin 2 → k[X] :=
  fun i ↦ if i = 0 then Polynomial.contract 2 f else Polynomial.contract 2 f.divX

@[simp] theorem coefficients_zero (f : k[X]) :
    coefficients k f 0 = Polynomial.contract 2 f := by simp [coefficients]

@[simp] theorem coefficients_one (f : k[X]) :
    coefficients k f 1 = Polynomial.contract 2 f.divX := by simp [coefficients]

theorem assemble_coefficients (f : k[X]) : assemble k (coefficients k f) = f := by
  ext n
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with h | h
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, coeff_assemble_even, coefficients_zero,
      Polynomial.coeff_contract (by decide : 2 ≠ 0)]
    congr 1
    omega
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, coeff_assemble_odd, coefficients_one,
      Polynomial.coeff_contract (by decide : 2 ≠ 0), Polynomial.coeff_divX]
    congr 1
    omega

theorem assemble_injective : Function.Injective (assemble k) := by
  intro v w h
  apply _root_.funext
  refine (Fin.forall_fin_two.mpr ?_ : ∀ i : Fin 2, v i = w i)
  constructor
  · ext n
    have hc := congrArg (fun f : k[X] ↦ f.coeff (2 * n)) h
    simpa only [coeff_assemble_even] using hc
  · ext n
    have hc := congrArg (fun f : k[X] ↦ f.coeff (2 * n + 1)) h
    simpa only [coeff_assemble_odd] using hc

/-- A genuine copy of the original target ring; its elements retain their actual polynomials. -/
abbrev Extension := ULift.{0} k[X]

/-- The original polynomial representative of an element of the target copy. -/
def downEquiv : Extension k ≃+* k[X] := ULift.ringEquiv

/-- The square algebra map on the target copy, retaining the original coordinate homomorphism. -/
def extensionHom : k[X] →+* Extension k :=
  (downEquiv k).symm.toRingHom.comp (squareHom k)

@[instance_reducible]
def squareAlgebra : Algebra k[X] (Extension k) := (extensionHom k).toAlgebra

attribute [local instance] squareAlgebra

/-- The square-map module structure on the target copy; coefficient polynomials keep
their original regular module structure. -/
@[instance_reducible]
def squareModule : Module k[X] (Extension k) := Algebra.toModule

attribute [local instance] squareModule

@[simp] theorem extensionHom_down (f : k[X]) : (extensionHom k f).down = squareHom k f := rfl

@[simp] theorem algebraMap_down (f : k[X]) :
    (algebraMap k[X] (Extension k) f).down = squareHom k f := rfl

theorem down_comp_extensionHom :
    (downEquiv k).toRingHom.comp (extensionHom k) = squareHom k := by
  apply RingHom.ext
  intro f
  rfl

/-- Assembly is linear for the actual square-map scalar action on the target copy. -/
def assembleLinear : (Fin 2 → k[X]) →ₗ[k[X]] Extension k where
  toFun v := ⟨assemble k v⟩
  map_add' v w := by
    apply ULift.ext
    change squareHom k (v 0 + w 0) + X * squareHom k (v 1 + w 1) =
      (squareHom k (v 0) + X * squareHom k (v 1)) +
        (squareHom k (w 0) + X * squareHom k (w 1))
    simp only [map_add]
    ring
  map_smul' r v := by
    apply ULift.ext
    change squareHom k (r * v 0) + X * squareHom k (r * v 1) =
      squareHom k r * (squareHom k (v 0) + X * squareHom k (v 1))
    simp only [map_mul]
    ring

/-- The actual even/odd decomposition as a linear equivalence over the original coordinate ring. -/
def linearEquiv : (Fin 2 → k[X]) ≃ₗ[k[X]] Extension k :=
  LinearEquiv.ofBijective (assembleLinear k) ⟨
    fun _v _w h ↦ assemble_injective k (congrArg ULift.down h),
    fun f ↦ ⟨coefficients k f.down, ULift.ext (assemble_coefficients k f.down)⟩⟩

/-- The basis whose actual polynomial representatives are exactly `1,X`. -/
def oneXBasis : Module.Basis (Fin 2) k[X] (Extension k) :=
  (Pi.basisFun k[X] (Fin 2)).map (linearEquiv k)

@[simp] theorem oneXBasis_zero_down : (oneXBasis k 0).down = 1 := by
  simp [oneXBasis, Pi.basisFun_apply, linearEquiv, assembleLinear, assemble]

@[simp] theorem oneXBasis_one_down : (oneXBasis k 1).down = X := by
  simp [oneXBasis, Pi.basisFun_apply, linearEquiv, assembleLinear, assemble]

theorem extension_free : Module.Free k[X] (Extension k) :=
  Module.Free.of_basis (oneXBasis k)

theorem extension_finite : Module.Finite k[X] (Extension k) :=
  Module.Finite.of_basis (oneXBasis k)

theorem extensionHom_finite : (extensionHom k).Finite := by
  let := extension_finite k
  change (algebraMap k[X] (Extension k)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem extensionHom_flat : (extensionHom k).Flat := by
  let := extension_free k
  change (algebraMap k[X] (Extension k)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Finiteness of the exact original square homomorphism, transported through the target ring copy. -/
theorem squareHom_finite : (squareHom k).Finite := by
  rw [← down_comp_extensionHom k]
  exact RingHom.Finite.comp (downEquiv k).finite (extensionHom_finite k)

/-- The exact original square homomorphism is flat because its actual target module has basis `1,X`. -/
theorem squareHom_flat : (squareHom k).Flat := by
  rw [← down_comp_extensionHom k]
  exact (extensionHom_flat k).comp
    (RingHom.Flat.of_bijective (downEquiv k).bijective)

variable [Nontrivial k]

theorem extension_finrank : Module.finrank k[X] (Extension k) = 2 := by
  rw [Module.finrank_eq_card_basis (oneXBasis k), Fintype.card_fin]

/-- Rank at every prime belongs to the original square map, with no supplied rank hypothesis. -/
theorem squareHom_finrank (x : PrimeSpectrum k[X]) : (squareHom k).finrank x = 2 := by
  rw [← down_comp_extensionHom k,
    RingHom.finrank_comp_left_of_bijective (extensionHom k) (downEquiv k).toRingHom
      (downEquiv k).bijective (extensionHom_finite k) (extensionHom_flat k)]
  let := extension_free k
  change Module.rankAtStalk (Extension k) x = 2
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact extension_finrank k

omit [Nontrivial k] in
/-- The actual inverse-image ideal of the original origin retains its square. -/
theorem map_origin_ideal :
    (Ideal.span ({X} : Set k[X])).map (squareHom k) = Ideal.span ({X ^ 2} : Set k[X]) := by
  rw [Ideal.map_span, Set.image_singleton, squareHom_X]

end HodgeConjecture.PolynomialSquare

namespace HodgeConjecture.PolynomialSquare

open Polynomial

universe u

variable (k : Type u) [Field k]

/-- The original nonreduced coordinate quotient of the fiber over the origin. -/
abbrev zeroFiber := k[X] ⧸ Ideal.span ({X ^ 2} : Set k[X])

theorem zeroFiber_finrank : Module.finrank k (zeroFiber k) = 2 := by
  rw [finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_X_pow (R := k) 2

theorem zeroFiber_length_over_base : Module.length k (zeroFiber k) = 2 := by
  let : Module.Finite k (zeroFiber k) := (Polynomial.monic_X_pow 2).finite_quotient
  rw [Module.length_eq_finrank, zeroFiber_finrank]
  rfl

theorem zeroFiber_root_sq :
    (AdjoinRoot.root (X ^ 2 : k[X]) : zeroFiber k) ^ 2 = 0 := by
  change ((AdjoinRoot.mk (X ^ 2 : k[X])) X) ^ 2 = 0
  exact ((AdjoinRoot.mk (X ^ 2 : k[X])).map_pow X 2).symm.trans AdjoinRoot.mk_self

theorem zeroFiber_root_ne_zero :
    (AdjoinRoot.root (X ^ 2 : k[X]) : zeroFiber k) ≠ 0 := by
  intro h
  change AdjoinRoot.mk (X ^ 2 : k[X]) X = 0 at h
  have hdiv := AdjoinRoot.mk_eq_zero.mp h
  have hd := Polynomial.natDegree_le_of_dvd hdiv (Polynomial.X_ne_zero (R := k))
  norm_num at hd

end HodgeConjecture.PolynomialSquare

end
