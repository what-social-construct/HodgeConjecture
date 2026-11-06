module

public import HodgeConjecture.Realization.DeRham.Polynomial
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

/-!
# Closed functions on finite disjoint unions of affine lines

The original coordinate ring is a finite product of polynomial rings.
Closed functions are exactly the functions constant on each affine line;
the component selectors give a basis of the actual degree-zero kernel.
No topological component comparison or cycle-class map is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open CategoryTheory KaehlerDifferential
open scoped Polynomial BigOperators

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- Component idempotents are closed in every characteristic, with no reducedness hypothesis. -/
theorem idempotent_closed {A : Type u} [CommRing A] [Algebra k A]
    {e : A} (he : IsIdempotentElem e) : D k A e = 0 := by
  have h : e • D k A e + e • D k A e = D k A e := by
    simpa only [Derivation.leibniz] using congrArg (D k A) he.eq
  have h' : e • D k A e = 0 := by
    have hh := congrArg (e • ·) h
    simpa only [smul_add, smul_smul, he.eq, add_eq_left] using hh
  simpa only [h', zero_add] using h.symm

variable (I : Type u) [Finite I]

/-- The original inclusion of componentwise constant functions into the polynomial rings. -/
def componentConstants : (I → k) →ₐ[k] H0 k (I → k[X]) :=
  (map k (AlgHom.pi fun i ↦
    (IsScalarTower.toAlgHom k k k[X]).comp (Pi.evalAlgHom k (fun _ : I ↦ k) i))).comp
      (unramifiedCoordinates k (I → k)).symm.toAlgHom

@[simp]
theorem componentConstants_coe (a : I → k) (i : I) :
    (componentConstants k I a).val i = Polynomial.C (a i) := rfl

variable [HasUniqueDiv k]

/-- A function on a finite union of affine lines is closed precisely when it is
constant on each original component. -/
theorem closed_affineLines_iff (p : I → k[X]) :
    D k (I → k[X]) p = 0 ↔ ∀ i, p i = Polynomial.C ((p i).coeff 0) := by
  constructor
  · intro hp i
    exact eq_C_of_closed k k
      (map_closed k (Pi.evalAlgHom k (fun _ : I ↦ k[X]) i) hp)
  · intro hp
    have h := (componentConstants k I (fun i ↦ (p i).coeff 0)).property
    change D k (I → k[X]) (fun i ↦ Polynomial.C ((p i).coeff 0)) = 0 at h
    simpa only [← funext hp] using h

/-- Component evaluation computes the actual degree-zero cohomology algebra. -/
def affineLinesCoordinates : H0 k (I → k[X]) ≃ₐ[k] (I → k) :=
  (AlgEquiv.ofBijective (componentConstants k I) ⟨
    fun _a _b h ↦ funext fun i ↦ Polynomial.C_injective (congrArg (fun p ↦ p.val i) h),
    fun p ↦ ⟨fun i ↦ (p.val i).coeff 0, Subtype.ext
      (funext fun i ↦ ((closed_affineLines_iff k I p.val).mp p.property i).symm)⟩⟩).symm

@[simp]
theorem affineLinesCoordinates_symm_coe (a : I → k) (i : I) :
    ((affineLinesCoordinates k I).symm a).val i = Polynomial.C (a i) := rfl

/-- These coordinates are evaluation on each original affine component. -/
theorem affineLinesCoordinates_apply (p : H0 k (I → k[X])) (i : I) :
    affineLinesCoordinates k I p i = (p.val i).coeff 0 := by
  have h := congrArg (fun q : H0 k (I → k[X]) ↦ (q.val i).coeff 0)
    ((affineLinesCoordinates k I).symm_apply_apply p)
  simpa only [affineLinesCoordinates_symm_coe, Polynomial.coeff_C_zero] using h

/-- Evaluation at any point of a component gives its same cohomology coordinate. -/
theorem affineLines_eval_closed (p : H0 k (I → k[X])) (i : I) (a : k) :
    Polynomial.aeval a (p.val i) = affineLinesCoordinates k I p i := by
  rw [(closed_affineLines_iff k I p.val).mp p.property i,
    Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    affineLinesCoordinates_apply]

/-- Component coordinates identify categorical homology of the constructed complex. -/
def affineLinesCohomologyZeroIso :
    (deRhamComplex k (I → k[X])).homology 0 ≅ ModuleCat.of k (I → k) :=
  cohomologyZeroIso k (I → k[X]) ≪≫ (affineLinesCoordinates k I).toLinearEquiv.toModuleIso

/-- The component characteristic functions form a basis of the actual de Rham kernel. -/
def affineLinesBasis : Module.Basis I k (H0 k (I → k[X])) :=
  (Pi.basisFun k I).map (affineLinesCoordinates k I).symm.toLinearEquiv

@[simp]
theorem affineLinesBasis_coe [DecidableEq I] (i j : I) :
    (affineLinesBasis k I i).val j = if j = i then 1 else 0 := by
  classical
  simp [affineLinesBasis, Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- Each basis class is the actual characteristic idempotent of its component. -/
theorem affineLinesBasis_isIdempotent (i : I) :
    IsIdempotentElem (affineLinesBasis k I i) := by
  classical
  apply Subtype.ext
  funext j
  simp only [Subalgebra.coe_mul, Pi.mul_apply, affineLinesBasis_coe]
  split_ifs <;> simp

end

section Dimension

universe u

variable (k I : Type u) [Field k] [CharZero k] [Fintype I]

/-- The dimension is the number of original affine components, including the empty product. -/
theorem affineLines_finrank :
    Module.finrank k (H0 k (I → k[X])) = Fintype.card I := by
  exact Module.finrank_eq_card_basis (affineLinesBasis k I)

end Dimension

end HodgeConjecture.AffineDeRham
