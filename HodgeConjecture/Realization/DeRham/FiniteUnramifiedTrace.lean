module

public import HodgeConjecture.Realization.DeRham.AffineDegreeZero
public import HodgeConjecture.Realization.Transfer
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

/-!
# Actual traces on degree-zero de Rham cohomology of unramified algebras

When the source and target are formally unramified over the base, their
Kähler differentials vanish. The ordinary algebra trace therefore induces
a map on the actual closed-function kernels. A finite basis gives the
degree formula. No trace map or degree identity is supplied as a field.

This is the degree-zero, affine unramified case of the Stacks trace route.
It does not construct the general finite-syntomic trace on hypercohomology.
-/

set_option autoImplicit false

namespace HodgeConjecture

namespace AffineDeRham

open scoped BigOperators

noncomputable section

universe u

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra.FormallyUnramified k A] [Algebra.FormallyUnramified k B]

/-- Pullback induced by the structural homomorphism of the original algebras. -/
def finitePullback : H0 k A →ₗ[k] H0 k B :=
  (map k (IsScalarTower.toAlgHom k A B)).toLinearMap

/-- The actual algebra trace, restricted to the closed-function models. -/
def finiteTrace : H0 k B →ₗ[k] H0 k A :=
  (unramifiedCoordinates k A).symm.toLinearMap.comp
    (((Algebra.trace A B).restrictScalars k).comp (unramifiedCoordinates k B).toLinearMap)

omit [Algebra.FormallyUnramified k A] [Algebra.FormallyUnramified k B] in
@[simp]
theorem finitePullback_coe (a : H0 k A) :
    (finitePullback k A B a).val = algebraMap A B a.val := rfl

@[simp]
theorem finiteTrace_coe (a : H0 k B) :
    (finiteTrace k A B a).val = Algebra.trace A B a.val := rfl

/-- The degree is the size of an actual finite basis of the original algebra. -/
theorem finiteTrace_finitePullback_of_basis {ι : Type u} [Fintype ι]
    (b : Module.Basis ι A B) (a : H0 k A) :
    finiteTrace k A B (finitePullback k A B a) = Fintype.card ι • a := by
  apply Subtype.ext
  exact Algebra.trace_algebraMap_of_basis b a.val

/-- Geometric module rank gives the same degree when the base has invariant basis number. -/
theorem finiteTrace_finitePullback [StrongRankCondition A] [Module.Free A B]
    (a : H0 k A) :
    finiteTrace k A B (finitePullback k A B a) = Module.finrank A B • a := by
  apply Subtype.ext
  exact Algebra.trace_algebraMap a.val

/-- The split algebra trace is the sum of its actual component values. -/
theorem algebraTrace_pi (J : Type u) [Fintype J] (a : J → A) :
    Algebra.trace A (J → A) a = ∑ j, a j := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun A J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [Algebra.leftMulMatrix_eq_repr_mul]

end

end AffineDeRham

namespace RationalAffineDeRham

open AffineDeRham

noncomputable section

variable (A B : Type) [CommRing A] [CommRing B]
  [Algebra ℚ A] [Algebra ℚ B] [Algebra A B] [IsScalarTower ℚ A B]
  [Algebra.FormallyUnramified ℚ A] [Algebra.FormallyUnramified ℚ B]

/-- An actual finite free map supplies rational de Rham transfer in degree zero. -/
def finiteFreeTransfer (d : ℕ) (hd : d ≠ 0) (b : Module.Basis (Fin d) A B) :
    RationalDegreeTransfer (H0 ℚ B) (H0 ℚ A) where
  pull := finitePullback ℚ A B
  push := finiteTrace ℚ A B
  degree := d
  degree_ne_zero := hd
  push_comp_pull := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Nat.cast_smul_eq_nsmul, Fintype.card_fin] using
      finiteTrace_finitePullback_of_basis ℚ A B b a

theorem finitePullback_injective (d : ℕ) (hd : d ≠ 0)
    (b : Module.Basis (Fin d) A B) : Function.Injective (finitePullback ℚ A B) :=
  (finiteFreeTransfer A B d hd b).pull_injective

end

end RationalAffineDeRham

end HodgeConjecture
