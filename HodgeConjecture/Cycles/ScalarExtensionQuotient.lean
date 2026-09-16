import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension of a quotient by actual relation generators

If an existing module `N` realizes scalar extension of `M`, the scalar
extension of the quotient of `M` by a generated submodule is the quotient
of `N` by the scalar-extended generators. The equivalence is constructed
from the quotient and tensor universal properties and retains its formula
on representatives. It requires no flatness or injectivity assumption.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

open TensorProduct

universe uR uS uM uN uI

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN} {ι : Type uI}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

private def quotientScalarExtensionMap (r : ι → M) (f : M →ₗ[R] N) :
    S ⊗[R] (M ⧸ Submodule.span R (Set.range r)) →ₗ[S]
      N ⧸ Submodule.span S (Set.range (fun i ↦ f (r i))) :=
  ((Submodule.span R (Set.range r)).liftQ
    (((Submodule.span S (Set.range (fun i ↦ f (r i)))).mkQ.restrictScalars R).comp f)
    (by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change Submodule.Quotient.mk (f (r i)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.subset_span (Set.mem_range_self i)))).liftBaseChange S

private theorem quotientScalarExtensionMap_tmul_mk
    (r : ι → M) (f : M →ₗ[R] N) (s : S) (m : M) :
    quotientScalarExtensionMap r f (s ⊗ₜ[R] Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (s • f m) := rfl

private def quotientScalarExtensionInverse (r : ι → M) (f : M →ₗ[R] N)
    (E : (S ⊗[R] M) ≃ₗ[S] N)
    (hE : ∀ s m, E (s ⊗ₜ[R] m) = s • f m) :
    (N ⧸ Submodule.span S (Set.range (fun i ↦ f (r i)))) →ₗ[S]
      S ⊗[R] (M ⧸ Submodule.span R (Set.range r)) :=
  (Submodule.span S (Set.range (fun i ↦ f (r i)))).liftQ
    (((Submodule.span R (Set.range r)).mkQ.baseChange S).comp E.symm.toLinearMap)
    (by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change ((Submodule.span R (Set.range r)).mkQ.baseChange S) (E.symm (f (r i))) = 0
      have he : E.symm (f (r i)) = 1 ⊗ₜ[R] r i := by
        apply E.injective
        rw [E.apply_symm_apply, hE, one_smul]
      rw [he, LinearMap.baseChange_tmul]
      have hr : (Submodule.span R (Set.range r)).mkQ (r i) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.subset_span (Set.mem_range_self i))
      rw [hr, tmul_zero])

omit [IsScalarTower R S N] in
private theorem quotientScalarExtensionInverse_mk_image
    (r : ι → M) (f : M →ₗ[R] N) (E : (S ⊗[R] M) ≃ₗ[S] N)
    (hE : ∀ s m, E (s ⊗ₜ[R] m) = s • f m) (m : M) :
    quotientScalarExtensionInverse r f E hE (Submodule.Quotient.mk (f m)) =
      1 ⊗ₜ[R] Submodule.Quotient.mk m := by
  have he : E.symm (f m) = 1 ⊗ₜ[R] m := by
    apply E.injective
    rw [E.apply_symm_apply, hE, one_smul]
  change ((Submodule.span R (Set.range r)).mkQ.baseChange S) (E.symm (f m)) = _
  rw [he, LinearMap.baseChange_tmul]
  rfl

/-- Scalar extension commutes with the quotient by the span of the same
relation generators in an existing scalar-extension model. -/
def scalarExtensionQuotientEquiv (r : ι → M) (f : M →ₗ[R] N)
    (E : (S ⊗[R] M) ≃ₗ[S] N)
    (hE : ∀ s m, E (s ⊗ₜ[R] m) = s • f m) :
    (S ⊗[R] (M ⧸ Submodule.span R (Set.range r))) ≃ₗ[S]
      N ⧸ Submodule.span S (Set.range (fun i ↦ f (r i))) :=
  LinearEquiv.ofLinear (quotientScalarExtensionMap r f)
    (quotientScalarExtensionInverse r f E hE)
    (by
      apply Submodule.quot_hom_ext
      intro x
      obtain ⟨v, rfl⟩ := E.surjective x
      change quotientScalarExtensionMap r f
        (quotientScalarExtensionInverse r f E hE (Submodule.Quotient.mk (E v))) =
          Submodule.Quotient.mk (E v)
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s m =>
          rw [hE]
          simp only [Submodule.Quotient.mk_smul, map_smul,
            quotientScalarExtensionInverse_mk_image,
            quotientScalarExtensionMap_tmul_mk, one_smul]
      | add v w hv hw =>
          simp only [map_add, Submodule.Quotient.mk_add, hv, hw])
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s x
      induction x using Submodule.Quotient.induction_on with
      | H m =>
          change quotientScalarExtensionInverse r f E hE
            (quotientScalarExtensionMap r f (s ⊗ₜ[R] Submodule.Quotient.mk m)) =
              s ⊗ₜ[R] Submodule.Quotient.mk m
          rw [quotientScalarExtensionMap_tmul_mk]
          simp only [Submodule.Quotient.mk_smul, map_smul,
            quotientScalarExtensionInverse_mk_image, smul_tmul', smul_eq_mul, mul_one])

/-- The quotient equivalence sends a pure tensor of an actual class to
the class of its scalar-extended representative. -/
@[simp]
theorem scalarExtensionQuotientEquiv_tmul_mk (r : ι → M) (f : M →ₗ[R] N)
    (E : (S ⊗[R] M) ≃ₗ[S] N)
    (hE : ∀ s m, E (s ⊗ₜ[R] m) = s • f m) (s : S) (m : M) :
    scalarExtensionQuotientEquiv r f E hE (s ⊗ₜ[R] Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (s • f m) := rfl

end

end HodgeConjecture.SchemeCycles
