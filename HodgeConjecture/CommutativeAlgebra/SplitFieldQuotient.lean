module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-!
# Integral quotients of a finite product of fields

Every prime ideal of `I → K`, for `I` finite and `K` a field, is the
kernel of evaluation at a unique coordinate. Its quotient is therefore
canonically isomorphic to `K` after choosing that coordinate.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitFieldQuotient

noncomputable section

universe u v

variable (K : Type u) [Field K] (I : Type v) [Finite I]

/-- Prime ideals of a finite product of copies of a field are precisely
the coordinate kernels; the coordinate is unique. -/
theorem existsUnique_prime_eq_ker_eval (p : Ideal (I → K)) [p.IsPrime] :
    ∃! i : I, p = RingHom.ker (Pi.evalRingHom (fun _ : I ↦ K) i) := by
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨p, inferInstance⟩ : PrimeSpectrum (I → K))
  have hq0 : q = (default : PrimeSpectrum K) := Subsingleton.elim _ _
  subst q
  have hi : p = RingHom.ker (Pi.evalRingHom (fun _ : I ↦ K) i) :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  have h : PrimeSpectrum.sigmaToPi (fun _ : I ↦ K) ⟨j, default⟩ =
      PrimeSpectrum.sigmaToPi (fun _ : I ↦ K) ⟨i, default⟩ := by
    apply PrimeSpectrum.ext
    exact hj.symm.trans hi
  exact congrArg Sigma.fst (PrimeSpectrum.sigmaToPi_injective _ h)

/-- The quotient by a coordinate prime is the original field. -/
def evalQuotientEquiv (i : I) :
    ((I → K) ⧸ RingHom.ker (Pi.evalRingHom (fun _ : I ↦ K) i)) ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := Pi.evalAlgHom K (fun _ : I ↦ K) i) (fun x ↦ ⟨fun _ ↦ x, rfl⟩)

omit [Finite I] in
@[simp]
theorem evalQuotientEquiv_apply_mk (i : I) (x : I → K) :
    evalQuotientEquiv K I i (Ideal.Quotient.mk _ x) = x i := rfl

/-- Every integral quotient of the finite split coordinate ring is a
single reduced rational point at the ring level. -/
theorem exists_prime_quotient_equiv (p : Ideal (I → K)) [p.IsPrime] :
    Nonempty (((I → K) ⧸ p) ≃ₐ[K] K) := by
  obtain ⟨i, rfl, _⟩ := existsUnique_prime_eq_ker_eval K I p
  exact ⟨evalQuotientEquiv K I i⟩

end

end HodgeConjecture.SplitFieldQuotient
