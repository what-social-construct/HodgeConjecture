module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

@[expose] public section

/-!
# Lifting an actual polynomial normalization of a prime quotient

A polynomial algebra map to a quotient lifts by choosing representatives
of the images of its variables. The quotient composite is the original
map, not merely an isomorphic polynomial presentation. Injectivity of that
composite implies injectivity upstairs and disjointness of the image of
nonzero polynomial elements from the selected prime.

For a finite-type algebra over a field, Noether normalization is applied
to the actual prime quotient. The original algebra need not be a domain.
No integrality of the lifted map to the original algebra is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable (k : Type u) (B : Type v) [CommRing k] [CommRing B] [Algebra k B]

/-- Lift the images of the actual polynomial generators through the quotient map. -/
def quotientPolynomialLift (q : Ideal B) (n : ℕ)
    (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q) : MvPolynomial (Fin n) k →ₐ[k] B :=
  MvPolynomial.aeval fun i ↦ (Ideal.Quotient.mkₐ_surjective k q (g (MvPolynomial.X i))).choose

/-- The lifted polynomial map has exactly the prescribed quotient composite. -/
@[simp] theorem quotient_comp_quotientPolynomialLift (q : Ideal B) (n : ℕ)
    (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q) :
    (Ideal.Quotient.mkₐ k q).comp (quotientPolynomialLift k B q n g) = g := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, quotientPolynomialLift, MvPolynomial.aeval_X] using
    (Ideal.Quotient.mkₐ_surjective k q (g (MvPolynomial.X i))).choose_spec

/-- Injectivity of the original quotient map is retained by its polynomial lift. -/
theorem quotientPolynomialLift_injective (q : Ideal B) (n : ℕ)
    (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q) (hinj : Function.Injective g) :
    Function.Injective (quotientPolynomialLift k B q n g) := by
  intro a b hab
  apply hinj
  rw [← quotient_comp_quotientPolynomialLift k B q n g]
  exact congrArg (Ideal.Quotient.mkₐ k q) hab

/-- A nonzero polynomial cannot map into the ideal when the quotient composite is injective. -/
theorem polynomial_notMem_of_quotient_injective (q : Ideal B) (n : ℕ)
    (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f))
    (a : MvPolynomial (Fin n) k) (ha : a ≠ 0) : f a ∉ q := by
  intro hmem
  apply ha
  apply hinj
  simpa only [AlgHom.comp_apply, map_zero, Ideal.Quotient.mkₐ_eq_mk] using
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem

/-- The actual lifted images of nonzero polynomials avoid the original ideal. -/
theorem quotientPolynomialLift_notMem (q : Ideal B) (n : ℕ)
    (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q) (hinj : Function.Injective g)
    (a : MvPolynomial (Fin n) k) (ha : a ≠ 0) :
    quotientPolynomialLift k B q n g a ∉ q := by
  apply polynomial_notMem_of_quotient_injective k B q n _ _ a ha
  simpa using hinj

/-- The multiplicative subset used for localization is contained in the selected prime complement.
For a field base its source is exactly the nonzero polynomial elements. -/
theorem polynomial_map_nonZeroDivisors_le_primeCompl [Nontrivial k]
    (q : Ideal B) [q.IsPrime] (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f)) :
    (nonZeroDivisors (MvPolynomial (Fin n) k)).map f.toMonoidHom ≤ q.primeCompl := by
  rintro _ ⟨a, ha, rfl⟩
  exact polynomial_notMem_of_quotient_injective k B q n f hinj a
    (nonZeroDivisors.ne_zero ha)

/-- Set-theoretic disjointness of the actual multiplicative image and the selected prime. -/
theorem polynomial_map_nonZeroDivisors_disjoint [Nontrivial k]
    (q : Ideal B) [q.IsPrime] (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f)) :
    Disjoint (↑((nonZeroDivisors (MvPolynomial (Fin n) k)).map f.toMonoidHom) : Set B)
      (q : Set B) := by
  rw [Set.disjoint_left]
  intro b hb hq
  exact polynomial_map_nonZeroDivisors_le_primeCompl k B q n f hinj hb hq

/-- Noether normalization of the actual prime quotient, lifted to the original finite-type algebra.
Only the quotient composite is claimed integral; no domain hypothesis on the original algebra
and no localization conclusion are included. -/
theorem exists_lifted_residue_normalization (k : Type u) [Field k]
    (B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (q : Ideal B) [q.IsPrime] :
    ∃ n, ∃ f : MvPolynomial (Fin n) k →ₐ[k] B,
      Function.Injective f ∧
        Function.Injective ((Ideal.Quotient.mkₐ k q).comp f) ∧
        ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k (B ⧸ q)
  refine ⟨n, quotientPolynomialLift k B q n g,
    quotientPolynomialLift_injective k B q n g hinj, ?_, ?_⟩
  · simpa using hinj
  · simpa using hint

end

end HodgeConjecture.SchemeCycles
