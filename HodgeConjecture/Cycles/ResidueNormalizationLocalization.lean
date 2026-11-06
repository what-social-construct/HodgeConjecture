module

public import HodgeConjecture.Cycles.ResidueNormalizationLift
public import HodgeConjecture.CommutativeAlgebra.GenericFiberAlgebra
public import HodgeConjecture.CommutativeAlgebra.ResidueLocalization
public import HodgeConjecture.Cycles.NormalizationLocalDimension

@[expose] public section

/-!
# The actual localization of a lifted residue normalization

A polynomial normalization of `B/q` lifts to `B`. Inverting the images
of its nonzero polynomials constructs a finite-type algebra over the
actual polynomial fraction field. The extended prime is maximal and
retains its contraction and height. For domain `B`, the preceding
maximal-height theorem computes the original prime height over this new
coefficient field. No integrality of the lifted map into `B` is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open CommutativeAlgebra

noncomputable section

universe u v

variable (k : Type u) [Field k] (B : Type v) [CommRing B]
  [Algebra k B] [Algebra.FiniteType k B]

/-- An actual lifted quotient normalization constructs a finite-type
generic fiber, a maximal extended prime, and exact contraction and height.
The ambient algebra need not be a domain. -/
theorem residueNormalization_localization
    (q : Ideal B) [q.IsPrime] (n : ℕ)
    (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f))
    (hint : ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    Algebra.FiniteType (FractionRing (MvPolynomial (Fin n) k)) B' ∧
      (q.map (algebraMap B B')).IsMaximal ∧
      (q.map (algebraMap B B')).comap (algebraMap B B') = q ∧
      (q.map (algebraMap B B')).height = q.height := by
  algebraize [f.toRingHom]
  let P := MvPolynomial (Fin n) k
  let B' := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
  letI := genericFiberAlgebra P B B'
  letI : IsScalarTower P (FractionRing P) B' := genericFiberAlgebra_isScalarTower P B B'
  letI : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType k P B
  refine ⟨genericFiber_finiteType P B B',
    residueLocalization_map_isMaximal P B B' q hinj hint,
    residueLocalization_comap_map P B B' q hinj, ?_⟩
  letI := residueLocalization_map_isPrime P B B' q hinj
  skip
  exact residueLocalization_primeHeight_map P B B' q hinj

/-- Noether normalization of the actual prime quotient supplies all
inputs to the residue-localization construction. -/
theorem exists_residueNormalization_localization
    (q : Ideal B) [q.IsPrime] :
    ∃ n, ∃ f : MvPolynomial (Fin n) k →ₐ[k] B,
      Function.Injective f ∧
      Function.Injective ((Ideal.Quotient.mkₐ k q).comp f) ∧
      ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral ∧
      (letI := f.toRingHom.toAlgebra
       let B' := Localization
         (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
       letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
       Algebra.FiniteType (FractionRing (MvPolynomial (Fin n) k)) B' ∧
         (q.map (algebraMap B B')).IsMaximal ∧
         (q.map (algebraMap B B')).comap (algebraMap B B') = q ∧
         (q.map (algebraMap B B')).height = q.height) := by
  obtain ⟨n, f, hf, hinj, hint⟩ := exists_lifted_residue_normalization k B q
  exact ⟨n, f, hf, hinj, hint, residueNormalization_localization k B q n f hinj hint⟩

/-- For a domain, preserved height and the proved maximal-height formula
identify the original prime height with the generic fiber's transcendence
degree over the actual polynomial fraction field. -/
theorem primeHeight_eq_residueNormalization_trdeg [IsDomain B]
    (q : Ideal B) [q.IsPrime] (n : ℕ)
    (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f))
    (hint : ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    q.height =
      ((Algebra.trdeg (FractionRing (MvPolynomial (Fin n) k)) B').toNat : ℕ∞) := by
  algebraize [f.toRingHom]
  let P := MvPolynomial (Fin n) k
  let B' := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
  letI := genericFiberAlgebra P B B'
  have h := residueNormalization_localization k B q n f hinj hint
  letI : Algebra.FiniteType (FractionRing P) B' := h.1
  letI : (q.map (algebraMap B B')).IsMaximal := h.2.1
  have hf : Function.Injective (algebraMap P B) := by
    intro a b hab
    exact hinj (congrArg (Ideal.Quotient.mk q) hab)
  letI : IsDomain B' := genericFiber_isDomain P B B' hf
  rw [← residueLocalization_primeHeight_map P B B' q hinj]
  exact primeHeight_eq_trdeg_toNat_of_isMaximal (FractionRing P) B' _

end

end HodgeConjecture.SchemeCycles
