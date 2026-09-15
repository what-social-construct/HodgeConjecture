import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.Height

/-!
# Localization along an integral prime quotient

Suppose `R` is a domain and `R → S/q` is injective and integral. Localizing
`S` at the images of the nonzero elements of `R` makes `q` maximal while
preserving its contraction and height. The proof localizes the quotient
at the same denominators and obtains a domain integral over `Frac(R)`,
hence a field. The ambient ring `S` need not be a domain.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
  [CommRing S] [Algebra R S]

private theorem residueLocalization_disjoint
    (q : Ideal S) [q.IsPrime]
    (hinj : Function.Injective (algebraMap R (S ⧸ q))) :
    Disjoint (Algebra.algebraMapSubmonoid S (nonZeroDivisors R) : Set S) q := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨r, hr, rfl⟩ hq
  have hzero : algebraMap R (S ⧸ q) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hq
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    ((map_eq_zero_iff _ hinj).mp hzero)

variable (S' : Type w) [CommRing S'] [Algebra S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S']

/-- The extended prime contracts to the original prime. Only injectivity
of the map to the quotient is needed for this conclusion. -/
theorem residueLocalization_comap_map
    (q : Ideal S) [q.IsPrime]
    (hinj : Function.Injective (algebraMap R (S ⧸ q))) :
    (q.map (algebraMap S S')).comap (algebraMap S S') = q :=
  IsLocalization.comap_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S' q inferInstance
    (residueLocalization_disjoint R S q hinj)

/-- The prime remains prime after the actual localization. -/
theorem residueLocalization_map_isPrime
    (q : Ideal S) [q.IsPrime]
    (hinj : Function.Injective (algebraMap R (S ⧸ q))) :
    (q.map (algebraMap S S')).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S' q inferInstance
    (residueLocalization_disjoint R S q hinj)

/-- An integral quotient becomes a field after inverting the nonzero
base elements, so the original prime extends to a maximal ideal. -/
theorem residueLocalization_map_isMaximal
    (q : Ideal S) [q.IsPrime]
    (hinj : Function.Injective (algebraMap R (S ⧸ q)))
    (hint : (algebraMap R (S ⧸ q)).IsIntegral) :
    (q.map (algebraMap S S')).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  let N := Algebra.algebraMapSubmonoid (S ⧸ q) (nonZeroDivisors R)
  let T := Localization N
  letI : IsLocalization N T := Localization.isLocalization
  have hMN : M.map (Ideal.Quotient.mk q) = N := by
    exact Algebra.algebraMapSubmonoid_map_eq (nonZeroDivisors R) (Ideal.Quotient.mkₐ R q)
  letI : IsLocalization (M.map (Ideal.Quotient.mk q)) T := by
    rw [hMN]
    infer_instance
  letI : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := N)
    (map_le_nonZeroDivisors_of_injective (algebraMap R (S ⧸ q)) hinj le_rfl)
  letI : Algebra.IsIntegral R (S ⧸ q) := ⟨hint⟩
  let f : FractionRing R →+* T :=
    IsLocalization.map (M := nonZeroDivisors R) (S := FractionRing R) (T := N)
      T (algebraMap R (S ⧸ q)) (nonZeroDivisors R).le_comap_map
  letI : Algebra (FractionRing R) T := f.toAlgebra
  letI : Algebra.IsIntegral (FractionRing R) T :=
    ⟨show f.IsIntegral from isIntegral_localization (R := R) (S := S ⧸ q)
      (Rₘ := FractionRing R) (Sₘ := T) (M := nonZeroDivisors R)⟩
  letI : Field T := (isField_of_isIntegral_of_isField' (R := FractionRing R)
    (S := T) (Field.toIsField _)).toField
  let g : S' →+* T := IsLocalization.map T (Ideal.Quotient.mk q) M.le_comap_map
  have hg : Function.Surjective g :=
    IsLocalization.map_surjective_of_surjective M S' T (Ideal.Quotient.mk_surjective (I := q))
  have hker : RingHom.ker g = q.map (algebraMap S S') := by
    simpa only [Ideal.mk_ker] using
      (IsLocalization.ker_map (S := S') T (Ideal.Quotient.mk q) hMN)
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective g hg

/-- Localization preserves the complete prime height, not just a bound.
The primality proof is constructed from the quotient injection. -/
theorem residueLocalization_primeHeight_map
    (q : Ideal S) [q.IsPrime]
    (hinj : Function.Injective (algebraMap R (S ⧸ q))) :
    letI := residueLocalization_map_isPrime R S S' q hinj
    (q.map (algebraMap S S')).primeHeight = q.primeHeight := by
  letI := residueLocalization_map_isPrime R S S' q hinj
  have h := IsLocalization.primeHeight_comap
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
    (q.map (algebraMap S S'))
  simpa only [residueLocalization_comap_map R S S' q hinj] using h.symm

end

end HodgeConjecture.CommutativeAlgebra
