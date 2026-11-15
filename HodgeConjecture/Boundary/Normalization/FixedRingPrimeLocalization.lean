module

public import HodgeConjecture.Boundary.Normalization.FixedRingLocalizationComparison
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

/-!
# The selected prime under fixed-ring localization

For an equivariant localization, the prime below the image of `Q` in the
localized fixed ring contracts to the prime below `Q` in the original fixed
ring. This identifies the selected primes in the local-ring comparison.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Contracting the image prime through the fixed-ring localization recovers
the original selected fixed-ring prime. -/
theorem fixedSubalgebra_under_map_of_isLocalization
    {A S T G : Type*}
    [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [Group G] [MulSemiringAction G S] [MulSemiringAction G T]
    [SMulCommClass G A S] [SMulCommClass G A T]
    (H : Subgroup G) (M : Submonoid A)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) T]
    (hequiv : ∀ (g : G) (x : S),
      g • algebraMap S T x = algebraMap S T (g • x))
    (Q : Ideal S) [Q.IsPrime]
    (hdisjoint : Disjoint
      (Algebra.algebraMapSubmonoid S M : Set S) (Q : Set S)) :
    let F := FixedPoints.subalgebra A S H
    let F' := FixedPoints.subalgebra A T H
    letI : Algebra F F' := (fixedSubalgebraLocalizationMap H hequiv).toAlgebra
    ((Q.map (algebraMap S T)).under F').under F = Q.under F := by
  dsimp only
  let F := FixedPoints.subalgebra A S H
  let F' := FixedPoints.subalgebra A T H
  letI : Algebra F F' := (fixedSubalgebraLocalizationMap H hequiv).toAlgebra
  have hunder : (Q.map (algebraMap S T)).under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S M) T
      (inferInstance : Q.IsPrime) hdisjoint
  apply Ideal.ext
  intro x
  change ((fixedSubalgebraLocalizationMap H hequiv x : F') : T) ∈
    Q.map (algebraMap S T) ↔ (x : S) ∈ Q
  change algebraMap S T (x : S) ∈ Q.map (algebraMap S T) ↔ (x : S) ∈ Q
  exact Iff.of_eq (congrArg (fun J : Ideal S ↦ (x : S) ∈ J) hunder)

end

end HodgeConjecture.NormalizationInertia
