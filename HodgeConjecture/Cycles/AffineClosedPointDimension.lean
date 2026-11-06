module

public import HodgeConjecture.Cycles.NormalizationLocalDimension
public import HodgeConjecture.Cycles.SupportCodimension

@[expose] public section

/-!
# Closed-point local dimensions of finite-type affine domains

The actual structure-sheaf stalk at every closed point has the dimension
of the affine domain. Scheme-point coheight measures this local dimension;
the closed carrier's dimension is a different quantity. No normality of
the affine domain or rationality of the closed point is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

/-- The actual stalk at any maximal point has full dimension. -/
theorem affine_stalk_dimension_of_isMaximal
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk p) = ringKrullDim A := by
  change ringKrullDim ((AlgebraicGeometry.Spec.structureSheaf A).presheaf.stalk p) = _
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal,
    height_eq_trdeg_toNat_of_isMaximal k A p.asIdeal,
    ringKrullDim_eq_trdeg_toNat_of_finiteType k A]
  rfl

/-- Closedness alone supplies maximality for the actual stalk calculation. -/
theorem affine_stalk_dimension_of_isClosed
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) (hp : IsClosed ({p} : Set (PrimeSpectrum A))) :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk p) = ringKrullDim A := by
  letI := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp
  exact affine_stalk_dimension_of_isMaximal k A p

/-- Closed-point coheight in the scheme order equals the domain's finite
transcendence degree, independently of the residue field's degree over k. -/
theorem affine_closedPoint_coheight_eq_trdeg
    (k : Type u) [Field k] (A : Type v) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) (hp : IsClosed ({p} : Set (PrimeSpectrum A))) :
    Order.coheight (α := (Spec (CommRingCat.of A) : Scheme)) p =
      ((Algebra.trdeg k A).toNat : ℕ∞) := by
  apply WithBot.coe_injective
  exact (point_coheight_eq_stalkDim (Spec (CommRingCat.of A)) p).trans
    ((affine_stalk_dimension_of_isClosed k A p hp).trans
      (ringKrullDim_eq_trdeg_toNat_of_finiteType k A))

end

end HodgeConjecture.SchemeCycles
