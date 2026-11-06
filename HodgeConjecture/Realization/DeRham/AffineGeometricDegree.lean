module

public import HodgeConjecture.Realization.DeRham.FiniteUnramifiedTrace
public import HodgeConjecture.Cycles.FiniteFlatRank

@[expose] public section

/-!
# The degree-zero de Rham trace uses the original geometric degree

For an actual finite free map of affine coordinate algebras, the algebra
trace degree agrees with Mathlib's rank of the corresponding scheme map.
The same rank was already identified with the degree used by the project's
cycle and Chow pullback. This comparison supplies the degree from geometry.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open AlgebraicGeometry

noncomputable section

universe u

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra.FormallyUnramified k A] [Algebra.FormallyUnramified k B]
  [Nontrivial A] [Module.Free A B] [Module.Finite A B]

/-- De Rham pull–trace has the geometric rank of the same affine scheme map. -/
theorem finiteTrace_finitePullback_eq_geometricRank (y : PrimeSpectrum A) (a : H0 k A) :
    finiteTrace k A B (finitePullback k A B a) =
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).finrank y • a := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  exact finiteTrace_finitePullback k A B a

/-- The de Rham identity has exactly the fiber degree used by the existing cycle maps. -/
theorem finiteTrace_finitePullback_eq_cycleDegree
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) [IsFinite f] [Flat f]
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (y : PrimeSpectrum A) (a : H0 k A) :
    finiteTrace k A B (finitePullback k A B a) = SchemeCycles.finiteFiberDegree f y • a := by
  rw [SchemeCycles.finiteFiberDegree_eq_finrank, hf]
  exact finiteTrace_finitePullback_eq_geometricRank k A B y a

end

end HodgeConjecture.AffineDeRham
