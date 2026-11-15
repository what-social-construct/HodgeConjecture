module

public import HodgeConjecture.LinearAlgebra.HomCoefficients

@[expose] public noncomputable section

/-!
# Coefficient inclusion on the original functional complexes

This is literal postcomposition with the coefficient ring map, retaining
native scalar restriction. Its tensor extension is the existing evaluation
map; no alternative coefficient comparison is chosen.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

namespace HodgeConjecture.HomCoefficients

variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

def coefficientInclusion : functor k k ⟶ functor k A ⋙ ModuleCat.restrictScalars (algebraMap k A) where
  app V := ModuleCat.ofHom
    (X := (functor k k).obj V)
    (Y := (ModuleCat.restrictScalars (algebraMap k A)).obj ((functor k A).obj V))
    { toFun := fun φ ↦ (Algebra.linearMap k A).comp φ
      map_add' := (inclusion k A V.unop).map_add
      map_smul' := by
        intro r φ
        let φ' : V.unop →ₗ[k] k := φ
        apply LinearMap.ext
        intro v
        change algebraMap k A (r * φ' v) = algebraMap k A r * algebraMap k A (φ' v)
        exact map_mul _ _ _ }
  naturality V W f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    rfl

/-- The actual coefficient map on a chain complex is induced by native postcomposition. -/
def coefficientComplexMap (K : ChainComplex (ModuleCat.{0} k) ℕ) :
    dualComplex k k K ⟶
      ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (.up ℕ)).obj
        (dualComplex k A K) :=
  ((coefficientInclusion k A).mapHomologicalComplex (.up ℕ)).app K.op

end HodgeConjecture.HomCoefficients
