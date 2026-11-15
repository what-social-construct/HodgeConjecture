module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriers
public import HodgeConjecture.Cycles.ProjectiveLineCycleDegree
public import HodgeConjecture.Cycles.PrincipalRelations
public import HodgeConjecture.Cycles.RationalChow

/-!
# Homogeneous zero-coordinate cycles on P¹ × P¹

The two scheme-theoretic zero fibers are integral carriers isomorphic to
`P¹`. The field-induced dimension function places their fundamental cycles
in degree one of the existing cycle module. Their images in the existing
ordinary Chow quotient are the coordinate-fiber classes.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductChow

open AlgebraicGeometry CategoryTheory SchemeCycles

universe u

variable (k : Type u) [Field k]

/-- The actual product structure morphism is locally of finite type over the field. -/
instance product_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveLineProductStructureMorphism k) := by
  unfold projectiveLineProductStructureMorphism
  infer_instance

/-- The product is Noetherian, so its existing ordinary Chow quotients are available. -/
instance product_isNoetherian : IsNoetherian (projectiveLineProduct k) where
  toIsLocallyNoetherian := by infer_instance
  toCompactSpace := by infer_instance

/-- The existing global field-induced dimension function on the actual product. -/
def dimensionFunction : DimensionFunction (projectiveLineProduct k) :=
  DimensionFunction.ofLocallyOfFiniteType k (projectiveLineProduct k)
    (projectiveLineProductStructureMorphism k)

/-- The first zero fiber's actual carrier has dimension one in the existing grading. -/
theorem firstCarrier_supportDegree_one :
    supportDegree (dimensionFunction k) (projectiveLineProductZeroFirstCarrier k) = 1 := by
  apply (supportDegree_ofLocallyOfFiniteType_eq_iff k (projectiveLineProduct k)
    (projectiveLineProductStructureMorphism k)
    (projectiveLineProductZeroFirstCarrier k) 1).2
  have h := IsHomeomorph.topologicalKrullDim_eq
    (projectiveLineProductZeroFirstCarrierIso k).hom.base
    (projectiveLineProductZeroFirstCarrierIso k).hom.homeomorph.isHomeomorph
  rw [topologicalKrullDim_projectiveLine] at h
  exact_mod_cast h.symm

/-- The second zero fiber's actual carrier has dimension one in the existing grading. -/
theorem secondCarrier_supportDegree_one :
    supportDegree (dimensionFunction k) (projectiveLineProductZeroSecondCarrier k) = 1 := by
  apply (supportDegree_ofLocallyOfFiniteType_eq_iff k (projectiveLineProduct k)
    (projectiveLineProductStructureMorphism k)
    (projectiveLineProductZeroSecondCarrier k) 1).2
  have h := IsHomeomorph.topologicalKrullDim_eq
    (projectiveLineProductZeroSecondCarrierIso k).hom.base
    (projectiveLineProductZeroSecondCarrierIso k).hom.homeomorph.isHomeomorph
  rw [topologicalKrullDim_projectiveLine] at h
  exact_mod_cast h.symm

/-- The first coordinate fiber as a homogeneous integral cycle. -/
def firstZeroCycle : cyclesOfDegree ℤ (dimensionFunction k) 1 :=
  ⟨fundamentalCycle ℤ (projectiveLineProductZeroFirstCarrier k),
    fundamentalCycle_mem_cyclesOfDegree ℤ (dimensionFunction k) 1
      (projectiveLineProductZeroFirstCarrier k) (firstCarrier_supportDegree_one k)⟩

/-- The second coordinate fiber as a homogeneous integral cycle. -/
def secondZeroCycle : cyclesOfDegree ℤ (dimensionFunction k) 1 :=
  ⟨fundamentalCycle ℤ (projectiveLineProductZeroSecondCarrier k),
    fundamentalCycle_mem_cyclesOfDegree ℤ (dimensionFunction k) 1
      (projectiveLineProductZeroSecondCarrier k) (secondCarrier_supportDegree_one k)⟩

/-- The first coordinate-fiber class in the actual degree-one Chow quotient. -/
def firstZeroChowClass : ChowGroup (dimensionFunction k) 1 :=
  classMap (dimensionFunction k) 1 (firstZeroCycle k)

/-- The second coordinate-fiber class in the actual degree-one Chow quotient. -/
def secondZeroChowClass : ChowGroup (dimensionFunction k) 1 :=
  classMap (dimensionFunction k) 1 (secondZeroCycle k)

/-- Rationalization of the first actual coordinate-fiber Chow class. -/
def firstZeroRationalChowClass : RationalChowGroup (dimensionFunction k) 1 :=
  chowRationalize (dimensionFunction k) 1 (firstZeroChowClass k)

/-- Rationalization of the second actual coordinate-fiber Chow class. -/
def secondZeroRationalChowClass : RationalChowGroup (dimensionFunction k) 1 :=
  chowRationalize (dimensionFunction k) 1 (secondZeroChowClass k)

end HodgeConjecture.ProjectiveLineProductChow

end
