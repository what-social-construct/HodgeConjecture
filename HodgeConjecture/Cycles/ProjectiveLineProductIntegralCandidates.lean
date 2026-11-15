module

public import HodgeConjecture.Cycles.ProjectiveLineProductFibers
public import HodgeConjecture.Geometry.ProjectiveLineProductSections
public import HodgeConjecture.Geometry.ProjectiveLineProperties

@[expose] public section

/-!
# Integral supports in coordinate fibers of P¹ × P¹

The zero section paired with the generic point of the other projective line
gives a point of the product. Its reduced closure is an actual integral
closed subscheme, and its support lies in the corresponding closed fiber.
The free projection takes its generic point to the generic point of P¹.
Equality with the whole scheme-theoretic fiber and codimension one remain
separate geometric questions.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineProductIntegralCandidates

open AlgebraicGeometry CategoryTheory TopologicalSpace SchemeCycles
open ProjectiveLineProductFibers

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The zero section evaluated at the image of the generic point of P¹. -/
def zeroSectionPoint : projectiveLine k :=
  (projectiveLineZeroSection k).base
    ((projectiveLine k ↘ Spec (.of k)).base (genericPoint (projectiveLine k)))

/-- The reduced closure of the generic point in the first coordinate fiber. -/
def firstZeroCarrier : IntegralClosedSubscheme (projectiveLineProduct k) :=
  pointSupport (projectiveLineProduct k)
    ((projectiveLineProductZeroFirst k).base (genericPoint (projectiveLine k)))

/-- The reduced closure of the generic point in the second coordinate fiber. -/
def secondZeroCarrier : IntegralClosedSubscheme (projectiveLineProduct k) :=
  pointSupport (projectiveLineProduct k)
    ((projectiveLineProductZeroSecond k).base (genericPoint (projectiveLine k)))

/-- The free second coordinate maps the first carrier's generic point to the
generic point of P¹. -/
@[simp] theorem firstZeroCarrier_generic_snd :
    (projectiveLineProductSnd k).base (ambientGenericPoint (firstZeroCarrier k)) =
      genericPoint (projectiveLine k) := by
  rw [firstZeroCarrier, ambientGenericPoint_pointSupport]
  change ((projectiveLineProductZeroFirst k ≫ projectiveLineProductSnd k).base
    (genericPoint (projectiveLine k))) = _
  rw [projectiveLineProductZeroFirst_snd]
  rfl

/-- The free first coordinate maps the second carrier's generic point to the
generic point of P¹. -/
@[simp] theorem secondZeroCarrier_generic_fst :
    (projectiveLineProductFst k).base (ambientGenericPoint (secondZeroCarrier k)) =
      genericPoint (projectiveLine k) := by
  rw [secondZeroCarrier, ambientGenericPoint_pointSupport]
  change ((projectiveLineProductZeroSecond k ≫ projectiveLineProductFst k).base
    (genericPoint (projectiveLine k))) = _
  rw [projectiveLineProductZeroSecond_fst]
  rfl

/-- The distinguished generic point of the first carrier lies in the
scheme-theoretic first zero fiber. -/
theorem firstZeroCarrier_generic_mem_fiber :
    ambientGenericPoint (firstZeroCarrier k) ∈
      (firstFiberIdeal k (zeroSectionPoint k)).support := by
  rw [firstZeroCarrier, ambientGenericPoint_pointSupport,
    mem_firstFiber_support]
  change ((projectiveLineProductZeroFirst k ≫ projectiveLineProductFst k).base
    (genericPoint (projectiveLine k))) ∈ closure ({zeroSectionPoint k} : Set _)
  rw [projectiveLineProductZeroFirst_fst]
  exact subset_closure (Set.mem_singleton _)

/-- The distinguished generic point of the second carrier lies in the
scheme-theoretic second zero fiber. -/
theorem secondZeroCarrier_generic_mem_fiber :
    ambientGenericPoint (secondZeroCarrier k) ∈
      (secondFiberIdeal k (zeroSectionPoint k)).support := by
  rw [secondZeroCarrier, ambientGenericPoint_pointSupport,
    mem_secondFiber_support]
  change ((projectiveLineProductZeroSecond k ≫ projectiveLineProductSnd k).base
    (genericPoint (projectiveLine k))) ∈ closure ({zeroSectionPoint k} : Set _)
  rw [projectiveLineProductZeroSecond_snd]
  exact subset_closure (Set.mem_singleton _)

/-- The first integral carrier's entire reduced closure is supported in
the actual first zero fiber. -/
theorem firstZeroCarrier_support_le_fiber :
    (firstZeroCarrier k).val.support ≤
      (firstFiberIdeal k (zeroSectionPoint k)).support := by
  rw [firstZeroCarrier, pointSupport_support, Closeds.closure_le]
  have h := firstZeroCarrier_generic_mem_fiber k
  rw [firstZeroCarrier, ambientGenericPoint_pointSupport] at h
  simpa using h

/-- The second integral carrier's entire reduced closure is supported in
the actual second zero fiber. -/
theorem secondZeroCarrier_support_le_fiber :
    (secondZeroCarrier k).val.support ≤
      (secondFiberIdeal k (zeroSectionPoint k)).support := by
  rw [secondZeroCarrier, pointSupport_support, Closeds.closure_le]
  have h := secondZeroCarrier_generic_mem_fiber k
  rw [secondZeroCarrier, ambientGenericPoint_pointSupport] at h
  simpa using h

end

end HodgeConjecture.ProjectiveLineProductIntegralCandidates
