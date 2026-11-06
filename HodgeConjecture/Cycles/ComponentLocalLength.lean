module

public import HodgeConjecture.Cycles.FlatComponents
public import HodgeConjecture.CommutativeAlgebra.FiniteFiberLength
public import HodgeConjecture.CommutativeAlgebra.FlatLocalMultiplicity

@[expose] public section

/-!
# Actual component multiplicities in local coordinates

The minimal-prime localization of the original stalk has the same length
as the original scheme's stalk at the generic point of that component.
The defining ideal of the existing reduced component is the corresponding
minimal prime. These comparisons do not introduce a second cycle object.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace
open HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

/-- The existing reduced component ideal is its vanishing ideal. -/
theorem pointSupport_component_val {X : Scheme.{u}} (W : irreducibleComponents X) :
    (pointSupport X W.2.1.genericPoint).val =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ := by
  rw [pointSupport_val]
  congr 1
  exact Closeds.ext (genericPoints.isGenericPoint_ofComponent W)

/-- A reduced component's defining stalk ideal is exactly the associated minimal prime. -/
theorem pointSupport_component_stalk {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    IdealSheafData.stalk (pointSupport X W.1.2.1.genericPoint).val x =
      (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal := by
  rw [pointSupport_component_val]
  apply stalk_vanishingIdeal_eq_of_mem_minimalPrimes x W.1 W.2
    (irreducibleComponentsEquivMinimalPrimes x W).1
    (irreducibleComponentsEquivMinimalPrimes x W).2
  rw [fromSpecStalk_irreducibleComponentsEquivMinimalPrimes]
  exact (genericPoints.isGenericPoint_ofComponent W.1).mem

/-- The original point as a point of an existing reduced component that contains it. -/
def componentPoint {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    (pointSupport X W.1.2.1.genericPoint).val.subscheme := by
  refine ⟨x, ?_⟩
  change x ∈ closure ({W.1.2.1.genericPoint} : Set X)
  exact ((genericPoints.isGenericPoint_ofComponent W.1).specializes W.2).mem_closure

@[simp]
theorem componentPoint_image {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    (pointSupport X W.1.2.1.genericPoint).val.subschemeι.base (componentPoint x W) = x := rfl

/-- The original closed component inclusion cuts out precisely the corresponding minimal
prime in the original source stalk. -/
theorem componentPoint_stalkMap_ker {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    RingHom.ker ((pointSupport X W.1.2.1.genericPoint).val.subschemeι.stalkMap
      (componentPoint x W)).hom =
        (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal := by
  exact (IdealSheafData.ker_stalkMap_subschemeι_eq_stalk _
    (componentPoint x W)).trans (pointSupport_component_stalk x W)

/-- The minimal-prime principal quotient is the actual principal quotient in the reduced
component's local ring, preserving its length over the component ring. -/
theorem componentPoint_principal_quotient_length {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) (a : X.presheaf.stalk x) :
    Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ (Ideal.span {a} ⊔
          (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)) =
      Module.length ((pointSupport X W.1.2.1.genericPoint).val.subscheme.presheaf.stalk
        (componentPoint x W))
        (((pointSupport X W.1.2.1.genericPoint).val.subscheme.presheaf.stalk
          (componentPoint x W)) ⧸ Ideal.span
          {((pointSupport X W.1.2.1.genericPoint).val.subschemeι.stalkMap
            (componentPoint x W)).hom a}) := by
  rw [← componentPoint_stalkMap_ker x W]
  exact length_quotient_span_sup_ker _
    ((pointSupport X W.1.2.1.genericPoint).val.subschemeι.stalkMap_surjective
      (componentPoint x W)) a

/-- The multiplicity read in a minimal-prime localization is the length of the actual
source scheme's local ring at that component's generic point. -/
theorem component_localized_length {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    Module.length
        (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)
        (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal) =
      Module.length (X.presheaf.stalk (genericPoints.ofComponent W.1 : X))
        (X.presheaf.stalk (genericPoints.ofComponent W.1 : X)) := by
  let p := (irreducibleComponentsEquivMinimalPrimes x W).1
  letI := isIso_stalkMap_fromSpecStalk x p
  let e := (asIso ((X.fromSpecStalk x).stalkMap p)).commRingCatIsoToRingEquiv
  have h := length_regular_ringEquiv
    (e.trans (StructureSheaf.stalkIso (X.presheaf.stalk x) p).symm.toRingEquiv)
  rw [fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x W] at h
  exact h.symm

end

end HodgeConjecture.SchemeCycles
