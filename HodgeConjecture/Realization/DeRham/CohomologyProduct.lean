module

public import HodgeConjecture.Realization.DeRham.AffineCohomology
public import HodgeConjecture.CommutativeAlgebra.DeRham.WedgeProduct
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

/-!
# Genuine positive-degree cup product on affine de Rham cohomology

The actual wedge product of two closed one-forms is closed. If either
factor is exact, the original differential gives an explicit primitive
for the product. Descending these two proved identities through the
existing closed/exact quotients constructs H¹ × H¹ → H². The product
retains its actual wedge representatives and is alternating in every
characteristic. No intersection or analytic comparison is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open KaehlerDifferential

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The actual wedge of closed one-forms, bilinear over the structural base. -/
def closedOneWedge : closedForms k A 1 →ₗ[k] closedForms k A 1 →ₗ[k] closedForms k A 2 :=
  LinearMap.mk₂ k
    (fun ω η ↦ ⟨exteriorPower.wedgeMul 1 1 ω.val η.val,
      deRhamDifferential_wedgeMul_eq_zero_of_closed 1 1 ω.val η.val ω.property η.property⟩)
    (fun ω₁ ω₂ η ↦ Subtype.ext (by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun c ω η ↦ Subtype.ext (by
      change exteriorPower.wedgeMul 1 1 (c • ω.val) η.val =
        c • exteriorPower.wedgeMul 1 1 ω.val η.val
      rw [← algebraMap_smul A c ω.val, map_smul, LinearMap.smul_apply, algebraMap_smul]))
    (fun ω η₁ η₂ ↦ Subtype.ext (by simp only [Submodule.coe_add, map_add]))
    (fun c ω η ↦ Subtype.ext (by
      change exteriorPower.wedgeMul 1 1 ω.val (c • η.val) =
        c • exteriorPower.wedgeMul 1 1 ω.val η.val
      rw [← algebraMap_smul A c η.val, map_smul, algebraMap_smul]))

@[simp]
theorem closedOneWedge_val (ω η : closedForms k A 1) :
    (closedOneWedge k A ω η).val = exteriorPower.wedgeMul 1 1 ω.val η.val := rfl

/-- Exactness on the left has an actual degree-one primitive ω₀ ∧ η₁. -/
theorem closedOneWedge_exact_left (ω η : closedForms k A 1)
    (hω : ω ∈ exactForms k A 1) : closedOneWedge k A ω η ∈ exactForms k A 2 := by
  rw [exactForms_succ] at hω ⊢
  obtain ⟨ξ, hξ⟩ := hω
  refine ⟨exteriorPower.wedgeMul 0 1 ξ η.val, ?_⟩
  apply Subtype.ext
  have hξ' : deRhamDifferential (A := k) 0 ξ = ω.val := congrArg Subtype.val hξ
  have h := deRhamDifferential_wedgeMul_of_right_closed
    (A := k) 0 1 ξ η.val η.property
  rw [hξ'] at h
  exact h

/-- Exactness on the right has the actual primitive −ω₁ ∧ η₀. -/
theorem closedOneWedge_exact_right (ω η : closedForms k A 1)
    (hη : η ∈ exactForms k A 1) : closedOneWedge k A ω η ∈ exactForms k A 2 := by
  rw [exactForms_succ] at hη ⊢
  obtain ⟨ξ, hξ⟩ := hη
  refine ⟨-exteriorPower.wedgeMul 1 0 ω.val ξ, ?_⟩
  apply Subtype.ext
  have hξ' : deRhamDifferential (A := k) 0 ξ = η.val := congrArg Subtype.val hξ
  have h := deRhamDifferential_wedgeMul_of_left_closed
    (A := k) 1 0 ω.val ξ ω.property
  change deRhamDifferential (A := k) 1 (-exteriorPower.wedgeMul 1 0 ω.val ξ) =
    exteriorPower.wedgeMul 1 1 ω.val η.val
  rw [map_neg, h, hξ']
  rw [pow_one]
  exact (congrArg Neg.neg (neg_one_smul A
    (exteriorPower.wedgeMul 1 1 ω.val η.val))).trans (neg_neg _)

/-- Actual closed wedge followed by the actual degree-two quotient map. -/
def closedOneWedgeClass :
    closedForms k A 1 →ₗ[k] closedForms k A 1 →ₗ[k] Cohomology k A 2 :=
  (closedOneWedge k A).compr₂ (cohomologyClass k A 2)

/-- Left exact forms are killed by the bilinear class map, proved through actual primitives. -/
theorem exactForms_le_ker_closedOneWedgeClass :
    exactForms k A 1 ≤ LinearMap.ker (closedOneWedgeClass k A) := by
  intro ω hω
  apply LinearMap.ext
  intro η
  exact (cohomologyClass_eq_zero_iff k A 2 _).mpr
    (closedOneWedge_exact_left k A ω η hω)

/-- Right exact forms are killed independently. -/
theorem exactForms_le_ker_closedOneWedgeClass_flip :
    exactForms k A 1 ≤ LinearMap.ker (closedOneWedgeClass k A).flip := by
  intro η hη
  apply LinearMap.ext
  intro ω
  exact (cohomologyClass_eq_zero_iff k A 2 _).mpr
    (closedOneWedge_exact_right k A ω η hη)

/-- The bilinear cup product of genuine degree-one affine de Rham classes. -/
def cupOne : Cohomology k A 1 →ₗ[k] Cohomology k A 1 →ₗ[k] Cohomology k A 2 :=
  LinearMap.liftQ₂ (exactForms k A 1) (exactForms k A 1) (closedOneWedgeClass k A)
    (exactForms_le_ker_closedOneWedgeClass k A)
    (exactForms_le_ker_closedOneWedgeClass_flip k A)

/-- The quotient cup product retains its original actual wedge representatives. -/
@[simp]
theorem cupOne_class_class (ω η : closedForms k A 1) :
    cupOne k A (cohomologyClass k A 1 ω) (cohomologyClass k A 1 η) =
      cohomologyClass k A 2 (closedOneWedge k A ω η) := rfl

theorem closedOneWedge_swap (ω η : closedForms k A 1) :
    closedOneWedge k A ω η = -closedOneWedge k A η ω := by
  apply Subtype.ext
  apply Subtype.ext
  simpa using exteriorPower.coe_wedgeMul_comm 1 1 ω.val η.val

@[simp]
theorem closedOneWedge_self (ω : closedForms k A 1) : closedOneWedge k A ω ω = 0 :=
  Subtype.ext (exteriorPower.wedgeMul_one_self ω.val)

/-- Alternation survives the actual exact-form quotient, without assuming characteristic zero. -/
@[simp]
theorem cupOne_self (α : Cohomology k A 1) : cupOne k A α α = 0 := by
  obtain ⟨ω, rfl⟩ := cohomologyClass_surjective k A 1 α
  rw [cupOne_class_class, closedOneWedge_self, map_zero]

theorem cupOne_swap (α β : Cohomology k A 1) : cupOne k A α β = -cupOne k A β α := by
  obtain ⟨ω, rfl⟩ := cohomologyClass_surjective k A 1 α
  obtain ⟨η, rfl⟩ := cohomologyClass_surjective k A 1 β
  rw [cupOne_class_class, cupOne_class_class, closedOneWedge_swap, map_neg]

end

end HodgeConjecture.AffineDeRham
