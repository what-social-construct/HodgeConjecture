module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Topological codimension and local dimension

The codimension of an irreducible closed support is its coheight in the
inclusion order on irreducible closed subsets: the supremum of lengths of
chains of irreducible closed supersets. For any scheme, this equals the
Krull dimension of the stalk at its generic point.

The proof passes through the specialization order, restricts to an affine
neighbourhood without changing the generizations, and applies the height
formula for a localization at a prime. No integral or Noetherian hypothesis
is imposed on the ambient scheme.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- A scheme's specialization order is the inclusion order on actual
irreducible closed point closures. -/
def pointClosureOrderIso (X : Scheme.{u}) : X ≃o IrreducibleCloseds X :=
  irreducibleSetEquivPoints.symm

@[simp]
theorem pointClosureOrderIso_coe (X : Scheme.{u}) (x : X) :
    ((pointClosureOrderIso X x : IrreducibleCloseds X) : Set X) = closure {x} := rfl

/-- Topological codimension of a point closure is its specialization coheight. -/
theorem pointClosure_coheight (X : Scheme.{u}) (x : X) :
    Order.coheight (pointClosureOrderIso X x) = Order.coheight x :=
  Order.coheight_orderIso (pointClosureOrderIso X) x

private def openGenerizationOrderIso (X : Scheme.{u}) (U : X.Opens) (x : U) :
    Set.Ici x ≃o Set.Ici (x.val : X) where
  toFun y := ⟨y.val.val, y.property⟩
  invFun y := ⟨⟨y.val, (Scheme.le_iff_specializes.mp y.property).mem_open U.isOpen x.property⟩,
    y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem open_coheight (X : Scheme.{u}) (U : X.Opens) (x : U) :
    (Order.coheight x : WithBot ℕ∞) = (Order.coheight (x.val : X) : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_eq_of_orderIso (openGenerizationOrderIso X U x)

private def affinePointOrderIso (X : Scheme.{u}) {U : X.Opens} (hU : IsAffineOpen U) :
    { x : X // x ∈ U } ≃o (PrimeSpectrum Γ(X, U))ᵒᵈ where
  toEquiv := (Scheme.homeoOfIso hU.isoSpec).toEquiv
  map_rel_iff' {x y} := by
    change hU.primeIdealOf y ≤ hU.primeIdealOf x ↔ (x.val : X) ≤ y.val
    rw [PrimeSpectrum.le_iff_specializes]
    exact (Scheme.homeoOfIso hU.isoSpec).isInducing.specializes_iff.trans
      (subtype_specializes_iff y x)

/-- The coheight of a scheme point is the dimension of its actual local ring. -/
theorem point_coheight_eq_stalkDim (X : Scheme.{u}) (x : X) :
    (Order.coheight x : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
  let y : U := ⟨x, hxU⟩
  letI := X.presheaf.algebra_section_stalk y
  letI := hU.isLocalization_stalk y
  change (Order.coheight y.val : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk y.val)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal,
    PrimeSpectrum.height_eq_orderHeight]
  have h := Order.coheight_orderIso (affinePointOrderIso X hU) y
  have h' : Order.coheight y = Order.height (hU.primeIdealOf y) := h.symm
  rw [← open_coheight X U y, h']

/-- Codimension by chains of irreducible closed supersets equals local
dimension at the actual generic point of that support. -/
theorem support_coheight_eq_stalkDim (X : Scheme.{u}) (Z : IrreducibleCloseds X)
    (x : X) (hx : IsGenericPoint x (Z : Set X)) :
    (Order.coheight Z : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  have hZ : Z = pointClosureOrderIso X x := by
    apply IrreducibleCloseds.ext
    rw [pointClosureOrderIso_coe]
    exact hx.symm
  rw [hZ, pointClosure_coheight]
  exact point_coheight_eq_stalkDim X x

end

end HodgeConjecture.SchemeCycles
