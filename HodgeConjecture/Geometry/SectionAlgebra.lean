module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

/-!
# Shared section algebras of a scheme over a ring

The existing structure-morphism base map, its induced algebra, and the
original section restriction homomorphisms live in the geometry layer.
Both algebraic de Rham and analytic regular evaluation use these same
objects. Extracted without changing their definitions or public names.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

/-- The actual base-ring map into sections on an open subset. -/
def sectionBaseMap (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom

/-- The base algebra on sections is induced by the original structure morphism. -/
@[instance_reducible]
def sectionAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  (sectionBaseMap k X f U).toAlgebra

theorem sectionBaseMap_restrict {U V : X.Opens} (i : U ⟶ V) (a : k) :
    X.presheaf.map i.op (sectionBaseMap k X f V a) = sectionBaseMap k X f U a := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V (by simp) ≫
    X.presheaf.map i.op) a = _
  rw [Scheme.Hom.appLE_map]
  rfl

/-- The original restriction map, preserving the structure-morphism base action. -/
def sectionMap {U V : X.Opens} (i : U ⟶ V) :
    letI := sectionAlgebra k X f V
    letI := sectionAlgebra k X f U
    Γ(X, V) →ₐ[k] Γ(X, U) := by
  letI := sectionAlgebra k X f V
  letI := sectionAlgebra k X f U
  exact { (X.presheaf.map i.op).hom with
    commutes' := sectionBaseMap_restrict k X f i }

@[simp]
theorem sectionMap_apply {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) :
    sectionMap k X f i a = X.presheaf.map i.op a := rfl

end

end HodgeConjecture.SchemeDeRham
