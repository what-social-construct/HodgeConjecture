module

public import HodgeConjecture.Realization.DeRham.HypercohomologyFiltration

@[expose] public section

/-!
# The actual degree-induced Hodge filtration on scheme de Rham cohomology

The original sheaf de Rham complex is restricted to form degrees at least
`p` and extended by zero below. Its original inclusion induces a map on
actual derived global sections. The Hodge filtration is the linear image
of that map. Integer indices at most zero retain the whole nonnegative
complex. No spectral-sequence degeneration is assumed or asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SchemeDeRham

open CategoryTheory AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

attribute [local instance] HasDerivedCategory.standard

/-- The original differential-form complex retaining only form degrees at least `p`. -/
def hodgeFiltrationComplex (p : ℤ) : CochainComplex (TopCat.Sheaf (ModuleCat.{u} k) X) ℕ :=
  DegreeFiltration.complex (sheafComplex k X f) p.toNat

/-- The original inclusion of that actual degree subcomplex into the actual sheaf de Rham complex. -/
def hodgeFiltrationInclusion (p : ℤ) : hodgeFiltrationComplex k X f p ⟶ sheafComplex k X f :=
  DegreeFiltration.inclusion (sheafComplex k X f) p.toNat

/-- The actual induced derived-global-sections map in cohomological degree `n`. -/
def hodgeFiltrationMap (n p : ℤ) :
    SheafHypercohomology.hypercohomology k X (hodgeFiltrationComplex k X f p) n ⟶
      hypercohomology k X f n :=
  SheafHypercohomology.hypercohomologyMap k X (hodgeFiltrationInclusion k X f p) n

/-- Hodge filtration as the actual linear range of the original derived inclusion map. -/
def hodgeFiltration (n p : ℤ) : Submodule k (hypercohomology k X f n) :=
  LinearMap.range (hodgeFiltrationMap k X f n p).hom

theorem mem_hodgeFiltration (n p : ℤ) (z : hypercohomology k X f n) :
    z ∈ hodgeFiltration k X f n p ↔
      ∃ x, hodgeFiltrationMap k X f n p x = z := Iff.rfl

/-- The generic image calculation uses exactly the original sheaf hypercohomology map. -/
theorem hodgeFiltration_eq_generic (n p : ℤ) :
    hodgeFiltration k X f n p =
      HypercohomologyFiltration.filtration (SheafHypercohomology.globalSections k X)
        (sheafComplex k X f) n p.toNat := rfl

/-- Original transitions between the degree subcomplexes give a decreasing filtration. -/
theorem hodgeFiltration_antitone (n : ℤ) : Antitone (hodgeFiltration k X f n) := by
  intro p q hpq
  rw [hodgeFiltration_eq_generic, hodgeFiltration_eq_generic]
  exact HypercohomologyFiltration.filtration_antitone _ _ n (Int.toNat_le_toNat hpq)

/-- Nonpositive Hodge indices retain the entire original nonnegative complex. -/
theorem hodgeFiltration_eq_top_of_nonpos (n p : ℤ) (hp : p ≤ 0) :
    hodgeFiltration k X f n p = ⊤ := by
  rw [hodgeFiltration_eq_generic, Int.toNat_eq_zero.mpr hp]
  exact HypercohomologyFiltration.filtration_zero _ _ n

end HodgeConjecture.SchemeDeRham
