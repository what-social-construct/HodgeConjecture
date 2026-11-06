module

public import HodgeConjecture.SheafCohomology.LinearRestriction
public import HodgeConjecture.SheafCohomology.LinearSheaves
public import HodgeConjecture.SheafCohomology.AffineCoefficients
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono

@[expose] public section

/-!
# Fixed-ring sheaves as cohomological coefficients

Forgetting the scalar action preserves exactness of sheaves: limits are
computed on sections, and local surjectivity is unchanged. Injective
fixed-ring sheaves have surjective restrictions by the supported-section
proof, so their underlying abelian sheaves are Čech-acyclic. The affine
vanishing theorem therefore applies to this actual coefficient category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace HodgeConjecture.SheafCohomology.LinearCoefficients

variable (k : Type u) [CommRing k] (X : TopCat.{u})

/-- The actual underlying abelian sheaf, retaining all sections and restrictions. -/
def underlying : TopCat.Sheaf (ModuleCat.{u} k) X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})

instance : (underlying k X).Additive where
  map_add := by intros; rfl

instance : PreservesLimits (underlying k X) := by
  have : (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Full :=
    (fullyFaithfulSheafToPresheaf _ _).full
  have : (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Faithful :=
    (fullyFaithfulSheafToPresheaf _ _).faithful
  have : PreservesLimits (underlying k X ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
    change PreservesLimits (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k) ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}))
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

instance : (underlying k X).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    have hlocal := (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u} k) φ).2 hφ
    have : Sheaf.IsLocallySurjective ((underlying k X).map φ) :=
      ⟨fun s ↦ hlocal.imageSieve_mem s⟩
    exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((underlying k X).map φ)).1 this

instance : PreservesFiniteColimits (underlying k X) := by
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (underlying k X)
  exact (underlying k X).preservesFiniteColimits_of_preservesHomology

/-- Underlying abelian sheaves of injective fixed-ring sheaves are flasque. -/
instance underlying_isFlasque (I : TopCat.Sheaf (ModuleCat.{u} k) X) [Injective I] :
    ((underlying k X).obj I).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact Cohomology.LinearRestriction.injective_linear_restriction_surjective
      I (leOfHom i.unop)

/-- The actual fixed-ring coefficient category satisfies the injective Čech-acyclicity
condition used by affine sheaf cohomology. -/
theorem cechAcyclicInjectives :
    Cohomology.BasisCycles.CechAcyclicInjectives (underlying k X) := by
  intro I hI κ Y q
  let : Injective I := hI
  apply Cohomology.BasisCycles.cechSurj_of_uliftFamily Y
    (Cohomology.Basis.abPresheaf (underlying k X) I) q
  rw [Cohomology.BasisCycles.cechSurj_iff_isZero_homology]
  exact Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    ((underlying k X).obj I)
    (⨆ i, (Cohomology.BasisCycles.uliftFamily Y : ULift.{u} κ → Opens X) i)
    (Cohomology.BasisCycles.uliftFamily Y : ULift.{u} κ → Opens X) rfl
    (q + 1) (Nat.succ_pos q)

end HodgeConjecture.SheafCohomology.LinearCoefficients
