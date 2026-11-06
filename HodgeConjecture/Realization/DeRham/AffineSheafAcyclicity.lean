module

public import HodgeConjecture.SheafCohomology.LocalAffineCoefficients
public import HodgeConjecture.SheafCohomology.StructureModule
public import HodgeConjecture.SheafCohomology.LinearCoefficients
public import HodgeConjecture.SheafCohomology.TwoOpenModules
public import HodgeConjecture.Realization.DeRham.SheafHypercohomology

@[expose] public section

/-!
# Actual fixed-ring cohomology from local regular-function coordinates

The localized affine criterion computes cohomology in the original sheaf
category. Exact forgetting of module scalars commutes with that same
right-derived sections functor, so vanishing is reflected back to its
actual module-valued cohomology.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace HodgeConjecture.SchemeDeRham

open SheafCohomology

noncomputable section

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u})

/-- Coefficient forgetting with the unbundled-site target category fixed explicitly. -/
def underlyingAbelian : TopCat.Sheaf (ModuleCat.{u} k) X ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  LinearCoefficients.underlying k X

instance : (underlyingAbelian k X).Additive where
  map_add := by intros; rfl

instance : PreservesLimits (underlyingAbelian k X) :=
  inferInstanceAs (PreservesLimits (LinearCoefficients.underlying k X))

instance : PreservesFiniteColimits (underlyingAbelian k X) :=
  inferInstanceAs (PreservesFiniteColimits (LinearCoefficients.underlying k X))

/-- Its injective coefficients have the already proved Čech-acyclic underlying sheaves. -/
theorem underlyingAbelian_cechAcyclicInjectives :
    Cohomology.BasisCycles.CechAcyclicInjectives (underlyingAbelian k X) :=
  LinearCoefficients.cechAcyclicInjectives k X

/-- Exact coefficient forgetting identifies the two ordinary derived-section objects. -/
def moduleCohomologyForgetIso (M : TopCat.Sheaf (ModuleCat.{u} k) X)
    (U : X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj
        (TwoOpenModules.Hobj k (𝟭 _) U n M) ≅
      Cohomology.Basis.Hobj (underlyingAbelian k X) U n M :=
  BoundedBelowDerived.rightDerivedPostcomposeIso
    (TwoOpenModules.secFunctor k (𝟭 _) U)
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) M n

/-- Local regular-function coordinates imply actual affine cohomology vanishing. -/
theorem isZero_moduleCohomology_of_localFunctions
    (M : TopCat.Sheaf (ModuleCat.{u} k) X) (U : X.Opens) (hU : IsAffineOpen U)
    (e : ∀ (V : X.Opens), V ≤ U → M.obj.obj (op V) ≃+ Γ(X, V))
    (he : ∀ {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U)
      (s : M.obj.obj (op W)),
      e V (hVW.trans hWU) (M.obj.map (homOfLE hVW).op s) =
        X.presheaf.map (homOfLE hVW).op (e W hWU s))
    (n : ℕ) (hn : 0 < n) : IsZero (TwoOpenModules.Hobj k (𝟭 _) U n M) := by
  have hAb : IsZero (Cohomology.Basis.Hobj (underlyingAbelian k X) U n M) :=
    isZero_coefficientCohomology_of_localAffineEquiv X (underlyingAbelian k X)
      (underlyingAbelian_cechAcyclicInjectives k X) M (structureModule X) U hU e he n hn
  have hz := hAb.of_iso (moduleCohomologyForgetIso k X M U n)
  rw [IsZero.iff_id_eq_zero]
  apply (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map_injective
  exact ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map_id _).trans
    (hz.eq_of_src _ _)

variable (f : X ⟶ Spec (.of k))

/-- The actual zero-form sheaf is the regular-function presheaf on all opens. -/
def zeroFormsSheafIsoFunctions :
    (formsSheaf k X f 0).obj ≅ functionsPresheaf k X f := by
  have : IsIso (toSheafify (Opens.grothendieckTopology X) (formsPresheaf k X f 0)) :=
    CategoryTheory.isIso_toSheafify _ (zeroFormsPresheaf_isSheaf k X f)
  exact (asIso (toSheafify (Opens.grothendieckTopology X)
    (formsPresheaf k X f 0))).symm ≪≫ zeroFormsIsoFunctions k X f

/-- Degree-zero forms are acyclic on every actual affine open of the scheme. -/
theorem isZero_zeroFormsCohomology (U : X.Opens) (hU : IsAffineOpen U)
    (n : ℕ) (hn : 0 < n) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) U n (formsSheaf k X f 0)) := by
  apply isZero_moduleCohomology_of_localFunctions k X _ U hU
    (fun V _ => ((zeroFormsSheafIsoFunctions k X f).app (op V)).toLinearEquiv.toAddEquiv)
    (fun {V W} hVW _hWU s => ?_) n hn
  exact congrArg (fun g => g s)
    ((zeroFormsSheafIsoFunctions k X f).hom.naturality (homOfLE hVW).op)

end

end HodgeConjecture.SchemeDeRham
