module

public import HodgeConjecture.Realization.DeRham.AffineFormsSheaf
public import HodgeConjecture.Realization.DeRham.LaurentFormsSheaf
public import HodgeConjecture.Realization.DeRham.OpenImmersionForms
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCharts

/-!
# Actual sheaf-form sections on the projective-line atlas

The canonical sheafification unit is an isomorphism on the original
affine chart opens. Composing its inverse with the existing section-ring
form coordinates gives coordinates on actual sections of the sheafified
de Rham complex. No affine-section comparison is supplied as a premise.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite KaehlerDifferential

universe u

namespace HodgeConjecture.ProjectiveLineDeRham

variable (k : Type u) [Field k]

/-- The actual form sheaf of the original projective-line structure morphism. -/
abbrev schemeFormsSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{u} k) (projectiveLine k) :=
  SchemeDeRham.formsSheaf k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)) n

/-- The actual canonical unit on the zero-coordinate open is an isomorphism. -/
theorem zeroFormsSheafUnit_isIso (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineXOpen k))) := by
  apply SchemeDeRham.openImmersionFormsSheafUnit_range_isIso k
    (projectiveLine k ↘ Spec (.of k)) (projectiveLineXChart k) n
  rw [projectiveLineXChart_comp_structureMorphism]
  exact SchemeDeRham.affineLineFormsSheafUnit_isIso k n

/-- The actual canonical unit on the infinity-coordinate open is an isomorphism. -/
theorem infinityFormsSheafUnit_isIso (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineYOpen k))) := by
  apply SchemeDeRham.openImmersionFormsSheafUnit_range_isIso k
    (projectiveLine k ↘ Spec (.of k)) (projectiveLineYChart k) n
  rw [projectiveLineYChart_comp_structureMorphism]
  exact SchemeDeRham.affineLineFormsSheafUnit_isIso k n

/-- The actual canonical unit on the Laurent overlap open is an isomorphism. -/
theorem overlapFormsSheafUnit_isIso (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app
          (op (projectiveLineOverlapChart k).opensRange)) := by
  apply SchemeDeRham.openImmersionFormsSheafUnit_range_isIso k
    (projectiveLine k ↘ Spec (.of k)) (projectiveLineOverlapChart k) n
  rw [overlapChart_comp_structureMorphism]
  exact SchemeDeRham.laurentFormsSheafUnit_isIso k n

local instance (U : (projectiveLine k).Opens) : Algebra k Γ(projectiveLine k, U) :=
  SchemeDeRham.sectionAlgebra k (projectiveLine k)
    (projectiveLine k ↘ Spec (.of k)) U

/-- Polynomial coordinates on actual sheaf-form sections of the zero-chart open. -/
def zeroSheafFormsCoordinates (n : ℕ) :
    (schemeFormsSheaf k n).obj.obj (op (projectiveLineXOpen k)) ≅
      ModuleCat.of k (⋀[Polynomial k]^n Ω[Polynomial k⁄k]) := by
  have := zeroFormsSheafUnit_isIso k n
  exact (asIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
    (SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineXOpen k)))).symm ≪≫
    (zeroFormsCoordinates k n).toModuleIso

/-- Polynomial coordinates on actual sheaf-form sections of the infinity-chart open. -/
def infinitySheafFormsCoordinates (n : ℕ) :
    (schemeFormsSheaf k n).obj.obj (op (projectiveLineYOpen k)) ≅
      ModuleCat.of k (⋀[Polynomial k]^n Ω[Polynomial k⁄k]) := by
  have := infinityFormsSheafUnit_isIso k n
  exact (asIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
    (SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineYOpen k)))).symm ≪≫
    (infinityFormsCoordinates k n).toModuleIso

/-- Laurent coordinates on actual sheaf-form sections of the overlap open. -/
def overlapSheafFormsCoordinates (n : ℕ) :
    (schemeFormsSheaf k n).obj.obj (op (projectiveLineOverlapChart k).opensRange) ≅
      ModuleCat.of k (⋀[LaurentPolynomial k]^n Ω[LaurentPolynomial k⁄k]) := by
  have := overlapFormsSheafUnit_isIso k n
  exact (asIso ((toSheafify (Opens.grothendieckTopology (projectiveLine k))
    (SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) n)).app
        (op (projectiveLineOverlapChart k).opensRange))).symm ≪≫
    (overlapFormsCoordinates k n).toModuleIso

/-- The zero-chart sheaf coordinates retain the original canonical unit. -/
@[reassoc (attr := simp)]
theorem zeroSheafFormsCoordinates_unit (n : ℕ) :
    (toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineXOpen k)) ≫
          (zeroSheafFormsCoordinates k n).hom =
      (zeroFormsCoordinates k n).toModuleIso.hom := by
  have := zeroFormsSheafUnit_isIso k n
  simp [zeroSheafFormsCoordinates]

/-- The infinity-chart sheaf coordinates retain the original canonical unit. -/
@[reassoc (attr := simp)]
theorem infinitySheafFormsCoordinates_unit (n : ℕ) :
    (toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app (op (projectiveLineYOpen k)) ≫
          (infinitySheafFormsCoordinates k n).hom =
      (infinityFormsCoordinates k n).toModuleIso.hom := by
  have := infinityFormsSheafUnit_isIso k n
  simp [infinitySheafFormsCoordinates]

/-- The overlap sheaf coordinates retain the original canonical unit. -/
@[reassoc (attr := simp)]
theorem overlapSheafFormsCoordinates_unit (n : ℕ) :
    (toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n)).app
          (op (projectiveLineOverlapChart k).opensRange) ≫
          (overlapSheafFormsCoordinates k n).hom =
      (overlapFormsCoordinates k n).toModuleIso.hom := by
  have := overlapFormsSheafUnit_isIso k n
  simp [overlapSheafFormsCoordinates]

/-- Actual restriction of sheaf forms from the zero-chart retains the original coordinate map. -/
@[reassoc]
theorem zeroSheafFormsCoordinates_restriction (n : ℕ) :
    (schemeFormsSheaf k n).obj.map (homOfLE (overlapOpen_le_zeroOpen k)).op ≫
        (overlapSheafFormsCoordinates k n).hom =
      (zeroSheafFormsCoordinates k n).hom ≫
        ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartZeroRingMap k) n) := by
  have := zeroFormsSheafUnit_isIso k n
  let η : SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) n ⟶ (schemeFormsSheaf k n).obj :=
    toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)) n)
  let a := (homOfLE (overlapOpen_le_zeroOpen k)).op
  have : IsIso (η.app (op (projectiveLineXOpen k))) := zeroFormsSheafUnit_isIso k n
  have hzero : η.app (op (projectiveLineXOpen k)) ≫ (zeroSheafFormsCoordinates k n).hom =
      (zeroFormsCoordinates k n).toModuleIso.hom := zeroSheafFormsCoordinates_unit k n
  have hoverlap : η.app (op (projectiveLineOverlapChart k).opensRange) ≫
      (overlapSheafFormsCoordinates k n).hom = (overlapFormsCoordinates k n).toModuleIso.hom :=
    overlapSheafFormsCoordinates_unit k n
  apply (cancel_epi (η.app (op (projectiveLineXOpen k)))).mp
  calc
    η.app (op (projectiveLineXOpen k)) ≫ (schemeFormsSheaf k n).obj.map a ≫
        (overlapSheafFormsCoordinates k n).hom =
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n).map a ≫
        η.app (op (projectiveLineOverlapChart k).opensRange) ≫
        (overlapSheafFormsCoordinates k n).hom := by
          simpa only [Category.assoc] using congrArg
            (fun g ↦ g ≫ (overlapSheafFormsCoordinates k n).hom) (η.naturality a).symm
    _ = (SchemeDeRham.formsPresheaf k (projectiveLine k)
          (projectiveLine k ↘ Spec (.of k)) n).map a ≫
          (overlapFormsCoordinates k n).toModuleIso.hom := by
            exact congrArg (fun g ↦ (SchemeDeRham.formsPresheaf k (projectiveLine k)
              (projectiveLine k ↘ Spec (.of k)) n).map a ≫ g) hoverlap
    _ = (zeroFormsCoordinates k n).toModuleIso.hom ≫
          ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartZeroRingMap k) n) := by
            apply ModuleCat.hom_ext
            exact LinearMap.ext (zeroFormsCoordinates_restriction k n)
    _ = η.app (op (projectiveLineXOpen k)) ≫ (zeroSheafFormsCoordinates k n).hom ≫
          ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartZeroRingMap k) n) := by
            simpa only [Category.assoc] using congrArg
              (fun g ↦ g ≫ ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartZeroRingMap k) n))
              hzero.symm

/-- Actual restriction of sheaf forms from the infinity-chart retains coordinate inversion. -/
@[reassoc]
theorem infinitySheafFormsCoordinates_restriction (n : ℕ) :
    (schemeFormsSheaf k n).obj.map (homOfLE (overlapOpen_le_infinityOpen k)).op ≫
        (overlapSheafFormsCoordinates k n).hom =
      (infinitySheafFormsCoordinates k n).hom ≫
        ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartInfinityRingMap k) n) := by
  have := infinityFormsSheafUnit_isIso k n
  let η : SchemeDeRham.formsPresheaf k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) n ⟶ (schemeFormsSheaf k n).obj :=
    toSheafify (Opens.grothendieckTopology (projectiveLine k))
      (SchemeDeRham.formsPresheaf k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)) n)
  let a := (homOfLE (overlapOpen_le_infinityOpen k)).op
  have : IsIso (η.app (op (projectiveLineYOpen k))) := infinityFormsSheafUnit_isIso k n
  have hinfinity : η.app (op (projectiveLineYOpen k)) ≫ (infinitySheafFormsCoordinates k n).hom =
      (infinityFormsCoordinates k n).toModuleIso.hom := infinitySheafFormsCoordinates_unit k n
  have hoverlap : η.app (op (projectiveLineOverlapChart k).opensRange) ≫
      (overlapSheafFormsCoordinates k n).hom = (overlapFormsCoordinates k n).toModuleIso.hom :=
    overlapSheafFormsCoordinates_unit k n
  apply (cancel_epi (η.app (op (projectiveLineYOpen k)))).mp
  calc
    η.app (op (projectiveLineYOpen k)) ≫ (schemeFormsSheaf k n).obj.map a ≫
        (overlapSheafFormsCoordinates k n).hom =
      (SchemeDeRham.formsPresheaf k (projectiveLine k)
        (projectiveLine k ↘ Spec (.of k)) n).map a ≫
        η.app (op (projectiveLineOverlapChart k).opensRange) ≫
        (overlapSheafFormsCoordinates k n).hom := by
          simpa only [Category.assoc] using congrArg
            (fun g ↦ g ≫ (overlapSheafFormsCoordinates k n).hom) (η.naturality a).symm
    _ = (SchemeDeRham.formsPresheaf k (projectiveLine k)
          (projectiveLine k ↘ Spec (.of k)) n).map a ≫
          (overlapFormsCoordinates k n).toModuleIso.hom := by
            exact congrArg (fun g ↦ (SchemeDeRham.formsPresheaf k (projectiveLine k)
              (projectiveLine k ↘ Spec (.of k)) n).map a ≫ g) hoverlap
    _ = (infinityFormsCoordinates k n).toModuleIso.hom ≫
          ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartInfinityRingMap k) n) := by
            apply ModuleCat.hom_ext
            exact LinearMap.ext (infinityFormsCoordinates_restriction k n)
    _ = η.app (op (projectiveLineYOpen k)) ≫ (infinitySheafFormsCoordinates k n).hom ≫
          ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartInfinityRingMap k) n) := by
            simpa only [Category.assoc] using congrArg
              (fun g ↦ g ≫ ModuleCat.ofHom (AlgebraDeRham.formsMap k (chartInfinityRingMap k) n))
              hinfinity.symm

end HodgeConjecture.ProjectiveLineDeRham
