module

public import HodgeConjecture.Cycles.FinitePushforwardResidue
public import HodgeConjecture.Cycles.GradedFinitePushforward
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

/-!
# Composition of the existing finite cycle pushforward

The actual residue-field maps form a scalar tower. Its degree formula,
together with composition of the original scheme-theoretic images, proves
functoriality of the existing degree-weighted cycle maps. Restriction to
compatible homogeneous submodules keeps the same underlying map.

This is the finite-morphism case of Stacks 02R5:
https://stacks.math.columbia.edu/tag/02R5
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/-- The original residue-field maps give the degree tower law. This equality
also holds for the `finrank` convention on infinite extensions. -/
theorem residueFieldDegree_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    residueFieldDegree (f ≫ g) x =
      residueFieldDegree f x * residueFieldDegree g (f.base x) := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x)) :=
    (g.residueFieldMap (f.base x)).hom.toAlgebra
  letI : Algebra (Z.residueField (g.base (f.base x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower (Z.residueField (g.base (f.base x)))
      (Y.residueField (f.base x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x))
  exact (Module.finrank_mul_finrank
    (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x))
    (X.residueField x)).symm.trans (Nat.mul_comm _ _)

/-- The actual integral scheme-theoretic images compose. -/
@[simp]
theorem imageSubscheme_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : IntegralClosedSubscheme X) :
    imageSubscheme g (imageSubscheme f W) = imageSubscheme (f ≫ g) W := by
  apply Subtype.ext
  simp only [imageSubscheme_val, Scheme.IdealSheafData.map_comp]

/-- The existing finite support-to-image weights multiply in a composite. -/
theorem finitePushforwardDegree_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g]
    (W : IntegralClosedSubscheme X) :
    finitePushforwardDegree (f ≫ g) W =
      finitePushforwardDegree f W * finitePushforwardDegree g (imageSubscheme f W) := by
  simp only [finitePushforwardDegree_eq_residueFieldDegree,
    ambientGenericPoint_imageSubscheme, residueFieldDegree_comp]

/-- Finite pushforward is covariantly functorial on the original finite cycles,
over any coefficient semiring. No field-base or ambient integrality is needed. -/
theorem finitePushforward_comp (R : Type v) [Semiring R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g] :
    (finitePushforward R g).comp (finitePushforward R f) =
      finitePushforward R (f ≫ g) := by
  apply Finsupp.lhom_ext
  intro W r
  simp only [LinearMap.comp_apply, finitePushforward_single, map_smul,
    map_nsmul, finitePushforward_fundamentalCycle, imageSubscheme_comp,
    finitePushforwardDegree_comp, mul_smul]

/-- Identity finite pushforward restricts to identity on homogeneous cycles. -/
theorem gradedFinitePushforward_id (R : Type v) [Semiring R]
    (X : Scheme.{u}) (δ : DimensionFunction X)
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δ (imageSubscheme (𝟙 X) W) = supportDegree δ W) (n : ℤ) :
    gradedFinitePushforward R δ δ (𝟙 X) hdeg n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact LinearMap.congr_fun (finitePushforward_id (X := X) R) c.val

/-- The same composition law restricts to the existing homogeneous cycles
for any compatible dimension functions. -/
theorem gradedFinitePushforward_comp (R : Type v) [Semiring R]
    {X Y Z : Scheme.{u}}
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ Z) [IsFinite g]
    (hf : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (imageSubscheme f W) = supportDegree δX W)
    (hg : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (imageSubscheme g W) = supportDegree δY W)
    (hfg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (imageSubscheme (f ≫ g) W) = supportDegree δX W)
    (n : ℤ) :
    (gradedFinitePushforward R δY δZ g hg n).comp
        (gradedFinitePushforward R δX δY f hf n) =
      gradedFinitePushforward R δX δZ (f ≫ g) hfg n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact LinearMap.congr_fun (finitePushforward_comp R f g) c.val

end

end HodgeConjecture.SchemeCycles
