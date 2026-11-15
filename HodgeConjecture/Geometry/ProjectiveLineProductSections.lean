module

public import HodgeConjecture.Geometry.ProjectiveLineProduct
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Rational sections and coordinate fibers of the projective-line product

Evaluation at zero gives an actual section of `P¹_k → Spec k`. Pairing this
section with the identity on `P¹_k` produces the two coordinate-fiber maps
into `P¹_k ×_{Spec k} P¹_k`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The rational zero section, built from evaluation at zero in the first affine chart. -/
def projectiveLineZeroSection : Spec (.of k) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    projectiveLineXChart k

/-- Evaluation at zero lands at the existing chart origin of `P¹`. -/
@[simp] theorem projectiveLineZeroSection_apply_unique :
    projectiveLineZeroSection k (default : Spec (.of k)) = projectiveLineZero k := by
  change projectiveLineXChart k
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
        (default : Spec (.of k))) =
    projectiveLineXChart k (affineLineOrigin k)
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap (Polynomial.evalRingHom (0 : k)) (⊥ : Ideal k) =
    Ideal.span {(Polynomial.X : Polynomial k)}
  rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]
  simp

/-- The zero section is a morphism over `Spec k`. -/
@[simp] theorem projectiveLineZeroSection_comp_structureMorphism :
    projectiveLineZeroSection k ≫ (projectiveLine k ↘ Spec (.of k)) =
      𝟙 (Spec (.of k)) := by
  rw [projectiveLineZeroSection, Category.assoc,
    projectiveLineXChart_comp_structureMorphism]
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = _
  rw [← Spec.map_comp]
  have h : (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
    ext a
    exact Polynomial.eval_C
  rw [h, Spec.map_id]

/-- The rational zero section is a closed immersion. -/
instance projectiveLineZeroSection_isClosedImmersion :
    IsClosedImmersion (projectiveLineZeroSection k) :=
  isClosedImmersion_of_comp_eq_id
    (projectiveLine k ↘ Spec (.of k)) (projectiveLineZeroSection k)
    (projectiveLineZeroSection_comp_structureMorphism k)

/-- The map whose first coordinate is zero and whose second coordinate is the identity. -/
def projectiveLineProductZeroFirst : projectiveLine k ⟶ projectiveLineProduct k :=
  pullback.lift
    ((projectiveLine k ↘ Spec (.of k)) ≫ projectiveLineZeroSection k)
    (𝟙 (projectiveLine k)) (by
      simp [Category.assoc])

/-- The map whose first coordinate is the identity and whose second coordinate is zero. -/
def projectiveLineProductZeroSecond : projectiveLine k ⟶ projectiveLineProduct k :=
  pullback.lift
    (𝟙 (projectiveLine k))
    ((projectiveLine k ↘ Spec (.of k)) ≫ projectiveLineZeroSection k) (by
      simp [Category.assoc])

@[simp] theorem projectiveLineProductZeroFirst_fst :
    projectiveLineProductZeroFirst k ≫ projectiveLineProductFst k =
      (projectiveLine k ↘ Spec (.of k)) ≫ projectiveLineZeroSection k := by
  simp [projectiveLineProductZeroFirst, projectiveLineProductFst]

@[simp] theorem projectiveLineProductZeroFirst_snd :
    projectiveLineProductZeroFirst k ≫ projectiveLineProductSnd k =
      𝟙 (projectiveLine k) := by
  simp [projectiveLineProductZeroFirst, projectiveLineProductSnd]

@[simp] theorem projectiveLineProductZeroSecond_fst :
    projectiveLineProductZeroSecond k ≫ projectiveLineProductFst k =
      𝟙 (projectiveLine k) := by
  simp [projectiveLineProductZeroSecond, projectiveLineProductFst]

@[simp] theorem projectiveLineProductZeroSecond_snd :
    projectiveLineProductZeroSecond k ≫ projectiveLineProductSnd k =
      (projectiveLine k ↘ Spec (.of k)) ≫ projectiveLineZeroSection k := by
  simp [projectiveLineProductZeroSecond, projectiveLineProductSnd]

end AlgebraicGeometry

end
