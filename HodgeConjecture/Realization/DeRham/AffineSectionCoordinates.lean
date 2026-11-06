module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import HodgeConjecture.Realization.DeRham.SheafComplex

@[expose] public section

/-!
# Affine-chart coordinates for actual scheme sections

An affine open immersion identifies sections on its actual open range with
the original coordinate ring. If a second affine chart factors through it
by a specified spectrum map, the actual structure-sheaf restriction becomes
that very ring map. These identifications retain the geometric maps used
in the projective-line Čech complex.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SchemeDeRham

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {X : Scheme.{u}} {A B : CommRingCat.{u}}

/-- Sections on the open range of an actual affine chart, in its original coordinates. -/
def affineSectionIso (i : Spec A ⟶ X) [IsOpenImmersion i] :
    Γ(X, i.opensRange) ≅ A :=
  (IsOpenImmersion.ΓIsoTop i).symm ≪≫ Scheme.ΓSpecIso A

theorem affineSectionIso_hom (i : Spec A ⟶ X) [IsOpenImmersion i] :
    (affineSectionIso i).hom =
      i.appLE i.opensRange ⊤ (by simp) ≫ (Scheme.ΓSpecIso A).hom := by
  simp [affineSectionIso, IsOpenImmersion.ΓIsoTop, Scheme.Hom.appIso_hom']

/-- A factorization of affine charts gives the actual inclusion of their open ranges. -/
theorem affineRange_le (i : Spec A ⟶ X) (j : Spec B ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (φ : A ⟶ B)
    (h : Spec.map φ ≫ i = j) : j.opensRange ≤ i.opensRange := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Spec.map φ y, ?_⟩
  exact congrArg (fun f : Spec B ⟶ X ↦ f y) h

/-- The section restriction square is forced by the factorization of scheme charts. -/
theorem affineSectionIso_restriction (i : Spec A ⟶ X) (j : Spec B ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (φ : A ⟶ B)
    (h : Spec.map φ ≫ i = j) :
    X.presheaf.map (homOfLE (affineRange_le i j φ h)).op ≫
        (affineSectionIso j).hom = (affineSectionIso i).hom ≫ φ := by
  have hi : (⊤ : (Spec A).Opens) ≤ i ⁻¹ᵁ i.opensRange := by simp
  have hj : (⊤ : (Spec B).Opens) ≤ j ⁻¹ᵁ j.opensRange := by simp
  have hm : (⊤ : (Spec B).Opens) ≤ (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec A).Opens) := by simp
  have hc :
      X.presheaf.map (homOfLE (affineRange_le i j φ h)).op ≫
        j.appLE j.opensRange ⊤ hj =
      i.appLE i.opensRange ⊤ hi ≫ (Spec.map φ).appTop := by
    change X.presheaf.map (homOfLE (affineRange_le i j φ h)).op ≫
        j.appLE j.opensRange ⊤ hj =
      i.appLE i.opensRange ⊤ hi ≫ (Spec.map φ).appLE ⊤ ⊤ hm
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [h]
  simp only [affineSectionIso_hom, Category.assoc]
  rw [← Category.assoc, hc, Category.assoc, Scheme.ΓSpecIso_naturality]

/-- Constants from the scheme's actual structural morphism become the original
coordinate-ring constants on an affine chart over the base. -/
theorem affineSectionIso_constants {K : CommRingCat.{u}} (f : X ⟶ Spec K)
    (i : Spec A ⟶ X) [IsOpenImmersion i] (c : K ⟶ A)
    (h : i ≫ f = Spec.map c) :
    (Scheme.ΓSpecIso K).inv ≫ f.appLE ⊤ i.opensRange (by simp) ≫
        (affineSectionIso i).hom = c := by
  rw [affineSectionIso_hom, ← Category.assoc, ← Category.assoc,
    Category.assoc (Scheme.ΓSpecIso K).inv,
    Scheme.Hom.appLE_comp_appLE]
  have hc : (i ≫ f).appLE ⊤ ⊤ (by simp) = (Spec.map c).appTop := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
      congrArg (fun g : Spec A ⟶ Spec K ↦ g.appTop) h
  rw [hc]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- Actual section coordinates are linear over the original scheme base. -/
def affineSectionAlgEquiv (k : Type u) [CommRing k] [Algebra k A]
    (f : X ⟶ Spec (.of k)) (i : Spec A ⟶ X) [IsOpenImmersion i]
    (h : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    letI := sectionAlgebra k X f i.opensRange
    Γ(X, i.opensRange) ≃ₐ[k] A := by
  letI := sectionAlgebra k X f i.opensRange
  refine { (affineSectionIso i).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro a
  exact congrArg (fun ψ : CommRingCat.of k ⟶ A ↦ ψ a)
    (affineSectionIso_constants f i (CommRingCat.ofHom (algebraMap k A)) h)

@[simp]
theorem affineSectionAlgEquiv_apply (k : Type u) [CommRing k] [Algebra k A]
    (f : X ⟶ Spec (.of k)) (i : Spec A ⟶ X) [IsOpenImmersion i]
    (h : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (a : Γ(X, i.opensRange)) :
    affineSectionAlgEquiv k f i h a = (affineSectionIso i).hom a := rfl

end HodgeConjecture.SchemeDeRham
