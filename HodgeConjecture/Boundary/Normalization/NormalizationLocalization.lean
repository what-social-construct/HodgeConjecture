import HodgeConjecture.Boundary.Normalization.Model
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Localization of the same normalization model

Base-ring enlargement induces the inclusion of integral closures in the
same ambient ring. These inclusions are functorial and commute with the
existing normalization maps. If the base enlargement is a localization,
the new integral closure is the corresponding localization of the old one.
No normality, Noetherianity, or field-extension hypothesis is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

variable {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]

/-- Enlarge the base ring, retaining each element of the original ambient ring. -/
def normalizationBaseChangeMap :
    normalizedCoordinateRing B E →ₐ[B] normalizedCoordinateRing C E where
  toFun x := ⟨x, x.property.tower_top (A := C)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The normalization restriction does not change the ambient element. -/
theorem normalizationBaseChangeMap_coe (x : normalizedCoordinateRing B E) :
    ((normalizationBaseChangeMap (C := C) x : normalizedCoordinateRing C E) : E) = x := rfl

/-- Inclusions of integral closures in the same ambient ring are injective. -/
theorem normalizationBaseChangeMap_injective :
    Function.Injective (normalizationBaseChangeMap (B := B) (C := C) (E := E)) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : normalizedCoordinateRing C E => (z : E)) h)

/-- Restricting the base to itself is the identity on its existing normalization. -/
theorem normalizationBaseChangeMap_self :
    normalizationBaseChangeMap (B := B) (C := B) (E := E) = AlgHom.id B _ := by
  ext x
  rfl

/-- Successive base enlargements retain the same normalization inclusion. -/
theorem normalizationBaseChangeMap_trans
    {D : Type u} [CommRing D] [Algebra B D] [Algebra C D] [Algebra D E]
    [IsScalarTower B C D] [IsScalarTower B D E] [IsScalarTower C D E] :
    (normalizationBaseChangeMap (B := C) (C := D) (E := E)).toRingHom.comp
        (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toRingHom =
      (normalizationBaseChangeMap (B := B) (C := D) (E := E)).toRingHom := by
  ext x
  rfl

/-- Base enlargement commutes with the original map of ambient algebras. -/
theorem normalizationBaseChangeMap_naturality
    {F : Type u} [CommRing F] [Algebra B F] [Algebra C F] [IsScalarTower B C F]
    (f : E →ₐ[C] F) :
    (normalizationMap F f).toRingHom.comp
        (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toRingHom =
      (normalizationBaseChangeMap (B := B) (C := C) (E := F)).toRingHom.comp
        (normalizationMap F (f.restrictScalars B)).toRingHom := by
  ext x
  rfl

/-- Integral closure commutes with localization inside the same ambient ring,
along the original inclusion. Compatible scalar maps encode the denominators. -/
theorem normalizedCoordinateRing_isLocalization (M : Submonoid B) [IsLocalization M C] :
    letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B E) M)
      (normalizedCoordinateRing C E) := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    have h := (IsLocalization.map_units C (⟨m, hm⟩ : M)).map
      (algebraMap C (normalizedCoordinateRing C E))
    have he : algebraMap (normalizedCoordinateRing B E) (normalizedCoordinateRing C E)
          (algebraMap B (normalizedCoordinateRing B E) m) =
        algebraMap C (normalizedCoordinateRing C E) (algebraMap B C m) := by
      apply Subtype.ext
      exact IsScalarTower.algebraMap_apply B C E m
    rw [he]
    exact h
  · intro x
    obtain ⟨m, hm⟩ := x.property.exists_multiple_integral_of_isLocalization M (x : E)
    refine ⟨⟨⟨m • (x : E), hm⟩,
      ⟨algebraMap B (normalizedCoordinateRing B E) m, ⟨m, m.property, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    change (x : E) * algebraMap B E m = m • (x : E)
    simp only [Submonoid.smul_def, Algebra.smul_def, mul_comm]
  · intro x y h
    refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, one_mul] using
      normalizationBaseChangeMap_injective (B := B) (C := C) (E := E) h

/-- The canonical tensor base change is the integral closure over the localized
base, not an abstractly substituted normalization ring. -/
def normalizationLocalizationBaseChangeEquiv (M : Submonoid B) [IsLocalization M C] :
    (C ⊗[B] normalizedCoordinateRing B E) ≃ₐ[C] normalizedCoordinateRing C E := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  letI : IsScalarTower B (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B E) M)
      (normalizedCoordinateRing C E) := normalizedCoordinateRing_isLocalization M
  letI : Algebra.IsPushout B C (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (Algebra.isPushout_of_isLocalization M C
      (normalizedCoordinateRing B E) (normalizedCoordinateRing C E)).symm
  exact Algebra.IsPushout.equiv B C (normalizedCoordinateRing B E) (normalizedCoordinateRing C E)

/-- The localization comparison preserves the actual ambient elements and scalars. -/
theorem normalizationLocalizationBaseChangeEquiv_tmul
    (M : Submonoid B) [IsLocalization M C] (c : C) (x : normalizedCoordinateRing B E) :
    ((normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M
      (c ⊗ₜ[B] x) : normalizedCoordinateRing C E) : E) = algebraMap C E c * (x : E) := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  letI : IsScalarTower B (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B E) M)
      (normalizedCoordinateRing C E) := normalizedCoordinateRing_isLocalization M
  letI : Algebra.IsPushout B C (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (Algebra.isPushout_of_isLocalization M C
      (normalizedCoordinateRing B E) (normalizedCoordinateRing C E)).symm
  exact congrArg (fun z : normalizedCoordinateRing C E => (z : E))
    (Algebra.IsPushout.equiv_tmul B C (normalizedCoordinateRing B E)
      (normalizedCoordinateRing C E) c x)

/-- The scheme map contravariant to the same-element normalization inclusion. -/
def normalizationBaseChange : normalizedAffineModel C E ⟶ normalizedAffineModel B E :=
  Spec.map (CommRingCat.ofHom
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toRingHom)

/-- The structural square retains both original base maps. -/
theorem normalizationBaseChange_comp_toBase :
    normalizationBaseChange (B := B) (C := C) (E := E) ≫ normalizedModelToBase B E =
      normalizedModelToBase C E ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
  unfold normalizationBaseChange normalizedModelToBase
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  exact IsScalarTower.algebraMap_apply B C E b

/-- The original normalization domination morphism commutes with restriction. -/
theorem normalizationBaseChange_naturality
    {F : Type u} [CommRing F] [Algebra B F] [Algebra C F] [IsScalarTower B C F]
    (f : E →ₐ[C] F) :
    normalizationBaseChange (B := B) (C := C) (E := F) ≫
        normalizationDomination F (f.restrictScalars B) =
      normalizationDomination F f ≫ normalizationBaseChange (B := B) (C := C) (E := E) := by
  unfold normalizationBaseChange normalizationDomination
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The identity base restriction has identity scheme map. -/
theorem normalizationBaseChange_self :
    normalizationBaseChange (B := B) (C := B) (E := E) = 𝟙 _ := by
  unfold normalizationBaseChange
  rw [normalizationBaseChangeMap_self]
  exact Spec.map_id _

/-- Successive restrictions compose on the same normalization schemes. -/
theorem normalizationBaseChange_trans
    {D : Type u} [CommRing D] [Algebra B D] [Algebra C D] [Algebra D E]
    [IsScalarTower B C D] [IsScalarTower B D E] [IsScalarTower C D E] :
    normalizationBaseChange (B := C) (C := D) (E := E) ≫
        normalizationBaseChange (B := B) (C := C) (E := E) =
      normalizationBaseChange (B := B) (C := D) (E := E) := by
  unfold normalizationBaseChange
  rw [← Spec.map_comp]
  congr 1

/-- A principal base localization localizes the existing normalization
at the image of that same section. -/
theorem normalizedCoordinateRing_isLocalizationAway (r : B) [IsLocalization.Away r C] :
    letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
    IsLocalization.Away (algebraMap B (normalizedCoordinateRing B E) r)
      (normalizedCoordinateRing C E) := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
    (normalizedCoordinateRing_isLocalization (B := B) (C := C) (E := E) (Submonoid.powers r))

/-- Principal localization induces an open immersion of the same models. -/
theorem normalizationBaseChange_isOpenImmersion (r : B) [IsLocalization.Away r C] :
    IsOpenImmersion (normalizationBaseChange (B := B) (C := C) (E := E)) := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  letI : IsLocalization.Away (algebraMap B (normalizedCoordinateRing B E) r)
      (normalizedCoordinateRing C E) := normalizedCoordinateRing_isLocalizationAway r
  exact IsOpenImmersion.of_isLocalization (algebraMap B (normalizedCoordinateRing B E) r)

/-- Its image is precisely the inverse image of the original principal open. -/
theorem normalizationBaseChange_range (r : B) [IsLocalization.Away r C] :
    Set.range (normalizationBaseChange (B := B) (C := C) (E := E)).base =
      (normalizedModelToBase B E).base ⁻¹'
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum B)) := by
  letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
  letI : IsLocalization.Away (algebraMap B (normalizedCoordinateRing B E) r)
      (normalizedCoordinateRing C E) := normalizedCoordinateRing_isLocalizationAway r
  exact PrimeSpectrum.localization_away_comap_range (normalizedCoordinateRing C E)
    (algebraMap B (normalizedCoordinateRing B E) r)

end

end HodgeConjecture.CollisionFoundations
