module

public import HodgeConjecture.Realization.DeRham.SheafComplex
public import HodgeConjecture.Realization.DeRham.LaurentDifferentials
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

/-!
# Differential forms on affine curves with a principal ideal coordinate ring

Every open subset of the spectrum of a principal ideal ring is a principal
open. The original affine section ring is therefore an actual localization.
This file retains the structure-morphism base action and computes its
Kähler forms from the localization theorem.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite KaehlerDifferential
open scoped ZeroObject
open TensorProduct
open scoped TensorProduct

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- Retain Mathlib's native affine structure-sheaf algebra through the scheme wrapper. -/
instance affineSectionsAlgebra (U : (Spec (.of A)).Opens) : Algebra A Γ(Spec (.of A), U) :=
  inferInstanceAs (Algebra A ((Spec.structureSheaf A).obj.obj
    (.op (show Opens (PrimeSpectrum.Top A) from U))))

/-- The standard affine structural morphism used by the sectionwise complex. -/
abbrev affineStructureMorphism : Spec (.of A) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

/-- The actual base map on an affine open agrees with the native structure-sheaf action. -/
theorem affine_sectionBaseMap (U : (Spec (.of A)).Opens) :
    sectionBaseMap k (Spec (.of A)) (affineStructureMorphism k A) U =
      (algebraMap A Γ(Spec (.of A), U)).comp (algebraMap k A) := by
  apply RingHom.ext
  intro a
  change (((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop) ≫
      (Spec (.of A)).presheaf.map U.leTop.op) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Scalar compatibility of the actual fixed-base action with affine localization. -/
theorem affineSectionScalarTower (U : (Spec (.of A)).Opens) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    IsScalarTower k A Γ(Spec (.of A), U) := by
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact congrArg (fun g : k →+* Γ(Spec (.of A), U) ↦ g a)
    (affine_sectionBaseMap k A U)

/-- Every open in the spectrum of a principal ideal ring is a principal open. -/
theorem exists_basicOpen_of_isPrincipalIdealRing [IsPrincipalIdealRing A]
    (U : (Spec (.of A)).Opens) : ∃ a : A, U = PrimeSpectrum.basicOpen a := by
  let U' : Opens (PrimeSpectrum.Top A) := U
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((U' : Set (PrimeSpectrum.Top A))ᶜ)).mp U'.isOpen.isClosed_compl
  refine ⟨Submodule.IsPrincipal.generator I, ?_⟩
  change U' = PrimeSpectrum.basicOpen _
  apply SetLike.coe_injective
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_singleton_generator, ← hI]
  exact compl_compl _ |>.symm

/-- A chosen principal-open coordinate for an actual affine open. -/
def principalOpenEquation [IsPrincipalIdealRing A] (U : (Spec (.of A)).Opens) : A :=
  (exists_basicOpen_of_isPrincipalIdealRing A U).choose

theorem principalOpenEquation_eq [IsPrincipalIdealRing A] (U : (Spec (.of A)).Opens) :
    U = PrimeSpectrum.basicOpen (principalOpenEquation A U) :=
  (exists_basicOpen_of_isPrincipalIdealRing A U).choose_spec

/-- The actual section ring, with its native affine action, is the indicated localization. -/
instance affineSectionsIsLocalization [IsPrincipalIdealRing A]
    (U : (Spec (.of A)).Opens) :
    IsLocalization.Away (principalOpenEquation A U) Γ(Spec (.of A), U) := by
  let a := principalOpenEquation A U
  have hU : U = PrimeSpectrum.basicOpen a := principalOpenEquation_eq A U
  change IsLocalization.Away a Γ(Spec (.of A), U)
  rw [hU]
  exact inferInstanceAs (IsLocalization.Away a
    ((Spec.structureSheaf A).obj.obj (.op (PrimeSpectrum.basicOpen a))))

end

end HodgeConjecture.SchemeDeRham

namespace HodgeConjecture.AlgebraDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- Extend an actual differential basis along a formally étale algebra map. -/
def localizedKaehlerCoordinates [Algebra.FormallyEtale A B] (e : Ω[A⁄k] ≃ₗ[A] A) :
    Ω[B⁄k] ≃ₗ[B] B :=
  (tensorKaehlerEquivOfFormallyEtale k A B).symm.trans
    ((e.baseChange A B).trans (AlgebraTensorModule.rid A B B))

@[simp]
theorem localizedKaehlerCoordinates_D_algebraMap [Algebra.FormallyEtale A B]
    (e : Ω[A⁄k] ≃ₗ[A] A) (a : A) :
    localizedKaehlerCoordinates k e (D k B (algebraMap A B a)) =
      algebraMap A B (e (D k A a)) := by
  simp [localizedKaehlerCoordinates,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, Algebra.smul_def]

end

end HodgeConjecture.AlgebraDeRham

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [CommRing A] [Algebra k A] [IsPrincipalIdealRing A]

/-- Coordinate-ring differentials give the actual differential coordinates on every open. -/
def affineKaehlerCoordinates (e : Ω[A⁄k] ≃ₗ[A] A) (U : (Spec (.of A)).Opens) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    Ω[Γ(Spec (.of A), U)⁄k] ≃ₗ[Γ(Spec (.of A), U)] Γ(Spec (.of A), U) := by
  letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  letI := affineSectionScalarTower k A U
  letI := Algebra.FormallyEtale.of_isLocalization
    (Rₘ := Γ(Spec (.of A), U)) (.powers (principalOpenEquation A U))
  exact AlgebraDeRham.localizedKaehlerCoordinates k e

@[simp]
theorem affineKaehlerCoordinates_D (e : Ω[A⁄k] ≃ₗ[A] A)
    (U : (Spec (.of A)).Opens) (a : A) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    affineKaehlerCoordinates k A e U (D k Γ(Spec (.of A), U)
      (algebraMap A Γ(Spec (.of A), U) a)) =
      algebraMap A Γ(Spec (.of A), U) (e (D k A a)) := by
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  let := affineSectionScalarTower k A U
  let := Algebra.FormallyEtale.of_isLocalization
    (Rₘ := Γ(Spec (.of A), U)) (.powers (principalOpenEquation A U))
  exact AlgebraDeRham.localizedKaehlerCoordinates_D_algebraMap k e a

/-- A normalized coordinate differential is a basis on each actual open section ring. -/
theorem affineKaehlerCoordinates_basis (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (U : (Spec (.of A)).Opens) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    ∀ ω : Ω[Γ(Spec (.of A), U)⁄k],
      ω = affineKaehlerCoordinates k A e U ω •
        D k Γ(Spec (.of A), U) (algebraMap A Γ(Spec (.of A), U) a₀) := by
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  intro ω
  apply (affineKaehlerCoordinates k A e U).injective
  rw [map_smul, affineKaehlerCoordinates_D, he, map_one, smul_eq_mul, mul_one]

/-- Every higher form on an actual affine open vanishes for this rank-one cotangent module. -/
theorem affineHigherForms_subsingleton (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (U : (Spec (.of A)).Opens)
    (n : ℕ) (hn : 2 ≤ n) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    Subsingleton (⋀[Γ(Spec (.of A), U)]^n Ω[Γ(Spec (.of A), U)⁄k]) := by
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  have hspan : Submodule.span Γ(Spec (.of A), U)
      (Set.range fun _ : Unit ↦ D k Γ(Spec (.of A), U)
        (algebraMap A Γ(Spec (.of A), U) a₀)) = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro ω
    rw [affineKaehlerCoordinates_basis k A e a₀ he U ω]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
  exact exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (fun _ : Unit ↦ D k Γ(Spec (.of A), U)
      (algebraMap A Γ(Spec (.of A), U) a₀)) hspan n (by
        have hcard : Nat.card Unit = 1 := by simp
        rw [hcard]
        omega)

omit [IsPrincipalIdealRing A] in
/-- Pullback between actual affine opens preserves the native coordinate-ring constants. -/
theorem affine_sectionMap_algebraMap {U V : (Spec (.of A)).Opens} (i : U ⟶ V) (a : A) :
    sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i
      (algebraMap A Γ(Spec (.of A), V) a) = algebraMap A Γ(Spec (.of A), U) a := rfl

/-- The degree-one coordinates on all affine opens retain their original restriction maps. -/
theorem affineKaehlerCoordinates_naturality (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) {U V : (Spec (.of A)).Opens} (i : U ⟶ V) :
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) V
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
    ∀ ω : Ω[Γ(Spec (.of A), V)⁄k],
      affineKaehlerCoordinates k A e U
          (AlgebraDeRham.kaehlerMap k
            (sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i) ω) =
        sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i
          (affineKaehlerCoordinates k A e V ω) := by
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) V
  let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U
  intro ω
  conv_lhs => rw [affineKaehlerCoordinates_basis k A e a₀ he V ω]
  rw [AlgebraDeRham.kaehlerMap_smul, map_smul, AlgebraDeRham.kaehlerMap_D,
    affine_sectionMap_algebraMap, affineKaehlerCoordinates_D, he, map_one,
    smul_eq_mul, mul_one]

/-- Degree-one sectionwise forms on the affine curve are its actual regular-function sheaf. -/
def affineOneFormsIsoFunctions (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) :
    formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) 1 ≅
      functionsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) :=
  NatIso.ofComponents (fun U ↦
    letI := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U.unop
    (((exteriorPower.oneEquiv Γ(Spec (.of A), U.unop)
      Ω[Γ(Spec (.of A), U.unop)⁄k]).trans
        (affineKaehlerCoordinates k A e U.unop)).restrictScalars k).toModuleIso)
    (fun {U V} i ↦ by
      let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U.unop
      let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) V.unop
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      have hforms := congrArg (fun g ↦ g ω) (AlgebraDeRham.formsMap_oneEquiv k
        (sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i.unop))
      change (exteriorPower.oneEquiv Γ(Spec (.of A), V.unop) _)
          (AlgebraDeRham.formsMap k
            (sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i.unop) 1 ω) =
        AlgebraDeRham.kaehlerMap k
          (sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i.unop)
          ((exteriorPower.oneEquiv Γ(Spec (.of A), U.unop) _) ω) at hforms
      change affineKaehlerCoordinates k A e V.unop
          ((exteriorPower.oneEquiv Γ(Spec (.of A), V.unop) _)
            (AlgebraDeRham.formsMap k
              (sectionMap k (Spec (.of A)) (affineStructureMorphism k A) i.unop) 1 ω)) = _
      rw [hforms]
      exact affineKaehlerCoordinates_naturality k A e a₀ he i.unop _)

theorem affineOneFormsPresheaf_isSheaf (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) :
    (formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) 1).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_iso (affineOneFormsIsoFunctions k A e a₀ he).symm
    (functionsPresheaf_isSheaf k (Spec (.of A)) (affineStructureMorphism k A))

/-- Higher sectionwise forms vanish on every actual open of the affine curve. -/
def affineHigherFormsIsoZero (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (n : ℕ) (hn : 2 ≤ n) :
    formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n ≅
      (Functor.const ((Spec (.of A)).Opensᵒᵖ)).obj (0 : ModuleCat.{u} k) := by
  haveI (U : (Spec (.of A)).Opensᵒᵖ) :
      Subsingleton ((formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n).obj U) := by
    let := sectionAlgebra k (Spec (.of A)) (affineStructureMorphism k A) U.unop
    exact affineHigherForms_subsingleton k A e a₀ he U.unop n hn
  exact NatIso.ofComponents (fun U ↦ (ModuleCat.isZero_of_subsingleton _).isoZero)
    (fun {_ _} _ ↦ (Limits.isZero_zero _).eq_of_tgt _ _)

/-- For the principal affine curve, no sheafification changes any degree of the forms. -/
theorem affineFormsPresheaf_isSheaf (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (n : ℕ) :
    (formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n).IsSheaf := by
  rcases n with _ | n
  · exact zeroFormsPresheaf_isSheaf _ _ _
  rcases n with _ | n
  · exact affineOneFormsPresheaf_isSheaf k A e a₀ he
  · apply TopCat.Presheaf.isSheaf_of_iso
      (affineHigherFormsIsoZero k A e a₀ he (n + 2) (by omega)).symm
    exact CategoryTheory.Presheaf.isSheaf_of_isTerminal _
      (Limits.isZero_zero (ModuleCat.{u} k)).isTerminal

/-- The canonical unit, not a chosen equivalence, is an isomorphism on the affine curve. -/
theorem affineFormsSheafUnit_isIso (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (n : ℕ) :
    IsIso (CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec (.of A)))
      (formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n)) :=
  CategoryTheory.isIso_toSheafify _ (affineFormsPresheaf_isSheaf k A e a₀ he n)

/-- The canonical unit identifies the original forms with actual sheaf sections on every open. -/
def affineFormsSheafSectionIso (e : Ω[A⁄k] ≃ₗ[A] A)
    (a₀ : A) (he : e (D k A a₀) = 1) (n : ℕ) (U : (Spec (.of A)).Opens) :
    (formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n).obj (.op U) ≅
      (formsSheaf k (Spec (.of A)) (affineStructureMorphism k A) n).obj.obj (.op U) := by
  letI := affineFormsSheafUnit_isIso k A e a₀ he n
  exact asIso ((CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec (.of A)))
    (formsPresheaf k (Spec (.of A)) (affineStructureMorphism k A) n)).app (.op U))

end

end HodgeConjecture.SchemeDeRham

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- On the actual affine line over a field, all sectionwise forms already form sheaves. -/
theorem affineLineFormsPresheaf_isSheaf (n : ℕ) :
    (formsPresheaf k (Spec (.of (Polynomial k)))
      (affineStructureMorphism k (Polynomial k)) n).IsSheaf :=
  affineFormsPresheaf_isSheaf k (Polynomial k) (polynomialEquiv k) Polynomial.X (by simp) n

/-- Every degree of the affine-line comparison is the canonical sheafification unit. -/
theorem affineLineFormsSheafUnit_isIso (n : ℕ) :
    IsIso (CategoryTheory.toSheafify
      (Opens.grothendieckTopology (Spec (.of (Polynomial k))))
      (formsPresheaf k (Spec (.of (Polynomial k)))
        (affineStructureMorphism k (Polynomial k)) n)) :=
  affineFormsSheafUnit_isIso k (Polynomial k) (polynomialEquiv k) Polynomial.X (by simp) n

end

end HodgeConjecture.SchemeDeRham
