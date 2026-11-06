module

public import HodgeConjecture.CommutativeAlgebra.FiniteFiberLength
public import HodgeConjecture.Cycles.StructuralResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

/-!
# Degree as the sum of the actual local lengths of a finite scheme

A finite morphism to a field spectrum supplies the global sections algebra.
Its dimension is the sum of the stalk lengths weighted by the degrees of
the actual residue fields, with the independently defined structural base
action. This includes empty and nonreduced finite schemes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

/-- The actual structural action on global sections, before evaluation. -/
def globalSectionBaseAlgebra (k : Type u) [CommRing k] {S : Scheme.{u}}
    (p : S ⟶ Spec (CommRingCat.of k)) : Algebra k Γ(S, ⊤) :=
  (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom).toAlgebra

/-- A finite structural morphism supplies a finite algebra on its actual
global sections. -/
theorem globalSectionBaseAlgebra_moduleFinite (k : Type u) [CommRing k]
    {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) [IsFinite p] :
    letI := globalSectionBaseAlgebra k p
    Module.Finite k Γ(S, ⊤) := by
  letI := globalSectionBaseAlgebra k p
  exact ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp
    (inferInstance : IsFinite p)).2.comp
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)

/-- Evaluation on an affine Artinian scheme is onto its actual residue field. -/
theorem affine_artinian_evaluation_surjective (S : Scheme.{u}) [IsAffine S]
    [IsArtinianRing Γ(S, ⊤)] (x : S) : Function.Surjective (S.Γevaluation x) := by
  letI := S.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : S.Opens))
  let q := ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal
  letI : IsLocalization.AtPrime (S.presheaf.stalk x) q :=
    (isAffineOpen_top S).isLocalization_stalk ⟨x, trivial⟩
  exact (S.residue_surjective x).comp
    (IsArtinianRing.localization_surjective q.primeCompl (S.presheaf.stalk x))

private theorem affine_evaluation_ker (S : Scheme.{u}) [IsAffine S] (x : S) :
    RingHom.ker (S.Γevaluation x).hom =
      ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  change RingHom.ker ((S.residue x).hom.comp
    (S.presheaf.germ ⊤ x trivial).hom) = _
  rw [← RingHom.comap_ker]
  change (RingHom.ker (IsLocalRing.residue (S.presheaf.stalk x))).comap _ = _
  rw [IsLocalRing.ker_residue]
  rfl

private def affineArtinianPointEquivMaximal (S : Scheme.{u}) [IsAffine S]
    [IsArtinianRing Γ(S, ⊤)] : S ≃ MaximalSpectrum Γ(S, ⊤) where
  toFun x := ⟨((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal, inferInstance⟩
  invFun q := (isAffineOpen_top S).fromSpec.base ⟨q.asIdeal, q.isMaximal.isPrime⟩
  left_inv x := (isAffineOpen_top S).fromSpec_primeIdealOf ⟨x, trivial⟩
  right_inv q := by
    apply MaximalSpectrum.ext
    exact congrArg PrimeSpectrum.asIdeal
      ((Scheme.homeoOfIso (isAffineOpen_top S).isoSpec).apply_symm_apply
        ⟨q.asIdeal, q.isMaximal.isPrime⟩)

private def affineArtinianResidueEquiv (k : Type u) [CommRing k]
    {S : Scheme.{u}} [IsAffine S] [IsArtinianRing Γ(S, ⊤)]
    (p : S ⟶ Spec (CommRingCat.of k)) (x : S) :
    letI := globalSectionBaseAlgebra k p
    letI := residueFieldBaseAlgebra k p x
    (Γ(S, ⊤) ⧸ (affineArtinianPointEquivMaximal S x).asIdeal) ≃ₐ[k] S.residueField x := by
  letI := globalSectionBaseAlgebra k p
  letI := residueFieldBaseAlgebra k p x
  let ev : Γ(S, ⊤) →ₐ[k] S.residueField x :=
    { (S.Γevaluation x).hom with commutes' := fun _ => rfl }
  have hker : RingHom.ker ev.toRingHom =
      (affineArtinianPointEquivMaximal S x).asIdeal := affine_evaluation_ker S x
  exact (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (show Function.Surjective ev from affine_artinian_evaluation_surjective S x))

private theorem affineArtinian_stalk_length (S : Scheme.{u}) [IsAffine S]
    [IsArtinianRing Γ(S, ⊤)] (x : S) :
    Module.length (S.presheaf.stalk x) (S.presheaf.stalk x) =
      Module.length
        (Localization.AtPrime (affineArtinianPointEquivMaximal S x).asIdeal)
        (Localization.AtPrime (affineArtinianPointEquivMaximal S x).asIdeal) := by
  letI := S.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : S.Opens))
  let q := (affineArtinianPointEquivMaximal S x).asIdeal
  letI : IsLocalization.AtPrime (S.presheaf.stalk x) q :=
    (isAffineOpen_top S).isLocalization_stalk ⟨x, trivial⟩
  exact length_regular_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (S.presheaf.stalk x)
      (Localization.AtPrime q)).toRingEquiv

/-- Every local ring of an actual finite scheme over a field has finite
length. Thus passage from its length to a natural number loses no data. -/
theorem finiteScheme_stalk_length_ne_top (k : Type u) [Field k]
    {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) [IsFinite p] (x : S) :
    Module.length (S.presheaf.stalk x) (S.presheaf.stalk x) ≠ ⊤ := by
  letI := globalSectionBaseAlgebra k p
  letI : IsAffine S := isAffine_of_isAffineHom p
  letI := globalSectionBaseAlgebra_moduleFinite k p
  letI : IsArtinianRing Γ(S, ⊤) := IsArtinianRing.of_finite k Γ(S, ⊤)
  letI : IsNoetherianRing Γ(S, ⊤) := IsNoetherianRing.of_finite k Γ(S, ⊤)
  letI := S.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : S.Opens))
  let q := ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal
  letI : IsLocalization.AtPrime (S.presheaf.stalk x) q :=
    (isAffineOpen_top S).isLocalization_stalk ⟨x, trivial⟩
  letI : IsArtinianRing (S.presheaf.stalk x) :=
    IsArtinianRing.localization_artinian q.primeCompl _
  letI : IsNoetherianRing (S.presheaf.stalk x) :=
    isNoetherianRing_of_surjective Γ(S, ⊤) _ (algebraMap _ _)
      (IsArtinianRing.localization_surjective q.primeCompl _)
  exact Module.length_ne_top

/-- A finite scheme's degree is the sum of its actual residue degrees
times its actual stalk lengths. Nilpotents contribute through the length. -/
theorem finiteScheme_finrank_eq_sum_stalkLength (k : Type u) [Field k]
    {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) [IsFinite p] :
    letI := globalSectionBaseAlgebra k p
    Module.finrank k Γ(S, ⊤) = ∑ᶠ x : S,
      (letI := residueFieldBaseAlgebra k p x;
        Module.finrank k (S.residueField x)) *
        (Module.length (S.presheaf.stalk x) (S.presheaf.stalk x)).toNat := by
  letI := globalSectionBaseAlgebra k p
  letI : IsAffine S := isAffine_of_isAffineHom p
  letI := globalSectionBaseAlgebra_moduleFinite k p
  letI : IsArtinianRing Γ(S, ⊤) := IsArtinianRing.of_finite k Γ(S, ⊤)
  rw [finrank_eq_sum_residueDegree_mul_length k Γ(S, ⊤)]
  symm
  apply finsum_eq_of_bijective (affineArtinianPointEquivMaximal S)
    (affineArtinianPointEquivMaximal S).bijective
  intro x
  letI := residueFieldBaseAlgebra k p x
  rw [← (affineArtinianResidueEquiv k p x).toLinearEquiv.finrank_eq,
    affineArtinian_stalk_length S x]

end

end HodgeConjecture.SchemeCycles
