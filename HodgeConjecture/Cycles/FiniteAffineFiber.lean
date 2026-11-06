module

public import HodgeConjecture.CommutativeAlgebra.FiniteLocalization
public import HodgeConjecture.Boundary.Normalization.FiniteAffineChart

@[expose] public section

/-!
# The maximal ideals over a target point are the actual source fiber

On an affine target chart, use the whole affine inverse image of the
existing finite morphism. The maximal ideals of its semilocal algebra
correspond to the actual source points over the chosen target point.
This identifies the index set in the coefficient computation of Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT

The construction uses actual section maps and chart maps. It assumes no
normality, integrality of the schemes, or separately supplied fiber model.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (U : Y.Opens) (hU : IsAffineOpen U)

set_option quotPrecheck false in
local notation "A" => Γ(Y, U)
set_option quotPrecheck false in
local notation "B" => Γ(X, f ⁻¹ᵁ U)

local instance finiteAffineFiberSectionAlgebra : Algebra A B := (f.app U).hom.toAlgebra

/-- The prime corresponding to a point pulls back along the literal section homomorphism. -/
theorem finiteAffine_primeIdealOf_comap (x : X) (hx : f.base x ∈ U) :
    PrimeSpectrum.comap (f.app U).hom ((hU.preimage f).primeIdealOf ⟨x, hx⟩) =
      hU.primeIdealOf ⟨f.base x, hx⟩ := by
  apply hU.fromSpec.isOpenEmbedding.injective
  change (Spec.map (f.app U) ≫ hU.fromSpec).base
    ((hU.preimage f).primeIdealOf ⟨x, hx⟩) = _
  rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl]
  change f.base ((hU.preimage f).fromSpec.base ((hU.preimage f).primeIdealOf ⟨x, hx⟩)) = _
  rw [(hU.preimage f).fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]

/-- Primes over the target chart prime correspond to the actual points in its fiber. -/
def finiteAffine_primesOverEquivFiber (y : U) :
    (hU.primeIdealOf y).asIdeal.primesOver B ≃ {x : X // f.base x = y.val} where
  toFun q := ⟨(hU.preimage f).fromSpec.base ⟨q.val, q.property.1⟩, by
    have hq : PrimeSpectrum.comap (f.app U).hom ⟨q.val, q.property.1⟩ =
        hU.primeIdealOf y := PrimeSpectrum.ext (Ideal.over_def q.val (hU.primeIdealOf y).asIdeal).symm
    have hsq : Spec.map (f.app U) ≫ hU.fromSpec = (hU.preimage f).fromSpec ≫ f := by
      simpa only [Scheme.Hom.app_eq_appLE] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl)
    have h := congrArg (fun g : Spec (.of B) ⟶ Y => g.base ⟨q.val, q.property.1⟩) hsq
    change hU.fromSpec.base (PrimeSpectrum.comap (f.app U).hom ⟨q.val, q.property.1⟩) =
      f.base ((hU.preimage f).fromSpec.base ⟨q.val, q.property.1⟩) at h
    rw [hq, hU.fromSpec_primeIdealOf] at h
    exact h.symm⟩
  invFun x := ⟨((hU.preimage f).primeIdealOf ⟨x.val, by
      change f.base x.val ∈ U
      rw [x.property]
      exact y.property⟩).asIdeal,
    inferInstance, ⟨by
      have hx : f.base x.val ∈ U := by rw [x.property]; exact y.property
      have h := finiteAffine_primeIdealOf_comap f U hU x.val hx
      have hy : (⟨f.base x.val, hx⟩ : U) = y := Subtype.ext x.property
      rw [hy] at h
      exact (congrArg PrimeSpectrum.asIdeal h).symm⟩⟩
  left_inv q := by
    apply Subtype.ext
    exact congrArg PrimeSpectrum.asIdeal
      ((Scheme.homeoOfIso (hU.preimage f).isoSpec).apply_symm_apply ⟨q.val, q.property.1⟩)
  right_inv x := Subtype.ext ((hU.preimage f).fromSpec_primeIdealOf _)

/-- Maximal ideals of the whole localized inverse image index the actual finite fiber. -/
def finiteAffineFiberEquiv (y : U) :
    MaximalSpectrum (finiteLocalization A B (hU.primeIdealOf y).asIdeal) ≃
      {x : X // f.base x = y.val} := by
  letI : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
  exact (finiteLocalization_maximalEquiv A B (hU.primeIdealOf y).asIdeal).trans
    (finiteAffine_primesOverEquivFiber f U hU y)

include hU in
/-- Finiteness of the actual fiber follows from the finite semilocal algebra. -/
theorem finiteAffine_fiber_finite (y : U) : Finite {x : X // f.base x = y.val} := by
  letI : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
  letI := finite_primesOver A B (hU.primeIdealOf y).asIdeal
  exact Finite.of_equiv _ (finiteAffine_primesOverEquivFiber f U hU y)

/-- The maximal localization in the norm sum is the actual source stalk.
The equivalence preserves the original section-ring action. -/
def finiteAffineFiber_stalkEquiv (y : U)
    (q : MaximalSpectrum (finiteLocalization A B (hU.primeIdealOf y).asIdeal)) :
    let x := finiteAffineFiberEquiv f U hU y q
    letI := X.presheaf.algebra_section_stalk
      (⟨x.val, by change f.base x.val ∈ U; rw [x.property]; exact y.property⟩ : f ⁻¹ᵁ U)
    X.presheaf.stalk x.val ≃ₐ[B] Localization.AtPrime q.asIdeal := by
  letI : Module.Finite A B := CollisionFoundations.finiteAffinePreimage_moduleFinite f U hU
  let p := (hU.primeIdealOf y).asIdeal
  let x := finiteAffineFiberEquiv f U hU y q
  have hx : f.base x.val ∈ U := by rw [x.property]; exact y.property
  letI := X.presheaf.algebra_section_stalk (⟨x.val, hx⟩ : f ⁻¹ᵁ U)
  have hprime : ((hU.preimage f).primeIdealOf ⟨x.val, hx⟩).asIdeal =
      q.asIdeal.comap (algebraMap B (finiteLocalization A B p)) := by
    exact congrArg Subtype.val
      ((finiteAffine_primesOverEquivFiber f U hU y).symm_apply_apply
        (finiteLocalization_maximalEquiv A B p q))
  letI : IsLocalization.AtPrime (X.presheaf.stalk x.val)
      (q.asIdeal.comap (algebraMap B (finiteLocalization A B p))) := by
    simpa only [hprime] using (hU.preimage f).isLocalization_stalk ⟨x.val, hx⟩
  exact IsLocalization.algEquiv
    (q.asIdeal.comap (algebraMap B (finiteLocalization A B p))).primeCompl
    (X.presheaf.stalk x.val) (Localization.AtPrime q.asIdeal)

end

end HodgeConjecture.SchemeCycles
