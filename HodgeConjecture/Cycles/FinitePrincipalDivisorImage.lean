import HodgeConjecture.Cycles.FinitePrincipalDivisor
import HodgeConjecture.Cycles.FinitePushforwardSquare
import HodgeConjecture.Cycles.PrincipalRelations

/-!
# Norms on the actual image carriers of principal relations

An actual integral closed carrier maps finitely and dominantly to its
scheme-theoretic image. Its function-field norm constructs the target
function. The proved principal-divisor identity and the closed-carrier
square identify the ambient cycles. This is the finite specialization of
Stacks 02RT: https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Norm along the actual finite support-to-image morphism. -/
def finiteImageNorm (W : IntegralClosedSubscheme X) [IsFinite (W.val.subschemeι ≫ f)] :
    letI := W.property
    letI := (imageSubscheme f W).property
    W.val.subscheme.functionFieldˣ →* (imageSubscheme f W).val.subscheme.functionFieldˣ := by
  letI := W.property
  letI := (imageSubscheme f W).property
  letI : IsIntegral (W.val.subschemeι ≫ f).image := (imageSubscheme f W).property
  letI := finiteImage_toImage_isFinite f W
  exact functionFieldNorm (W.val.subschemeι ≫ f).toImage

/-- Finite pushforward sends a carrier principal divisor to the principal divisor
of its constructed norm on the actual image carrier. -/
theorem finitePushforward_ambientPrincipalDivisor
    (k : Type u) [Field k] [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    [IsFinite f] (W : IntegralClosedSubscheme X) :
    letI := W.property
    letI := (imageSubscheme f W).property
    ∀ g : W.val.subscheme.functionFieldˣ,
      finitePushforward ℤ f (ambientPrincipalDivisor W g) =
        ambientPrincipalDivisor (imageSubscheme f W) (finiteImageNorm f W g) := by
  letI := W.property
  letI := (imageSubscheme f W).property
  letI : IsIntegral (W.val.subschemeι ≫ f).image := (imageSubscheme f W).property
  letI := finiteImage_toImage_isFinite f W
  intro g
  rw [ambientPrincipalDivisor_eq, ambientPrincipalDivisor_eq]
  have hs := LinearMap.congr_fun
    (finitePushforward_closedImmersion_square ℤ W.val.subschemeι
      (W.val.subschemeι ≫ f).imageι f (W.val.subschemeι ≫ f).toImage
      (Scheme.Hom.toImage_imageι _).symm) (principalDivisor W.val.subscheme g)
  change finitePushforward ℤ f
      (closedImmersionPushforward ℤ W.val.subschemeι (principalDivisor W.val.subscheme g)) =
    closedImmersionPushforward ℤ (W.val.subschemeι ≫ f).imageι
      (principalDivisor (W.val.subschemeι ≫ f).image
        (functionFieldNorm (W.val.subschemeι ≫ f).toImage g))
  simpa only [LinearMap.comp_apply,
    finitePushforward_principalDivisor k ((W.val.subschemeι ≫ f).imageι ≫ pY)] using hs

end

end HodgeConjecture.SchemeCycles
