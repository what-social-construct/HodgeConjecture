module

public import HodgeConjecture.Cycles.PrincipalRelations
public import HodgeConjecture.Cycles.PrincipalDivisorTransport

@[expose] public section

/-!
# Top-degree relation carriers in an integral ambient scheme

An integral closed carrier with the same dimension-function value as the
ambient generic point is the whole reduced ambient scheme. Its actual
closed immersion is an isomorphism. Consequently its ambient principal
divisors are actual principal divisors of the ambient scheme, with the
rational function transported through the constructed function-field
isomorphism. This reduces top-degree relation carriers without supplying
a degree or cycle-class invariance hypothesis.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Strict dimension increase along generization detects the ambient generic point. -/
theorem ambientGenericPoint_eq_genericPoint_of_supportDegree_eq
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    (hW : supportDegree δ W = δ (genericPoint X)) :
    ambientGenericPoint W = genericPoint X := by
  have hle : ambientGenericPoint W ≤ genericPoint X :=
    Scheme.le_iff_specializes.mpr (genericPoint_specializes _)
  by_contra hne
  have hnot : ¬genericPoint X ≤ ambientGenericPoint W := by
    intro hge
    exact hne (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq)
  exact (ne_of_lt (δ.strictMono (lt_iff_le_not_ge.mpr ⟨hle, hnot⟩))) hW

/-- There is no proper reduced closed carrier of the ambient generic degree. -/
theorem integralSubscheme_ideal_eq_bot_of_supportDegree_eq
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    (hW : supportDegree δ W = δ (genericPoint X)) : W.val = ⊥ := by
  have h : W = pointSupport X (genericPoint X) := by
    rw [← ambientGenericPoint_eq_genericPoint_of_supportDegree_eq δ W hW]
    exact (pointSupport_ambientGenericPoint W).symm
  rw [h, pointSupport_val]
  have hclosure : Closeds.closure ({genericPoint X} : Set X) = ⊤ :=
    SetLike.coe_injective (genericPoint_spec X).def
  rw [hclosure, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot]

/-- The original carrier immersion is an actual scheme isomorphism. -/
theorem integralSubscheme_isIso_of_supportDegree_eq
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    (hW : supportDegree δ W = δ (genericPoint X)) : IsIso W.val.subschemeι :=
  (Scheme.isIso_subschemeι_iff_eq_bot W.val).mpr
    (integralSubscheme_ideal_eq_bot_of_supportDegree_eq δ W hW)

/-- Transport through that actual isomorphism turns the carrier relation
into an actual ambient principal divisor; the function is constructed. -/
theorem exists_ambientPrincipalDivisor_eq_principalDivisor
    [IsNoetherian X] (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    (hW : supportDegree δ W = δ (genericPoint X)) :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ, ∃ g : X.functionFieldˣ,
      ambientPrincipalDivisor W f = principalDivisor X g := by
  have := W.property
  have : IsIso W.val.subschemeι := integralSubscheme_isIso_of_supportDegree_eq δ W hW
  let e := asIso W.val.subschemeι
  intro f
  let g : X.functionFieldˣ := Units.map (functionFieldEquiv e).symm.toMonoidHom f
  refine ⟨g, ?_⟩
  have hg : Units.map (functionFieldEquiv e).toMonoidHom g = f := by
    apply Units.ext
    exact (functionFieldEquiv e).apply_symm_apply (f : W.val.subscheme.functionField)
  have h := principalDivisor_iso e g
  rw [hg] at h
  exact h

end

end HodgeConjecture.SchemeCycles
