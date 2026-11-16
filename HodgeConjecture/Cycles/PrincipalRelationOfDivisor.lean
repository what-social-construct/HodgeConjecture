module

public import HodgeConjecture.Cycles.TopDegreeRelations
public import HodgeConjecture.Cycles.PrincipalDivisorDegree

/-!
# Ambient principal divisors are actual top-degree relations

The reduced closure of the ambient generic point is the whole integral
scheme. Its carrier inclusion is an isomorphism, so every principal divisor
of the ambient function field is one of the existing principal-relation
generators, after transporting its function through that isomorphism.
-/

@[expose] public section

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Every original principal divisor on an integral Noetherian scheme is
an actual relation in the homogeneous degree immediately below its
generic degree. -/
theorem principalDivisor_mem_principalRelations_of_genericDegree
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (δ : DimensionFunction X) (f : X.functionFieldˣ) :
    (⟨principalDivisor X f, principalDivisor_mem_cyclesOfDegree δ f⟩ :
      cyclesOfDegree ℤ δ (δ (genericPoint X) - 1)) ∈
        principalRelations δ (δ (genericPoint X) - 1) := by
  let W : IntegralClosedSubscheme X := pointSupport X (genericPoint X)
  have hW : supportDegree δ W = (δ (genericPoint X) - 1) + 1 := by
    simp [W, supportDegree]
  letI := W.property
  have hIso : IsIso W.val.subschemeι :=
    integralSubscheme_isIso_of_supportDegree_eq δ W (by simpa [W, supportDegree])
  let e : W.val.subscheme ≅ X := asIso W.val.subschemeι
  let g : W.val.subscheme.functionFieldˣ :=
    Units.map (functionFieldEquiv e).toMonoidHom f
  let d : PrincipalRelationData δ (δ (genericPoint X) - 1) :=
    ⟨⟨W, hW⟩, g⟩
  have hd : (principalRelation δ (δ (genericPoint X) - 1) d).val =
      principalDivisor X f := by
    change closedImmersionPushforward ℤ e.hom (principalDivisor W.val.subscheme g) =
      principalDivisor X f
    exact principalDivisor_iso e f
  have hdeq : principalRelation δ (δ (genericPoint X) - 1) d =
      (⟨principalDivisor X f, principalDivisor_mem_cyclesOfDegree δ f⟩ :
        cyclesOfDegree ℤ δ (δ (genericPoint X) - 1)) :=
    Subtype.ext hd
  exact hdeq ▸ principalRelation_mem δ (δ (genericPoint X) - 1) d

/-- The ambient relation at an explicitly identified homogeneous degree. -/
theorem principalDivisor_mem_principalRelations_of_genericDegree_eq
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (δ : DimensionFunction X) (f : X.functionFieldˣ) (n : ℤ)
    (hn : δ (genericPoint X) - 1 = n) :
    (⟨principalDivisor X f, by
      simpa only [hn] using principalDivisor_mem_cyclesOfDegree δ f⟩ :
      cyclesOfDegree ℤ δ n) ∈ principalRelations δ n := by
  subst n
  exact principalDivisor_mem_principalRelations_of_genericDegree X δ f

end

end HodgeConjecture.SchemeCycles

end
