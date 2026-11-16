module

public import HodgeConjecture.Cycles.PrincipalRelationOfDivisor

/-!
# Top-degree rational equivalence on an integral scheme

When the relation carrier has the ambient generic degree, it is the whole
integral scheme. Thus a finite sum of the original carrier relations is a
single principal divisor of an actual rational function on the ambient
scheme. This statement uses the existing Chow relation submodule.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- In degree one below the generic degree, the original finite-sum
relation subgroup consists exactly of ambient principal divisors. -/
theorem mem_principalRelations_iff_exists_ambientPrincipalDivisor
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ)
    (hn : δ (genericPoint X) - 1 = n)
    (c : cyclesOfDegree ℤ δ n) :
    c ∈ principalRelations δ n ↔
      ∃ f : X.functionFieldˣ, (c : Cycles X ℤ) = principalDivisor X f := by
  constructor
  · intro hc
    obtain ⟨l, hl⟩ := (mem_principalRelations_iff_exists_list δ n c).mp hc
    have hsingle : ∀ d : PrincipalRelationData δ n,
        ∃ f : X.functionFieldˣ,
          ((principalRelation δ n d : cyclesOfDegree ℤ δ n) : Cycles X ℤ) =
            principalDivisor X f := by
      intro d
      let W := d.1.val
      have hW : supportDegree δ W = δ (genericPoint X) := by
        have hd := d.1.property
        dsimp only [W] at hd ⊢
        omega
      letI := W.property
      obtain ⟨f, hf⟩ :=
        exists_ambientPrincipalDivisor_eq_principalDivisor δ W hW d.2
      exact ⟨f, hf⟩
    have hlist : ∀ l : List (PrincipalRelationData δ n),
        ∃ f : X.functionFieldˣ,
          (((l.map (principalRelation δ n)).sum : cyclesOfDegree ℤ δ n) :
            Cycles X ℤ) = principalDivisor X f := by
      intro l
      induction l with
      | nil =>
          exact ⟨1, by simp⟩
      | cons d l ih =>
          obtain ⟨f, hf⟩ := hsingle d
          obtain ⟨g, hg⟩ := ih
          refine ⟨f * g, ?_⟩
          change (principalRelation δ n d).val +
              ((l.map (principalRelation δ n)).sum).val =
                principalDivisor X (f * g)
          rw [hf, hg, principalDivisor_mul]
    obtain ⟨f, hf⟩ := hlist l
    exact ⟨f, hl ▸ hf⟩
  · rintro ⟨f, hf⟩
    have hmem := principalDivisor_mem_principalRelations_of_genericDegree_eq
      X δ f n hn
    have hceq : c =
        (⟨principalDivisor X f, by
          simpa only [hn] using principalDivisor_mem_cyclesOfDegree δ f⟩ :
          cyclesOfDegree ℤ δ n) := Subtype.ext hf
    exact hceq ▸ hmem

end

end HodgeConjecture.SchemeCycles

end
