module

public import HodgeConjecture.Cycles.FiniteFlatPrincipalDivisor

@[expose] public section

/-! Preservation of the existing principal-relation span by the original
finite flat fiber pullback, proved using actual closed carriers. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

/-- Each original principal relation pulls back to a finite sum of genuine principal
relations on actual integral closed source carriers. -/
theorem gradedFiniteFiberPullback_principalRelation_mem
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ)
    (d : PrincipalRelationData (DimensionFunction.ofLocallyOfFiniteType k Y pY) n) :
    gradedFiniteFiberPullback f k ℤ pY n
        (principalRelation (DimensionFunction.ofLocallyOfFiniteType k Y pY) n d) ∈
      principalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n := by
  classical
  let δX := DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)
  let δY := DimensionFunction.ofLocallyOfFiniteType k Y pY
  let W := d.1.val
  letI := W.property
  let P : Scheme.{u} := pullback f W.val.subschemeι
  let iX : P ⟶ X := pullback.fst f W.val.subschemeι
  let q : P ⟶ W.val.subscheme := pullback.snd f W.val.subschemeι
  let pW := W.val.subschemeι ≫ pY
  letI : IsNoetherian P := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian iX
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace iX }
  letI : Fintype (irreducibleComponents P) :=
    (finite_irreducibleComponents_of_isNoetherian (X := P)).fintype
  let carrier (V : irreducibleComponents P) := pointSupport P V.2.1.genericPoint
  let image (V : irreducibleComponents P) := closedImageSubscheme iX (carrier V)
  have hdegree (V : irreducibleComponents P) : supportDegree δX (image V) = n + 1 := by
    rw [supportDegree_closedImageSubscheme, ambientGenericPoint_pointSupport]
    change δX (iX.base V.2.1.genericPoint) = n + 1
    dsimp only [δX]
    rw [DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k pY f]
    have hpt : f.base (iX.base V.2.1.genericPoint) =
        W.val.subschemeι.base (genericPoint W.val.subscheme) := by
      have h := congrArg (fun m : P ⟶ Y ↦ m.base V.2.1.genericPoint)
        (pullback.condition (f := f) (g := W.val.subschemeι))
      change f.base (iX.base V.2.1.genericPoint) =
        W.val.subschemeι.base (q.base V.2.1.genericPoint) at h
      rwa [map_genericPoint_irreducibleComponent_eq_genericPoint q V] at h
    rw [hpt]
    exact d.1.property
  let function (V : irreducibleComponents P) :
      letI := (image V).property
      (image V).val.subscheme.functionFieldˣ := by
    letI := (carrier V).property
    letI := (image V).property
    letI : IsIntegral ((carrier V).val.map iX).subscheme :=
      closedImageSubscheme_isIntegral iX (carrier V)
    exact Units.map (functionFieldEquiv (closedImageSubschemeIso iX (carrier V))).symm.toMonoidHom
      (Units.map (flatComponentFunctionFieldMap q V).hom.toMonoidHom d.2)
  let data (V : irreducibleComponents P) : PrincipalRelationData δX n :=
    ⟨⟨image V, hdegree V⟩, function V⟩
  let e : cyclesOfDegree ℤ δX n := ∑ V : irreducibleComponents P,
    (finiteFiberMultiplicity q V.2.1.genericPoint : ℤ) • principalRelation δX n (data V)
  have he : e ∈ principalRelations δX n := by
    apply Submodule.sum_mem
    intro V _
    exact Submodule.smul_mem _ _ (principalRelation_mem δX n (data V))
  have hval :
      (gradedFiniteFiberPullback f k ℤ pY n (principalRelation δY n d)).val = e.val := by
    change finiteFiberPullback f ℤ (ambientPrincipalDivisor W d.2) = _
    rw [ambientPrincipalDivisor_eq, finiteFiberPullback_closedImmersionPushforward,
      finiteFlat_pullback_principalDivisor_eq_sum_components k pW q]
    change closedImmersionPushforward ℤ iX
        (∑ᶠ V : irreducibleComponents P,
          (finiteFiberMultiplicity q V.2.1.genericPoint : ℤ) •
            flatComponentPrincipalDivisor q V d.2) = e.val
    dsimp only [e]
    rw [finsum_eq_sum_of_fintype, map_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul, principalRelation_coe]
    apply Finset.sum_congr rfl
    intro V _
    rw [map_smul]
    change (finiteFiberMultiplicity q V.2.1.genericPoint : ℤ) •
        closedImmersionPushforward ℤ iX
          (ambientPrincipalDivisor (carrier V)
            (Units.map (flatComponentFunctionFieldMap q V).hom.toMonoidHom d.2)) = _
    rw [closedImmersionPushforward_ambientPrincipalDivisor]
  exact (Subtype.ext hval).symm ▸ he

/-- The original graded finite flat pullback preserves the original relation span. -/
theorem principalRelations_le_comap_finiteFlatPullback
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (n : ℤ) :
    principalRelations (DimensionFunction.ofLocallyOfFiniteType k Y pY) n ≤
      (principalRelations (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n).comap
        (gradedFiniteFiberPullback f k ℤ pY n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact gradedFiniteFiberPullback_principalRelation_mem k pY f n d

end

end HodgeConjecture.SchemeCycles
