module

public import HodgeConjecture.Realization.Chow.Examples.SplitCycleMultiplicity
public import HodgeConjecture.Cycles.FiniteFlatChowPullback
public import HodgeConjecture.Cycles.RationalFiniteChowPushforward
public import HodgeConjecture.Cycles.FiberMultiplicityLocal

@[expose] public section

/-!
# Ordinary Chow groups of finite split schemes

Every actual integral closed support has dimension zero. Thus the ordinary
degree-zero cycle submodule is the entire original cycle module, and its
ordinary principal-relation index is empty. The resulting comparison with
the existing split Chow quotient retains the identical cycle representatives.
The original finite Chow maps agree with the split maps, by their actual
local fiber lengths and support-to-image degrees.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitZeroCycles

open AlgebraicGeometry CategoryTheory SplitPointGeometry

noncomputable section

universe u

variable (K : Type u) [Field K] (I : Type u) [Finite I]

instance splitScheme_isNoetherian : IsNoetherian (scheme K I) := by
  dsimp [scheme]
  infer_instance

/-- The ordinary structural grading, with its original residue-field definition. -/
abbrev ordinaryDimensionFunction :=
  SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) (toBase K I)

/-- The ordinary rational Chow group of the actual split finite scheme. -/
abbrev OrdinaryChow := SchemeCycles.RationalChowGroup (ordinaryDimensionFunction K I) 0

variable (p : scheme K I ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]

/-- Every original integral support is in ordinary structural degree zero. -/
theorem ordinarySupportDegree_eq_zero (W : SchemeCycles.IntegralClosedSubscheme (scheme K I)) :
    SchemeCycles.supportDegree
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) W = 0 := by
  exact (SchemeCycles.supportDegree_ofLocallyOfFiniteType_eq_iff K (scheme K I) p W 0).mpr
    (integralClosedSubscheme_dimension K I W)

/-- Forgetting the degree-zero proof retains exactly the same actual cycles. -/
def ordinaryCyclesEquiv :
    SchemeCycles.cyclesOfDegree ℚ
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0 ≃ₗ[ℚ]
        Cycles K I ℚ where
  toFun c := c.val
  invFun c := ⟨c, (SchemeCycles.mem_cyclesOfDegree_iff ℚ _ 0 c).mpr
    (fun W _ ↦ ordinarySupportDegree_eq_zero K I p W)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- No actual degree-one carrier exists to generate ordinary zero-cycle relations. -/
instance ordinaryPrincipalRelationData_isEmpty : IsEmpty
    (SchemeCycles.PrincipalRelationData
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0) := by
  refine ⟨fun d ↦ ?_⟩
  have h := d.1.property
  rw [ordinarySupportDegree_eq_zero K I p] at h
  norm_num at h

theorem ordinaryRationalPrincipalRelations_eq_bot :
    SchemeCycles.rationalPrincipalRelations
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0 = ⊥ := by
  simp only [SchemeCycles.rationalPrincipalRelations, Set.range_eq_empty,
    Submodule.span_empty]

/-- The ordinary and split Chow quotients identify through identical representatives.
Allowing an explicit structure map keeps the source of the original finite maps exact. -/
def ordinaryChowEquivOfStructure :
    SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0 ≃ₗ[ℚ]
        Chow K I ℚ :=
  ((SchemeCycles.rationalPrincipalRelations
    (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0).quotEquivOfEqBot
      (ordinaryRationalPrincipalRelations_eq_bot K I p)).trans
    ((ordinaryCyclesEquiv K I p).trans (chowEquivCycles K I ℚ).symm)

@[simp]
theorem ordinaryChowEquivOfStructure_rationalClassMap
    (c : SchemeCycles.cyclesOfDegree ℚ
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0) :
    ordinaryChowEquivOfStructure K I p
      (SchemeCycles.rationalClassMap _ 0 c) = classMap K I ℚ c.val := rfl

/-- The canonical comparison for the original split structure map. -/
def ordinaryChowEquiv : OrdinaryChow K I ≃ₗ[ℚ] Chow K I ℚ :=
  ordinaryChowEquivOfStructure K I (toBase K I)

@[simp]
theorem ordinaryChowEquiv_rationalClassMap
    (c : SchemeCycles.cyclesOfDegree ℚ (ordinaryDimensionFunction K I) 0) :
    ordinaryChowEquiv K I (SchemeCycles.rationalClassMap _ 0 c) =
      classMap K I ℚ c.val := rfl

/-- Change the structural grading through the identical actual cycle representatives. -/
def ordinaryChangeStructure : OrdinaryChow K I ≃ₗ[ℚ]
    SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0 :=
  (ordinaryChowEquiv K I).trans (ordinaryChowEquivOfStructure K I p).symm

@[simp]
theorem ordinaryChowEquivOfStructure_changeStructure (z : OrdinaryChow K I) :
    ordinaryChowEquivOfStructure K I p (ordinaryChangeStructure K I p z) =
      ordinaryChowEquiv K I z :=
  (ordinaryChowEquivOfStructure K I p).apply_symm_apply _

@[simp]
theorem ordinaryChangeStructure_rationalClassMap
    (c : SchemeCycles.cyclesOfDegree ℚ (ordinaryDimensionFunction K I) 0) :
    ordinaryChangeStructure K I p (SchemeCycles.rationalClassMap _ 0 c) =
      SchemeCycles.rationalClassMap _ 0
        ⟨c.val, (SchemeCycles.mem_cyclesOfDegree_iff ℚ _ 0 c.val).mpr
          (fun W _ ↦ ordinarySupportDegree_eq_zero K I p W)⟩ := by
  apply (ordinaryChowEquivOfStructure K I p).injective
  rw [ordinaryChowEquivOfStructure_changeStructure,
    ordinaryChowEquiv_rationalClassMap,
    ordinaryChowEquivOfStructure_rationalClassMap]

/-- The class of the actual reduced point, in the original ordinary Chow quotient. -/
def ordinaryPointClass (i : I) : OrdinaryChow K I :=
  SchemeCycles.rationalClassMap _ 0 ⟨pointCycle K I ℚ i,
    SchemeCycles.single_mem_cyclesOfDegree ℚ (ordinaryDimensionFunction K I) 0
      (pointIntegralSubscheme K I i) 1
      (ordinarySupportDegree_eq_zero K I (toBase K I) _)⟩

@[simp]
theorem ordinaryChowEquiv_ordinaryPointClass (i : I) :
    ordinaryChowEquiv K I (ordinaryPointClass K I i) =
      classMap K I ℚ (pointCycle K I ℚ i) := rfl

variable {I} {S : Type u} [Finite S]

/-- The original finite pushforward uses the same scheme-theoretic images,
and every support-to-image morphism has actual degree one. -/
theorem finitePushforward_eq_split (f : S → I) :
    SchemeCycles.finitePushforward ℚ (mapOfFunction K f) = pushforward K ℚ f := by
  apply Finsupp.lhom_ext
  intro W r
  rw [SchemeCycles.finitePushforward_single,
    SchemeCycles.finitePushforwardDegree_of_isClosedImmersion]
  change r • (1 • Finsupp.single (SchemeCycles.imageSubscheme (mapOfFunction K f) W) 1) = _
  have himage : SchemeCycles.imageSubscheme (mapOfFunction K f) W =
      imageIntegralSubscheme K f W := Subtype.ext rfl
  simp [himage, pushforward]

/-- The ordinary multiplicity is computed from the actual fiber stalk.
The local quotient formula reduces it to the length of a field. -/
theorem finiteFiberMultiplicity_eq_one (f : S → I) (x : scheme K S) :
    SchemeCycles.finiteFiberMultiplicity (mapOfFunction K f) x = 1 := by
  letI := (stalk_isField K S x).toField
  letI := (stalk_isField K I ((mapOfFunction K f).base x)).toField
  rw [SchemeCycles.finiteFiberMultiplicity_eq_length_quotient,
    IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot,
    (AlgEquiv.quotientBot ((scheme K S).presheaf.stalk x)
      ((scheme K S).presheaf.stalk x)).toLinearEquiv.length_eq,
    Module.length_eq_one]
  rfl

/-- The original finite-fiber pullback is the existing split cycle pullback. -/
theorem finiteFiberPullback_eq_split (f : S → I) :
    SchemeCycles.finiteFiberPullback (mapOfFunction K f) ℚ = pullback K ℚ f := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro W
  rw [SchemeCycles.finiteFiberPullback_apply, finiteFiberMultiplicity_eq_one,
    Nat.cast_one, mul_one]
  have himage : SchemeCycles.pointSupport (scheme K I)
      ((mapOfFunction K f).base (SchemeCycles.ambientGenericPoint W)) =
        imageIntegralSubscheme K f W := by
    rw [← SchemeCycles.imageSubscheme_eq_pointSupport]
    exact Subtype.ext rfl
  rw [himage]
  obtain ⟨s, hs⟩ := (labelEquivIntegralClosedSubscheme K S).surjective W
  subst W
  change c (imageIntegralSubscheme K f (pointIntegralSubscheme K S s)) = _
  rw [imageIntegralSubscheme_point]
  exact (coordinates_pullback K ℚ f c s).symm

/-- The pushforward square for the original ordinary finite Chow map. -/
theorem ordinaryChowEquivOfStructure_finitePushforward (f : S → I)
    (z : SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K S)
        (mapOfFunction K f ≫ p)) 0) :
    ordinaryChowEquivOfStructure K I p
      (SchemeCycles.rationalChowFinitePushforward K p (mapOfFunction K f) 0 z) =
        chowPushforward K ℚ f
          (ordinaryChowEquivOfStructure K S (mapOfFunction K f ≫ p) z) := by
  obtain ⟨c, rfl⟩ := SchemeCycles.rationalClassMap_surjective _ 0 z
  rw [SchemeCycles.rationalChowFinitePushforward_classMap,
    ordinaryChowEquivOfStructure_rationalClassMap,
    ordinaryChowEquivOfStructure_rationalClassMap, chowPushforward_classMap]
  congr 1
  exact LinearMap.congr_fun (finitePushforward_eq_split K f) c.val

/-- The pullback square for the original ordinary finite flat Chow map. -/
theorem ordinaryChowEquivOfStructure_finiteFlatPullback (f : S → I)
    (z : SchemeCycles.RationalChowGroup
      (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType K (scheme K I) p) 0) :
    ordinaryChowEquivOfStructure K S (mapOfFunction K f ≫ p)
      (SchemeCycles.rationalChowFiniteFlatPullback K p (mapOfFunction K f) 0 z) =
        chowPullback K ℚ f (ordinaryChowEquivOfStructure K I p z) := by
  obtain ⟨c, rfl⟩ := SchemeCycles.rationalClassMap_surjective _ 0 z
  rw [SchemeCycles.rationalChowFiniteFlatPullback_classMap,
    ordinaryChowEquivOfStructure_rationalClassMap,
    ordinaryChowEquivOfStructure_rationalClassMap, chowPullback_classMap]
  congr 1
  exact LinearMap.congr_fun (finiteFiberPullback_eq_split K f) c.val

omit p in
/-- The original finite Chow pushforward, preceded only by the comparison
of the source structural gradings through identical cycle representatives. -/
def ordinaryChowPushforward (f : S → I) : OrdinaryChow K S →ₗ[ℚ] OrdinaryChow K I :=
  (SchemeCycles.rationalChowFinitePushforward K (toBase K I) (mapOfFunction K f) 0).comp
    (ordinaryChangeStructure K S (mapOfFunction K f ≫ toBase K I)).toLinearMap

omit p in
/-- The original finite flat Chow pullback, followed only by that same
identity on actual representatives in the source structural grading. -/
def ordinaryChowPullback (f : S → I) : OrdinaryChow K I →ₗ[ℚ] OrdinaryChow K S :=
  (ordinaryChangeStructure K S (mapOfFunction K f ≫ toBase K I)).symm.toLinearMap.comp
    (SchemeCycles.rationalChowFiniteFlatPullback K (toBase K I) (mapOfFunction K f) 0)

omit p in
theorem ordinaryChowEquiv_pushforward (f : S → I) (z : OrdinaryChow K S) :
    ordinaryChowEquiv K I (ordinaryChowPushforward K f z) =
      chowPushforward K ℚ f (ordinaryChowEquiv K S z) := by
  change ordinaryChowEquivOfStructure K I (toBase K I)
    (SchemeCycles.rationalChowFinitePushforward K (toBase K I) (mapOfFunction K f) 0
      (ordinaryChangeStructure K S (mapOfFunction K f ≫ toBase K I) z)) = _
  rw [ordinaryChowEquivOfStructure_finitePushforward,
    ordinaryChowEquivOfStructure_changeStructure]

omit p in
theorem ordinaryChowEquiv_pullback (f : S → I) (z : OrdinaryChow K I) :
    ordinaryChowEquiv K S (ordinaryChowPullback K f z) =
      chowPullback K ℚ f (ordinaryChowEquiv K I z) := by
  change ordinaryChowEquiv K S
    ((ordinaryChowEquiv K S).symm
      (ordinaryChowEquivOfStructure K S (mapOfFunction K f ≫ toBase K I)
        (SchemeCycles.rationalChowFiniteFlatPullback K (toBase K I) (mapOfFunction K f) 0 z))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ordinaryChowEquivOfStructure_finiteFlatPullback K (toBase K I) f z

end

end HodgeConjecture.SplitZeroCycles
