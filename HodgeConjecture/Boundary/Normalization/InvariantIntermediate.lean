import HodgeConjecture.Boundary.Normalization.DeckAction

/-!
# Intermediate normalizations as fixed rings

For a subgroup `H` of the Galois group of `N / K`, the integral closure of
the affine base ring in the fixed field `N^H` is canonically the `H`-fixed
subalgebra of the integral closure in `N`.

The final specialization identifies the marked intermediate normalization
with the fixed ring for `NormalClosureData.intermediateFixingSubgroup`.
This supplies the invariant-ring model underlying the affine quotient
morphism that was previously implicit in the normalization triangle; no
scheme-level quotient universal property is asserted.  No unramifiedness or
purity hypothesis is used.

Mathematical references: Stacks Project, Tags `035J` and `035K` for
functoriality of relative normalization and compatibility with restriction
to opens; Tag `0BRH` for compatibility of finite-group invariants with flat
base change.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture

noncomputable section

universe u

namespace NormalizationInertia

section FixedRings

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- The Galois action on `N` restricts to `B`-algebra automorphisms of its
integral closure over `B`. -/
def normalClosureNormalizationRingActionHom :
    (N ≃ₐ[K] N) →*
      (NormalClosureNormalizationRing (B := B) (N := N) ≃ₐ[B]
        NormalClosureNormalizationRing (B := B) (N := N)) where
  toFun := normalClosureNormalizationRingEquiv (B := B)
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- The canonical semiring action of the normal-closure Galois group on the
normalization ring. -/
noncomputable instance normalClosureNormalizationRingMulSemiringAction :
    MulSemiringAction (N ≃ₐ[K] N)
      (NormalClosureNormalizationRing (B := B) (N := N)) :=
  MulSemiringAction.compHom _
    (normalClosureNormalizationRingActionHom
      (B := B) (K := K) (N := N))

/-- Every normal-closure automorphism fixes the affine base scalars. -/
instance normalClosureNormalizationRingSMulCommClass :
    SMulCommClass (N ≃ₐ[K] N) B
      (NormalClosureNormalizationRing (B := B) (N := N)) where
  smul_comm σ b x := by
    change
      (normalClosureNormalizationRingActionHom
        (B := B) (K := K) (N := N) σ) (b • x) =
        b • (normalClosureNormalizationRingActionHom
          (B := B) (K := K) (N := N) σ) x
    exact map_smul
      (normalClosureNormalizationRingActionHom
        (B := B) (K := K) (N := N) σ) b x

/-- The `H`-fixed subalgebra of the normal-closure normalization ring. -/
abbrev FixedSubgroupNormalizationRing
    (H : Subgroup (N ≃ₐ[K] N)) :=
  FixedPoints.subalgebra B
    (NormalClosureNormalizationRing (B := B) (N := N)) H

/-- Inclusion of the normalization in the fixed field into the fixed
subalgebra of the normal-closure normalization. -/
def fixedFieldNormalizationToFixedRing
    (H : Subgroup (N ≃ₐ[K] N)) :
    integralClosure B (IntermediateField.fixedField H) →ₐ[B]
      FixedSubgroupNormalizationRing (B := B) H where
  toFun x :=
    ⟨⟨(x.1 : N),
      x.property.map
        ((IntermediateField.fixedField H).val.restrictScalars B)⟩,
      by
        intro h
        apply Subtype.ext
        change h.1 (x.1 : N) = (x.1 : N)
        exact
          (IntermediateField.mem_fixedField_iff
            (H := H) (x.1 : N)).mp x.1.property h.1 h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Integral closure commutes with passing from the normal closure to a fixed
field: `IntCl_B(N^H) ≃ (IntCl_B N)^H`. -/
def fixedFieldNormalizationEquivFixedRing
    (H : Subgroup (N ≃ₐ[K] N)) :
    integralClosure B (IntermediateField.fixedField H) ≃ₐ[B]
      FixedSubgroupNormalizationRing (B := B) H :=
  AlgEquiv.ofBijective
    (fixedFieldNormalizationToFixedRing (B := B) H) ⟨by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact
        congrArg
          (fun z =>
            ((z.1 :
              NormalClosureNormalizationRing (B := B) (N := N)) : N))
          hxy, by
      intro y
      let z : IntermediateField.fixedField H :=
        ⟨(y.1 : N), by
          rw [IntermediateField.mem_fixedField_iff]
          intro σ hσ
          have hy := y.property (⟨σ, hσ⟩ : H)
          change σ (y.1 : N) = (y.1 : N)
          exact congrArg Subtype.val hy⟩
      have hzIntegral : IsIntegral B z := by
        apply
          (isIntegral_algHom_iff
            ((IntermediateField.fixedField H).val.restrictScalars B)
            (IntermediateField.fixedField H).val.injective).mp
        exact y.1.property
      refine ⟨⟨z, hzIntegral⟩, ?_⟩
      rfl⟩

/-- For a marked finite extension, its intermediate normalization is the
fixed ring of the subgroup fixing the marked copy of `L`. -/
def intermediateNormalizationEquivFixedRing
    [PerfectField K]
    (D : CollisionFoundations.NormalClosureData K L N) :
    IntermediateNormalizationRing (B := B) (L := L) ≃ₐ[B]
      FixedSubgroupNormalizationRing
        (B := B) D.intermediateFixingSubgroup :=
  (((AlgEquiv.ofInjectiveField D.embedding).restrictScalars B).trans
      ((IntermediateField.equivOfEq
        D.fixedField_intermediateFixingSubgroup).symm.restrictScalars B)).mapIntegralClosure.trans
    (fixedFieldNormalizationEquivFixedRing
      (B := B) D.intermediateFixingSubgroup)

@[simp]
theorem intermediateNormalizationEquivFixedRing_coe
    [PerfectField K]
    (D : CollisionFoundations.NormalClosureData K L N)
    (x : IntermediateNormalizationRing (B := B) (L := L)) :
    (((intermediateNormalizationEquivFixedRing (B := B) D x :
        FixedSubgroupNormalizationRing
          (B := B) D.intermediateFixingSubgroup) :
      NormalClosureNormalizationRing (B := B) (N := N)) : N) =
      D.embedding (x : L) :=
  rfl

end FixedRings

end NormalizationInertia

end

end HodgeConjecture
