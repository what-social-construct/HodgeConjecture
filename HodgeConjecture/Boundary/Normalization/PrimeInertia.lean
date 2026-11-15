module

public import HodgeConjecture.Boundary.Normalization.FixedRingUnramified
public import HodgeConjecture.Boundary.Normalization.InvariantIntermediate
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

/-!
# Prime inertia and the valuation-inertia comparison

Stacks Project Tag `0BST` uses the ring-theoretic inertia group at a prime
`Q`: the subgroup of the stabilizer of `Q` acting trivially on the residue
field.  The normalization diagram in this project instead starts with the
inertia group of a centered valuation.  This module keeps those groups
distinct and proves the comparison supplied by the current centeredness
hypothesis:

`valuation inertia ≤ prime inertia`.

The reverse containment is not asserted in this module.  It needs a stronger
local realization identifying the centered valuation ring with the
localization at `Q`; `LocalizationBridge.lean` constructs that realization
over a Noetherian base.  Without such an input, a sheet condition for
valuation inertia does not by itself imply the prime-inertia containment
required by `0BST`.

The source ring in `0BST` is the full invariant ring.  We therefore also
name that ring, package the exact unramifiedness conclusion as a proposition,
and, for marked finite normal-closure data over a perfect fraction field,
identify it with an integrally closed affine base.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture

noncomputable section

universe u

namespace NormalizationInertia

open scoped Pointwise

section AbstractPrimeInertia

variable {A S G : Type*}
variable [CommRing A] [CommRing S] [Algebra A S]
variable [Group G] [MulSemiringAction G S] [SMulCommClass G A S]

/-- The ring-theoretic inertia group at `Q`: elements stabilizing `Q` whose
induced action on `S / Q` is the identity. -/
noncomputable def primeInertiaSubgroup
    (Q : Ideal S) [Q.IsPrime] : Subgroup G :=
  (MonoidHom.ker
    (Ideal.Quotient.stabilizerHom Q (Q.under A) G)).map
      (MulAction.stabilizer G Q).subtype

/-- Prime inertia is contained in the decomposition group (the stabilizer of
the selected prime). -/
theorem primeInertiaSubgroup_le_stabilizer
    (Q : Ideal S) [Q.IsPrime] :
    primeInertiaSubgroup (A := A) Q ≤ MulAction.stabilizer G Q :=
  Subgroup.map_subtype_le _

/-- A prime is the unique prime above its contraction to the fixed ring of
its own prime-inertia subgroup. -/
theorem eq_of_under_primeInertiaSubgroup_eq
    [Finite G]
    (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    (hunder :
      Q'.under
          (FixedPoints.subalgebra A S
            (primeInertiaSubgroup (A := A) (G := G) Q)) =
        Q.under
          (FixedPoints.subalgebra A S
            (primeInertiaSubgroup (A := A) (G := G) Q))) :
    Q' = Q := by
  let I := primeInertiaSubgroup (A := A) (G := G) Q
  let SI := FixedPoints.subalgebra A S I
  letI : SMulCommClass I SI S := by
    constructor
    intro g a x
    change g.1 • ((a : S) * x) = (a : S) * (g.1 • x)
    rw [smul_mul']
    congr 1
    exact a.property g
  letI : Algebra.IsInvariant SI S I := by
    constructor
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq SI S I Q Q' hunder.symm
  have hgmem : (g : G) ∈
      primeInertiaSubgroup (A := A) (G := G) Q := by
    simpa only [I] using g.property
  have hfix : (g : G) • Q = Q :=
    primeInertiaSubgroup_le_stabilizer (A := A) (G := G) Q hgmem
  exact hg.trans hfix

/-- Membership in prime inertia is equivalent to stabilizing the prime and
acting trivially modulo it. -/
theorem mem_primeInertiaSubgroup_iff
    (Q : Ideal S) [Q.IsPrime] (g : G) :
    g ∈ primeInertiaSubgroup (A := A) Q ↔
      g • Q = Q ∧ ∀ x : S, g • x - x ∈ Q := by
  constructor
  · intro hg
    rw [primeInertiaSubgroup, Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hstab : (h : G) • Q = Q := h.property
    refine ⟨hstab, ?_⟩
    intro x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub]
    change
      (Ideal.Quotient.stabilizerHom Q (Q.under A) G h)
          (Ideal.Quotient.mk Q x) -
        Ideal.Quotient.mk Q x = 0
    rw [(MonoidHom.mem_ker.mp hh)]
    exact sub_self _
  · rintro ⟨hstab, hres⟩
    let h : MulAction.stabilizer G Q := ⟨g, hstab⟩
    rw [primeInertiaSubgroup, Subgroup.mem_map]
    refine ⟨h, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (g • x) = Ideal.Quotient.mk Q x
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hres x

/-- It is enough to check all action differences modulo `Q`: stability of
`Q` follows automatically by applying the same condition to inverses. -/
theorem mem_primeInertiaSubgroup_of_smul_sub_mem
    (Q : Ideal S) [Q.IsPrime] (g : G)
    (hres : ∀ x : S, g • x - x ∈ Q) :
    g ∈ primeInertiaSubgroup (A := A) Q := by
  rw [mem_primeInertiaSubgroup_iff]
  refine ⟨?_, hres⟩
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    have hdifference := hres (g⁻¹ • x)
    rw [smul_inv_smul] at hdifference
    exact
      (sub_add_cancel x (g⁻¹ • x)) ▸
        Q.add_mem hdifference hx
  · intro hx
    have hdifference := hres (g⁻¹ • x)
    rw [smul_inv_smul] at hdifference
    have hmem := Q.sub_mem hx hdifference
    simpa only [sub_sub_cancel] using hmem

/-- The stabilizer-kernel definition of prime inertia agrees with Mathlib's
ideal-theoretic inertia subgroup. This identifies the subgroup in Stacks
Project Tag `0BST`; it does not supply that tag's étaleness theorem. -/
theorem primeInertiaSubgroup_eq_inertia
    (Q : Ideal S) [Q.IsPrime] :
    primeInertiaSubgroup (A := A) Q = Q.inertia G := by
  ext g
  rw [Ideal.mem_inertia]
  constructor
  · intro hg
    exact ((mem_primeInertiaSubgroup_iff (A := A) Q g).mp hg).2
  · exact mem_primeInertiaSubgroup_of_smul_sub_mem (A := A) Q g

end AbstractPrimeInertia

section NormalizationPrimeInertia

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- The full Galois-invariant subring of the normal-closure normalization.
This, rather than an arbitrary affine base `B`, is the literal source ring in
Stacks Project Tag `0BST`. -/
abbrev FullInvariantNormalizationRing :=
  FixedPoints.subalgebra B
    (NormalClosureNormalizationRing (B := B) (N := N))
    (⊤ : Subgroup (N ≃ₐ[K] N))

/-- Elements of the full invariant ring commute with the Galois action on
the normalization ring because every such element is fixed. -/
instance fullInvariantNormalizationRingSMulCommClass :
    SMulCommClass (N ≃ₐ[K] N)
      (FullInvariantNormalizationRing (B := B) (K := K) (N := N))
      (NormalClosureNormalizationRing (B := B) (N := N)) where
  smul_comm σ a x := by
    change σ • ((a : NormalClosureNormalizationRing (B := B) (N := N)) * x) =
      (a : NormalClosureNormalizationRing (B := B) (N := N)) * (σ • x)
    rw [smul_mul']
    have ha := a.property ⟨σ, Subgroup.mem_top σ⟩
    change σ • (a : NormalClosureNormalizationRing (B := B) (N := N)) =
      (a : NormalClosureNormalizationRing (B := B) (N := N)) at ha
    rw [ha]

/-- Prime inertia for the normal-closure normalization, based at the full
invariant ring as in Tag `0BST`. -/
abbrev normalizationPrimeInertiaGroup
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] : Subgroup (N ≃ₐ[K] N) :=
  primeInertiaSubgroup
    (A := FullInvariantNormalizationRing (B := B) (K := K) (N := N)) Q

/-- The inertia group attached to the normalization prime is Mathlib's
ideal-theoretic inertia subgroup for the normal-closure Galois action. -/
theorem normalizationPrimeInertiaGroup_eq_inertia
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] :
    normalizationPrimeInertiaGroup (B := B) (K := K) Q =
      Q.inertia (N ≃ₐ[K] N) :=
  primeInertiaSubgroup_eq_inertia (A :=
    FullInvariantNormalizationRing (B := B) (K := K) (N := N)) Q

/-- The exact local unramifiedness conclusion supplied by the
fixed-prime-inertia theorem of Stacks Project Tag `0BST`.  It remains an
explicit proposition because that theorem is not in the pinned Mathlib. -/
abbrev NormalizationPrimeInertiaFixedRingUnramifiedAt
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] : Prop :=
  InertiaFixedRingUnramifiedAt
    (A := FullInvariantNormalizationRing (B := B) (K := K) (N := N))
    (S := NormalClosureNormalizationRing (B := B) (N := N))
    (normalizationPrimeInertiaGroup (B := B) (K := K) Q) Q

/-- For marked finite normal-closure data with a separable marked extension, an
affine base integrally closed in that fraction field is canonically equivalent
to the full invariant ring of the normal-closure normalization.  This records
the base-identification needed to apply the literal `S^G → S^I` statement of
Tag `0BST` over `B`. -/
def baseEquivFullInvariantNormalizationRing
    [Algebra.IsSeparable K L] [IsIntegrallyClosed B]
    (D : CollisionFoundations.NormalClosureData K L N) :
    B ≃ₐ[B]
      FullInvariantNormalizationRing (B := B) (K := K) (N := N) := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI : IsGalois K N := D.isGalois_of_isSeparable
  let eFixed :
      IntermediateField.fixedField
          (⊤ : Subgroup D.galoisGroup) ≃ₐ[K] K :=
    (IntermediateField.equivOfEq
      (IsGalois.fixedField_top (F := K) (E := N))).trans
        (IntermediateField.botEquiv K N)
  let eClosure :
      integralClosure B
          (IntermediateField.fixedField
            (⊤ : Subgroup D.galoisGroup)) ≃ₐ[B]
        integralClosure B K :=
    (eFixed.restrictScalars B).mapIntegralClosure
  let eBase : integralClosure B K ≃ₐ[B] B :=
    IsIntegralClosure.equiv B (integralClosure B K) K B
  exact eBase.symm.trans <|
    eClosure.symm.trans <|
      fixedFieldNormalizationEquivFixedRing
        (B := B) (⊤ : Subgroup D.galoisGroup)

end NormalizationPrimeInertia

section ValuationComparison

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : AlgebraicGeometry.Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
    {C : NormalizedCover
      (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

omit [IsFractionRing B K] in
/-- Valuation inertia acts trivially modulo the center prime.  This is the
presentation-independent port of the corresponding Jacobian-collision
lemma. -/
theorem valuationInertia_sub_centerPrime
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (σ : CollisionFoundations.inertiaGroupAt K
      (D.valuationAt E).valuationRing)
    (t : NormalClosureNormalizationRing (B := B) (N := N)) :
    normalClosureNormalizationRingEquiv (B := B) σ.1 t - t ∈
      E.1.asIdeal := by
  let V := (D.valuationAt E).valuationRing
  rcases D.valuation_centered E with ⟨centerMap, hcenter, hcomap⟩
  rw [← hcomap]
  change centerMap
      (normalClosureNormalizationRingEquiv (B := B) σ.1 t - t) ∈
    IsLocalRing.maximalIdeal V
  rw [map_sub centerMap]
  rcases σ.2 with ⟨τ0, hτ0, hmap⟩
  let τ : V.inertiaSubgroup K := ⟨τ0, hτ0⟩
  have hτ : τ.1.1 = σ.1 := hmap
  have hinertia :
      τ.1 • centerMap t - centerMap t ∈
        IsLocalRing.maximalIdeal V := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    have hker :
        MulSemiringAction.toRingAut
            (V.decompositionSubgroup K)
            (IsLocalRing.ResidueField V) τ.1 = 1 :=
      τ.2
    rw [IsLocalRing.ResidueField.residue_smul]
    change
      (MulSemiringAction.toRingAut
          (V.decompositionSubgroup K)
          (IsLocalRing.ResidueField V) τ.1)
            (IsLocalRing.residue V (centerMap t)) -
          IsLocalRing.residue V (centerMap t) = 0
    rw [hker]
    exact sub_self _
  have haction :
      centerMap (normalClosureNormalizationRingEquiv (B := B) σ.1 t) =
        τ.1 • centerMap t := by
    apply Subtype.ext
    rw [hcenter]
    change σ.1 (t : N) = _
    rw [← hτ]
    change τ.1.1 (t : N) = τ.1.1 ((centerMap t : V) : N)
    rw [hcenter]
  rw [haction]
  exact hinertia

omit [IsFractionRing B K] in
/-- The valuation-theoretic inertia group chosen by a normalization diagram
is contained in the ring-theoretic prime inertia group at its center. -/
theorem valuationInertia_le_normalizationPrimeInertiaGroup
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) :
    CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing ≤
      normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal := by
  intro σ hσ
  apply mem_primeInertiaSubgroup_of_smul_sub_mem
  intro t
  exact D.valuationInertia_sub_centerPrime E ⟨σ, hσ⟩ t

/-- The local comparison needed to replace the prime-inertia condition in
Tag `0BST` by the valuation-inertia condition used for sheets.

The current `ValuationCenteredAt` data prove the other containment.  This
reverse containment follows from identifying the valuation ring with the
localization at the center prime.  It remains available as an explicit input
here; `LocalizationBridge.lean` constructs it from the diagram when the
affine base is Noetherian. -/
structure PrimeInertiaComparisonAt
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N)) : Prop where
  prime_le_valuation :
    normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal ≤
      CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing

omit [IsFractionRing B K] in
/-- Under the explicit reverse comparison, valuation inertia and prime
inertia agree. -/
theorem valuationInertia_eq_normalizationPrimeInertiaGroup
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hcomparison : D.PrimeInertiaComparisonAt E) :
    CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing =
      normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal :=
  le_antisymm
    (D.valuationInertia_le_normalizationPrimeInertiaGroup E)
    hcomparison.prime_le_valuation

omit [IsFractionRing B K] in
/-- The explicit reverse comparison is exactly the extra arrow needed to
promote a sheet-theoretic containment `I_val ≤ H` to the prime-inertia
containment required by fixed-ring descent. -/
theorem normalizationPrimeInertia_le_of_valuationInertia_le
    (D : Diagram C)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hcomparison : D.PrimeInertiaComparisonAt E)
    (H : Subgroup C.normalClosure.galoisGroup)
    (hvaluation :
      CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing ≤ H) :
    normalizationPrimeInertiaGroup
        (B := B) (K := K) E.1.asIdeal ≤ H :=
  hcomparison.prime_le_valuation.trans hvaluation

end Diagram

end ValuationComparison

end NormalizationInertia

end

end HodgeConjecture
