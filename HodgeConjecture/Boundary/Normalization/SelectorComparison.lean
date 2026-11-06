module

public import HodgeConjecture.Boundary.Normalization.NormalClosure
public import HodgeConjecture.Boundary.Sheets.MarkedBlockProjector
public import HodgeConjecture.LinearAlgebra.MarkedAugmentedAlgebra
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

/-!
# Generic collision selectors from a marked normal closure

Chosen representatives of the marked embeddings of `L` in its normal
closure define an evaluation morphism from the collision tensor algebra
`L ⊗[K] L` to functions on the Galois sheets `G/H`.  The diagonal element
supplied by formal unramifiedness maps to the characteristic function of the
marked base sheet.

This constructs the comparison morphism needed by the selector architecture.
For a separable marked extension, the normal-closure base change is also proved
equivalent to the split algebra of functions on the sheets.  The selector
comparison itself uses only formal unramifiedness and essential finite type,
not that stronger equivalence.

Mathematical reference: Stacks Project, Tag `02FL` for the diagonal
idempotent attached to an unramified algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct

universe uK uL uN

variable {K : Type uK} {L : Type uL} {N : Type uN}
variable [Field K] [Field L] [Field N]
variable [Algebra K L] [Algebra K N]

/-- The canonical rational marked-sheet algebra indexed by a supplied normal
closure.  Its group and distinguished fixing subgroup come directly from
`D`; no additional normality or Galois datum is requested. -/
noncomputable abbrev NormalClosureData.rationalMarkedSheetAlgebra
    (D : NormalClosureData K L N) :
    HodgeConjecture.MarkedAugmentedAlgebra ℚ
      (HodgeConjecture.GenericSheetAlgebra ℚ
        D.intermediateFixingSubgroup) :=
  HodgeConjecture.MarkedSheetProjector.markedAugmentedAlgebra
    D.intermediateFixingSubgroup

/-- The embedding of the marked field represented by a Galois sheet. -/
def NormalClosureData.sheetEmbedding
    (D : NormalClosureData K L N)
    (s : GaloisSheets D.intermediateFixingSubgroup) :
    L →ₐ[K] N :=
  (s.out : D.galoisGroup).toAlgHom.comp D.embedding

/-- The marked base sheet induces the distinguished embedding `L → N`. -/
theorem NormalClosureData.sheetEmbedding_baseSheet
    (D : NormalClosureData K L N) :
    D.sheetEmbedding
        (HodgeConjecture.baseSheet D.intermediateFixingSubgroup) =
      D.embedding := by
  apply AlgHom.ext
  intro x
  obtain ⟨h, hh⟩ :=
    QuotientGroup.mk_out_eq_mul
      D.intermediateFixingSubgroup (1 : D.galoisGroup)
  have hout :
      (HodgeConjecture.baseSheet D.intermediateFixingSubgroup).out ∈
        D.intermediateFixingSubgroup := by
    simpa only [one_mul, hh] using h.property
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      D.intermediateField
      (HodgeConjecture.baseSheet
        D.intermediateFixingSubgroup).out).mp
      hout (D.embedding x) ⟨x, rfl⟩

/-- Distinct Galois sheets induce distinct embeddings of the marked field. -/
theorem NormalClosureData.sheetEmbedding_injective
    (D : NormalClosureData K L N) :
    Function.Injective D.sheetEmbedding := by
  intro s t hst
  rw [← s.out_eq', ← t.out_eq']
  apply (QuotientGroup.eq).2
  apply (IntermediateField.mem_fixingSubgroup_iff
    D.intermediateField (s.out⁻¹ * t.out)).2
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  have hx := DFunLike.congr_fun hst x
  change s.out (D.embedding x) = t.out (D.embedding x) at hx
  change s.out.symm (t.out (D.embedding x)) = D.embedding x
  rw [← hx, s.out.symm_apply_apply]

/-- Every embedding of the marked field into its normal closure is represented
by a Galois sheet. -/
theorem NormalClosureData.sheetEmbedding_surjective
    (D : NormalClosureData K L N) :
    Function.Surjective D.sheetEmbedding := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra L N := D.embedding.toRingHom.toAlgebra
  letI : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (D.embedding.commutes x).symm
  intro f
  let g : N ≃ₐ[K] N :=
    AlgEquiv.ofBijective
      (f.liftNormal N)
      (Algebra.IsAlgebraic.algHom_bijective (f.liftNormal N))
  refine ⟨(g : GaloisSheets D.intermediateFixingSubgroup), ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨h, hh⟩ :=
    QuotientGroup.mk_out_eq_mul D.intermediateFixingSubgroup g
  have hfix :
      (h : D.galoisGroup) (D.embedding x) = D.embedding x :=
    (IntermediateField.mem_fixingSubgroup_iff
      D.intermediateField (h : D.galoisGroup)).mp
      h.property (D.embedding x) ⟨x, rfl⟩
  change
    ((g : GaloisSheets D.intermediateFixingSubgroup).out :
      D.galoisGroup) (D.embedding x) = f x
  rw [hh]
  change g ((h : D.galoisGroup) (D.embedding x)) = f x
  rw [hfix]
  exact f.liftNormal_commutes N x

/-- Galois sheets are equivalent to embeddings of the marked field into the
chosen normal closure. -/
noncomputable def NormalClosureData.sheetEmbeddingEquiv
    (D : NormalClosureData K L N) :
    GaloisSheets D.intermediateFixingSubgroup ≃ (L →ₐ[K] N) :=
  Equiv.ofBijective D.sheetEmbedding
    ⟨D.sheetEmbedding_injective, D.sheetEmbedding_surjective⟩

/-- Evaluate the two factors of the collision tensor algebra through the
distinguished embedding and each chosen-representative sheet embedding. -/
def NormalClosureData.collisionToGenericSheets
    (D : NormalClosureData K L N) :
    L ⊗[K] L →ₐ[K]
      HodgeConjecture.GenericSheetAlgebra N
        D.intermediateFixingSubgroup :=
  Algebra.TensorProduct.lift
    (Pi.algHom K
      (fun _ : GaloisSheets D.intermediateFixingSubgroup => N)
      (fun _ => D.embedding))
    (Pi.algHom K
      (fun _ : GaloisSheets D.intermediateFixingSubgroup => N)
      D.sheetEmbedding)
    (fun _ _ => mul_comm _ _)

@[simp]
theorem NormalClosureData.collisionToGenericSheets_tmul_apply
    (D : NormalClosureData K L N)
    (x y : L) (s : GaloisSheets D.intermediateFixingSubgroup) :
    D.collisionToGenericSheets (x ⊗ₜ[K] y) s =
      D.embedding x * D.sheetEmbedding s y := by
  rfl

/-- On the marked base sheet, collision evaluation is multiplication followed
by the distinguished embedding. -/
theorem NormalClosureData.collisionToGenericSheets_apply_baseSheet
    (D : NormalClosureData K L N)
    (z : L ⊗[K] L) :
    D.collisionToGenericSheets z
        (HodgeConjecture.baseSheet D.intermediateFixingSubgroup) =
      D.embedding (Algebra.TensorProduct.lmul' K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp [D.sheetEmbedding_baseSheet]

/-- Every non-base sheet is represented by an embedding different from the
distinguished embedding on some element of `L`. -/
theorem NormalClosureData.exists_sheetEmbedding_ne_of_ne_baseSheet
    (D : NormalClosureData K L N)
    {s : GaloisSheets D.intermediateFixingSubgroup}
    (hs : s ≠ HodgeConjecture.baseSheet
      D.intermediateFixingSubgroup) :
    ∃ x : L, D.sheetEmbedding s x ≠ D.embedding x := by
  have hout : s.out ∉ D.intermediateFixingSubgroup := by
    intro hout
    apply hs
    rw [← s.out_eq']
    apply (QuotientGroup.eq).2
    simpa using D.intermediateFixingSubgroup.inv_mem hout
  have hout' :
      ¬ (∀ z : N, z ∈ D.intermediateField → s.out z = z) :=
    (IntermediateField.mem_fixingSubgroup_iff
      D.intermediateField s.out).not.mp hout
  push_neg at hout'
  obtain ⟨z, hz, hne⟩ := hout'
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, hne⟩

/-- The diagonal element vanishes on every non-base Galois sheet. -/
theorem NormalClosureData.collisionToGenericSheets_elem_apply_of_ne
    [Algebra.FormallyUnramified K L]
    [Algebra.EssFiniteType K L]
    (D : NormalClosureData K L N)
    {s : GaloisSheets D.intermediateFixingSubgroup}
    (hs : s ≠ HodgeConjecture.baseSheet
      D.intermediateFixingSubgroup) :
    D.collisionToGenericSheets
        (Algebra.FormallyUnramified.elem K L) s = 0 := by
  obtain ⟨x, hx⟩ :=
    D.exists_sheetEmbedding_ne_of_ne_baseSheet hs
  have hzero :=
    congrArg
      (fun z : L ⊗[K] L => D.collisionToGenericSheets z s)
      (Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem
        (R := K) x)
  have hmul :
      (D.sheetEmbedding s x - D.embedding x) *
          D.collisionToGenericSheets
            (Algebra.FormallyUnramified.elem K L) s = 0 := by
    simpa only [map_mul, map_sub, map_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, AlgHom.id_apply,
      NormalClosureData.collisionToGenericSheets_tmul_apply,
      map_one, one_mul, mul_one] using hzero
  exact
    (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hx)

/-- Under the generic collision comparison, the diagonal/separability element
is exactly the characteristic selector of the marked base sheet. -/
theorem NormalClosureData.collisionToGenericSheets_elem_eq_baseSheetSelector
    [Algebra.FormallyUnramified K L]
    [Algebra.EssFiniteType K L]
    (D : NormalClosureData K L N) :
    D.collisionToGenericSheets
        (Algebra.FormallyUnramified.elem K L) =
      HodgeConjecture.genericSheetSelector N
        D.intermediateFixingSubgroup
        {HodgeConjecture.baseSheet
          D.intermediateFixingSubgroup} := by
  funext s
  by_cases hs :
      s = HodgeConjecture.baseSheet D.intermediateFixingSubgroup
  · subst s
    rw [D.collisionToGenericSheets_apply_baseSheet]
    rw [Algebra.FormallyUnramified.lmul_elem]
    simp [HodgeConjecture.genericSheetSelector]
  · rw [D.collisionToGenericSheets_elem_apply_of_ne hs]
    simp [HodgeConjecture.genericSheetSelector, hs]

/-- The chosen-representative normal-closure base-change evaluation morphism
`N ⊗[K] L → functions(G/H, N)`. It is upgraded to an equivalence below when
the marked extension is separable. -/
def NormalClosureData.normalClosureTensorToGenericSheets
    (D : NormalClosureData K L N) :
    N ⊗[K] L →ₐ[N]
      HodgeConjecture.GenericSheetAlgebra N
        D.intermediateFixingSubgroup :=
  Algebra.TensorProduct.lift
    (Pi.algHom N
      (fun _ : GaloisSheets D.intermediateFixingSubgroup => N)
      (fun _ => AlgHom.id N N))
    (Pi.algHom K
      (fun _ : GaloisSheets D.intermediateFixingSubgroup => N)
      D.sheetEmbedding)
    (fun _ _ => mul_comm _ _)

@[simp]
theorem NormalClosureData.normalClosureTensorToGenericSheets_tmul_apply
    (D : NormalClosureData K L N)
    (x : N) (y : L)
    (s : GaloisSheets D.intermediateFixingSubgroup) :
    D.normalClosureTensorToGenericSheets (x ⊗ₜ[K] y) s =
      x * D.sheetEmbedding s y := by
  rfl

/-!
## The multiplicative base-sheet square

The distinguished sheet is evaluated by an algebra homomorphism, not merely
by a linear functional.  On the tensor side the corresponding map is the
diagonal multiplication morphism obtained from the identity of `N` and the
marked embedding `L → N`.  The next theorem says that normal-closure sheet
evaluation intertwines these two augmentations.
-/

/-- Evaluation at the distinguished base sheet as an `N`-algebra
homomorphism. -/
def NormalClosureData.normalClosureBaseSheetAugmentation
    (D : NormalClosureData K L N) :
    HodgeConjecture.GenericSheetAlgebra N
        D.intermediateFixingSubgroup →ₐ[N] N :=
  Pi.evalAlgHom N
    (fun _ : GaloisSheets D.intermediateFixingSubgroup => N)
    (HodgeConjecture.baseSheet D.intermediateFixingSubgroup)

@[simp]
theorem NormalClosureData.normalClosureBaseSheetAugmentation_apply
    (D : NormalClosureData K L N)
    (q : HodgeConjecture.GenericSheetAlgebra N
      D.intermediateFixingSubgroup) :
    D.normalClosureBaseSheetAugmentation q =
      q (HodgeConjecture.baseSheet D.intermediateFixingSubgroup) :=
  rfl

/-- The diagonal multiplication map on the normal-closure base change.  On a
pure tensor it sends `x ⊗ y` to `x * D.embedding y`. -/
def NormalClosureData.normalClosureTensorDiagonal
    (D : NormalClosureData K L N) :
    N ⊗[K] L →ₐ[N] N :=
  Algebra.TensorProduct.lift
    (AlgHom.id N N) D.embedding
    (fun _ _ => mul_comm _ _)

@[simp]
theorem NormalClosureData.normalClosureTensorDiagonal_tmul
    (D : NormalClosureData K L N)
    (x : N) (y : L) :
    D.normalClosureTensorDiagonal (x ⊗ₜ[K] y) =
      x * D.embedding y :=
  rfl

/-- The normal-closure sheet map commutes with the two multiplicative
augmentations: evaluating its output at the base sheet is diagonal
multiplication on `N ⊗[K] L`. -/
theorem NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets
    (D : NormalClosureData K L N) :
    D.normalClosureBaseSheetAugmentation.comp
        D.normalClosureTensorToGenericSheets =
      D.normalClosureTensorDiagonal := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [NormalClosureData.sheetEmbedding_baseSheet]

section

variable [Algebra.FormallyUnramified K L]
variable [Algebra.EssFiniteType K L]

/-- The translate of the diagonal element associated to a Galois sheet. -/
def NormalClosureData.sheetDeltaTensor
    (D : NormalClosureData K L N)
    (s : GaloisSheets D.intermediateFixingSubgroup) :
    N ⊗[K] L :=
  Algebra.TensorProduct.map
    (D.sheetEmbedding s) (AlgHom.id K L)
    (Algebra.FormallyUnramified.elem K L)

omit [Algebra.FormallyUnramified K L] [Algebra.EssFiniteType K L] in
theorem NormalClosureData.normalClosureTensor_map_apply_same
    (D : NormalClosureData K L N)
    (s : GaloisSheets D.intermediateFixingSubgroup)
    (z : L ⊗[K] L) :
    D.normalClosureTensorToGenericSheets
        (Algebra.TensorProduct.map
          (D.sheetEmbedding s) (AlgHom.id K L) z) s =
      D.sheetEmbedding s (Algebra.TensorProduct.lmul' K z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y => simp

/-- The translated diagonal element evaluates to the characteristic function
of its sheet. -/
theorem NormalClosureData.sheetDeltaTensor_maps_to_selector
    (D : NormalClosureData K L N)
    (s : GaloisSheets D.intermediateFixingSubgroup) :
    D.normalClosureTensorToGenericSheets (D.sheetDeltaTensor s) =
      HodgeConjecture.genericSheetSelector N
        D.intermediateFixingSubgroup {s} := by
  funext t
  by_cases hts : t = s
  · subst t
    unfold NormalClosureData.sheetDeltaTensor
    rw [D.normalClosureTensor_map_apply_same]
    rw [Algebra.FormallyUnramified.lmul_elem]
    simp [HodgeConjecture.genericSheetSelector]
  · have hmaps : D.sheetEmbedding t ≠ D.sheetEmbedding s := by
      intro h
      exact hts (D.sheetEmbedding_injective h)
    have hex :
        ∃ x : L, D.sheetEmbedding t x ≠ D.sheetEmbedding s x := by
      by_contra h
      push_neg at h
      exact hmaps (AlgHom.ext h)
    obtain ⟨x, hx⟩ := hex
    have hzero :=
      congrArg
        (fun z : L ⊗[K] L =>
          D.normalClosureTensorToGenericSheets
            (Algebra.TensorProduct.map
              (D.sheetEmbedding s) (AlgHom.id K L) z) t)
        (Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem
          (R := K) x)
    have hmul :
        (D.sheetEmbedding t x - D.sheetEmbedding s x) *
          D.normalClosureTensorToGenericSheets
            (D.sheetDeltaTensor s) t = 0 := by
      simpa only [map_mul, map_sub, map_zero,
        Algebra.TensorProduct.map_tmul,
        NormalClosureData.normalClosureTensorToGenericSheets_tmul_apply,
        Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, AlgHom.id_apply, NormalClosureData.sheetDeltaTensor,
        map_one, one_mul, mul_one] using hzero
    rw [(mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hx)]
    simp [HodgeConjecture.genericSheetSelector, hts]

/-- The normal-closure evaluation morphism is onto the split sheet algebra. -/
theorem NormalClosureData.normalClosureTensorToGenericSheets_surjective
    (D : NormalClosureData K L N) :
    Function.Surjective D.normalClosureTensorToGenericSheets := by
  classical
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI : Fintype D.galoisGroup := Fintype.ofFinite D.galoisGroup
  letI : Fintype (GaloisSheets D.intermediateFixingSubgroup) :=
    Fintype.ofFinite (GaloisSheets D.intermediateFixingSubgroup)
  intro q
  refine ⟨∑ s, q s • D.sheetDeltaTensor s, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, D.sheetDeltaTensor_maps_to_selector]
  funext t
  change
    (Pi.evalAddMonoidHom
      (fun _ : GaloisSheets D.intermediateFixingSubgroup => N) t)
      (∑ s, q s • HodgeConjecture.genericSheetSelector N
        D.intermediateFixingSubgroup {s}) = q t
  rw [map_sum]
  simp only [Pi.evalAddMonoidHom_apply]
  simp [HodgeConjecture.genericSheetSelector]

end

/-- For a separable marked extension, normal-closure evaluation is bijective. -/
theorem NormalClosureData.normalClosureTensorToGenericSheets_bijective
    [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N) :
    Function.Bijective D.normalClosureTensorToGenericSheets := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI : Fintype D.galoisGroup := Fintype.ofFinite D.galoisGroup
  letI : Fintype (GaloisSheets D.intermediateFixingSubgroup) :=
    Fintype.ofFinite (GaloisSheets D.intermediateFixingSubgroup)
  have hsurj :
      Function.Surjective D.normalClosureTensorToGenericSheets :=
    D.normalClosureTensorToGenericSheets_surjective
  have hcard :
      Fintype.card (GaloisSheets D.intermediateFixingSubgroup) =
        Module.finrank K L := by
    rw [Fintype.card_eq_nat_card,
      Nat.card_congr D.sheetEmbeddingEquiv,
      AlgHom.natCard_of_splits K L N
        (fun x => D.normalClosure.splits x)]
  have hdim :
      Module.finrank N (N ⊗[K] L) =
        Module.finrank N
          (HodgeConjecture.GenericSheetAlgebra N
            D.intermediateFixingSubgroup) := by
    rw [Module.finrank_baseChange,
      Module.finrank_fintype_fun_eq_card, hcard]
  have hlinSurj :
      Function.Surjective
        D.normalClosureTensorToGenericSheets.toLinearMap :=
    hsurj
  have hlinInj :
      Function.Injective
        D.normalClosureTensorToGenericSheets.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim).mpr hlinSurj
  exact ⟨hlinInj, hsurj⟩

/-- For a separable marked extension, the normal-closure tensor product splits
as the algebra of functions on the Galois sheets. -/
noncomputable def NormalClosureData.normalClosureTensorGenericSheetsEquiv
    [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N) :
    N ⊗[K] L ≃ₐ[N]
      HodgeConjecture.GenericSheetAlgebra N
        D.intermediateFixingSubgroup :=
  AlgEquiv.ofBijective D.normalClosureTensorToGenericSheets
    D.normalClosureTensorToGenericSheets_bijective

/-- For a separable marked extension, base-sheet augmentation through the
Galois-sheet algebra equivalence is exactly the tensor diagonal morphism.
This is the equivalence form of the multiplicative base-sheet square above. -/
theorem NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv
    [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N) :
    D.normalClosureBaseSheetAugmentation.comp
        D.normalClosureTensorGenericSheetsEquiv.toAlgHom =
      D.normalClosureTensorDiagonal := by
  simpa only [NormalClosureData.normalClosureTensorGenericSheetsEquiv, AlgEquiv.toAlgHom_ofBijective] using
    D.normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets

universe uR uS

variable {R : Type uR} {S : Type uS}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FormallyUnramified R S]
variable [Algebra.EssFiniteType R S]

/-- Multiplication by the diagonal element supplied by formal
unramifiedness factors through tensor multiplication.  This is the rank-one
law needed to regard the tensor square as a marked augmented algebra. -/
theorem formallyUnramifiedElem_mul (z : S ⊗[R] S) :
    Algebra.FormallyUnramified.elem R S * z =
      Algebra.TensorProduct.lmul'' R z •
        Algebra.FormallyUnramified.elem R S := by
  rw [Algebra.smul_def]
  change
    Algebra.FormallyUnramified.elem R S * z =
      ((Algebra.TensorProduct.lmul' R z) ⊗ₜ[R] (1 : S)) *
        Algebra.FormallyUnramified.elem R S
  rw [mul_comm]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [add_mul, hx, hy, map_add,
        TensorProduct.add_tmul, add_mul]
  | tmul x y =>
      calc
        (x ⊗ₜ[R] y) *
            Algebra.FormallyUnramified.elem R S =
          (x ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] y) *
            Algebra.FormallyUnramified.elem R S := by simp
        _ = (x ⊗ₜ[R] (1 : S)) *
              (((1 : S) ⊗ₜ[R] y) *
                Algebra.FormallyUnramified.elem R S) := by
              rw [mul_assoc]
        _ = (x ⊗ₜ[R] (1 : S)) *
              ((y ⊗ₜ[R] (1 : S)) *
                Algebra.FormallyUnramified.elem R S) := by
              rw [Algebra.FormallyUnramified.one_tmul_mul_elem]
        _ = ((x * y) ⊗ₜ[R] (1 : S)) *
              Algebra.FormallyUnramified.elem R S := by
              simp [← mul_assoc]

/-- The tensor-square augmentation and the formally-unramified diagonal
element form a marked augmented algebra over `S`. -/
noncomputable def formallyUnramifiedMarkedAugmentedAlgebra :
    HodgeConjecture.MarkedAugmentedAlgebra S (S ⊗[R] S) where
  augmentation := Algebra.TensorProduct.lmul'' R
  selector := Algebra.FormallyUnramified.elem R S
  augmentation_selector :=
    Algebra.FormallyUnramified.lmul_elem
  selector_mul := formallyUnramifiedElem_mul

/-- The chosen diagonal element supplied by formal unramifiedness is an
idempotent in the tensor-square algebra. -/
theorem formallyUnramifiedElem_isIdempotent :
    IsIdempotentElem
      (Algebra.FormallyUnramified.elem R S) :=
  (formallyUnramifiedMarkedAugmentedAlgebra
    (R := R) (S := S)).selector_isIdempotent

end


end HodgeConjecture.CollisionFoundations
