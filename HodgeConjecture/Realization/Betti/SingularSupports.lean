module

public import HodgeConjecture.Realization.Betti.RelativeCochainsNaturality
public import HodgeConjecture.Realization.Betti.RelativeAdditivity
public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Original relative cohomology with specified supports

Support extension is the original identity map of relative pairs, before
passing to native cohomology. Finite assembly is the actual sum of these
singleton extensions. No absolute cohomology coordinate defines a map here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularSupports

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial

variable (X : Type) [TopologicalSpace X]

abbrev space : TopCat := TopCat.of X
abbrev singular : SSet := TopCat.toSSet.obj (space X)

/-- Original singular simplices contained in the actual support complement. -/
abbrev boundary (F : Set X) := SingularSubcomplexes.subsetSingular (space X) Fᶜ

/-- The original relative group of the actual complement pair. -/
abbrev Supported (F : Set X) (n : ℕ) := RelativeCochains.Cohomology (boundary X F) n

variable {F G H : Set X}

theorem extensionCondition (h : F ⊆ G) :
    boundary X G ≤ (boundary X F).preimage (𝟙 (singular X)) := by
  intro n σ hσ t hf
  exact hσ t (h hf)

/-- The original identity pullback of actual relative kernel complexes. -/
def extensionComplex (h : F ⊆ G) :
    RelativeCochains.complex (boundary X F) ⟶ RelativeCochains.complex (boundary X G) :=
  RelativeCochains.pullback (𝟙 (singular X)) (extensionCondition X h)

/-- Extend support along an actual set inclusion, using the original pair map. -/
def extension (h : F ⊆ G) (n : ℕ) : Supported X F n →ₗ[ℚ] Supported X G n :=
  (homologyMap (extensionComplex X h) n).hom

/-- Forget actual relative support by the original inclusion of cochains. -/
def forget (F : Set X) (n : ℕ) :
    Supported X F n →ₗ[ℚ] SingularCochains.Cohomology (space X) n :=
  (RelativeCochains.forget (boundary X F) n).hom

theorem extensionComplex_self (F : Set X) :
    extensionComplex X (Set.Subset.rfl : F ⊆ F) = 𝟙 _ :=
  RelativeCochains.pullback_id (boundary X F) (extensionCondition X Set.Subset.rfl)

theorem extension_self (F : Set X) (n : ℕ) :
    extension X (Set.Subset.rfl : F ⊆ F) n = LinearMap.id := by
  unfold extension
  rw [extensionComplex_self, homologyMap_id]
  rfl

theorem extensionComplex_trans (hFG : F ⊆ G) (hGH : G ⊆ H) :
    extensionComplex X hFG ≫ extensionComplex X hGH = extensionComplex X (hFG.trans hGH) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

theorem extension_trans (hFG : F ⊆ G) (hGH : G ⊆ H) (n : ℕ) :
    (extension X hGH n).comp (extension X hFG n) =
      extension X (hFG.trans hGH) n := by
  change (homologyMap (extensionComplex X hFG) n ≫
    homologyMap (extensionComplex X hGH) n).hom = _
  rw [← homologyMap_comp, extensionComplex_trans]
  rfl

theorem extensionComplex_forget (h : F ⊆ G) :
    extensionComplex X h ≫ RelativeCochains.inclusion (boundary X G) =
      RelativeCochains.inclusion (boundary X F) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rfl

theorem extension_forget (h : F ⊆ G) (n : ℕ) :
    (forget X G n).comp (extension X h n) = forget X F n := by
  change (homologyMap (extensionComplex X h) n ≫
    homologyMap (RelativeCochains.inclusion (boundary X G)) n).hom = _
  rw [← homologyMap_comp, extensionComplex_forget]
  rfl

/-- Equal actual supports give the original identity pair equivalence. -/
def equalityEquiv (h : F = G) (n : ℕ) : Supported X F n ≃ₗ[ℚ] Supported X G n := by
  subst G
  exact LinearEquiv.refl ℚ _

theorem equalityEquiv_toLinearMap (h : F = G) (n : ℕ) :
    (equalityEquiv X h n).toLinearMap = extension X h.le n := by
  subst G
  exact (extension_self X F n).symm

theorem empty_cochain_subsingleton (n : ℕ) :
    Subsingleton (RelativeCochains.Cochain (boundary X ∅) n) := by
  constructor
  intro φ ψ
  apply Subtype.ext
  funext σ
  have hσ : σ ∈ (boundary X (∅ : Set X)).obj (op ⦋n⦌) := by
    intro t
    simp
  exact (RelativeCochains.cochain_vanish (boundary X ∅) n φ ⟨σ, hσ⟩).trans
    (RelativeCochains.cochain_vanish (boundary X ∅) n ψ ⟨σ, hσ⟩).symm

theorem empty_isZero (n : ℕ) : IsZero (Supported X ∅ n) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero (ModuleCat.of ℚ (RelativeCochains.Cochain (boundary X ∅) n))
  exact ModuleCat.isZero_iff_subsingleton.mpr (empty_cochain_subsingleton X n)

theorem empty_eq_zero (n : ℕ) (z : Supported X ∅ n) : z = 0 :=
  (ModuleCat.isZero_iff_subsingleton.mp (empty_isZero X n)).elim z 0

/-- Original singleton support extension into a specified actual support. -/
def singletonExtension (S : Finset X) (p : ↥(S : Set X)) (n : ℕ) :
    Supported X ({p.val} : Set X) n →ₗ[ℚ] Supported X (S : Set X) n :=
  extension X (Set.singleton_subset_iff.mpr p.property) n

abbrev Family (S : Finset X) (n : ℕ) :=
  (p : ↥(S : Set X)) → Supported X ({p.val} : Set X) n

/-- The sum of original identity-pair extensions from the actual singleton supports. -/
def assemble (S : Finset X) (n : ℕ) : Family X S n →ₗ[ℚ] Supported X (S : Set X) n where
  toFun φ := ∑ p : ↥(S : Set X), singletonExtension X S p n (φ p)
  map_add' φ ψ := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' q φ := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem assemble_apply (S : Finset X) (n : ℕ) (φ : Family X S n) :
    assemble X S n φ = ∑ p : ↥(S : Set X), singletonExtension X S p n (φ p) := rfl

theorem forget_assemble (S : Finset X) (n : ℕ) (φ : Family X S n) :
    forget X (S : Set X) n (assemble X S n φ) =
      ∑ p : ↥(S : Set X), forget X ({p.val} : Set X) n (φ p) := by
  rw [assemble_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact LinearMap.congr_fun
    (extension_forget X (Set.singleton_subset_iff.mpr p.property) n) (φ p)

/-- The membership and subtype presentations of the same original singleton family. -/
def familyMembershipEquiv (S : Finset X) (n : ℕ) :
    Family X S n ≃ ((p : X) → p ∈ S → Supported X ({p} : Set X) n) where
  toFun φ p hp := φ ⟨p, hp⟩
  invFun φ p := φ p.val p.property
  left_inv _ := rfl
  right_inv _ := rfl

/-- Splitting the index set separates an actual singleton from the remaining actual supports. -/
def insertFamilyEquiv [DecidableEq X] (S : Finset X) (p : X) (hp : p ∉ S) (n : ℕ) :
    Family X (insert p S) n ≃ Supported X ({p} : Set X) n × Family X S n := by
  classical
  exact (familyMembershipEquiv X (insert p S) n).trans
    ((Finset.insertPiProdEquiv (fun q ↦ Supported X ({q} : Set X) n) hp).trans
      ((Equiv.refl _).prodCongr (familyMembershipEquiv X S n).symm))

theorem insertFamilyEquiv_fst [DecidableEq X] (S : Finset X) (p : X) (hp : p ∉ S)
    (n : ℕ) (φ : Family X (insert p S) n) :
    (insertFamilyEquiv X S p hp n φ).1 = φ ⟨p, Finset.mem_insert_self p S⟩ := rfl

theorem insertFamilyEquiv_snd [DecidableEq X] (S : Finset X) (p : X) (hp : p ∉ S)
    (n : ℕ) (φ : Family X (insert p S) n) (q : ↥(S : Set X)) :
    (insertFamilyEquiv X S p hp n φ).2 q =
      φ ⟨q.val, Finset.mem_insert_of_mem q.property⟩ := rfl

omit [TopologicalSpace X] in
theorem insertSingletonSubset [DecidableEq X] (S : Finset X) (p : X) :
    ({p} : Set X) ⊆ (insert p S : Finset X) :=
  Set.singleton_subset_iff.mpr (Finset.mem_insert_self p S)

omit [TopologicalSpace X] in
theorem insertRestSubset [DecidableEq X] (S : Finset X) (p : X) :
    (S : Set X) ⊆ (insert p S : Finset X) := by
  intro q hq
  exact Finset.mem_insert_of_mem hq

/-- The canonical sum into the support obtained by adjoining one actual point. -/
def insertBinaryMap [DecidableEq X] (S : Finset X) (p : X) (n : ℕ) :
    Supported X ({p} : Set X) n × Supported X (S : Set X) n →ₗ[ℚ]
      Supported X (insert p S : Finset X) n :=
  (extension X (insertSingletonSubset X S p) n).coprod
    (extension X (insertRestSubset X S p) n)

/-- Finite singleton assembly factors through the actual binary support sum. -/
theorem assemble_insert [DecidableEq X] (S : Finset X) (p : X) (hp : p ∉ S)
    (n : ℕ) (φ : Family X (insert p S) n) :
    assemble X (insert p S) n φ =
      insertBinaryMap X S p n
        ((insertFamilyEquiv X S p hp n φ).1,
          assemble X S n (insertFamilyEquiv X S p hp n φ).2) := by
  classical
  let e : ↥((insert p S : Finset X) : Set X) ≃ Option ↥(S : Set X) :=
    Finset.subtypeInsertEquivOption hp
  let f : ↥((insert p S : Finset X) : Set X) → Supported X (insert p S : Finset X) n :=
    fun q ↦ singletonExtension X (insert p S) q n (φ q)
  have hsum := Fintype.sum_equiv
    (ι := ↥((insert p S : Finset X) : Set X)) (κ := Option ↥(S : Set X))
    e f (fun q ↦ f (e.symm q))
    (fun q ↦ congrArg f (e.symm_apply_apply q).symm)
  rw [Fintype.sum_option] at hsum
  change (∑ q, f q) = _
  rw [hsum]
  change extension X (insertSingletonSubset X S p) n
      (φ ⟨p, Finset.mem_insert_self p S⟩) +
      (∑ q : ↥(S : Set X), singletonExtension X (insert p S)
        ⟨q.val, Finset.mem_insert_of_mem q.property⟩ n
          (φ ⟨q.val, Finset.mem_insert_of_mem q.property⟩)) = _
  change _ = extension X (insertSingletonSubset X S p) n
      (φ ⟨p, Finset.mem_insert_self p S⟩) +
      extension X (insertRestSubset X S p) n
        (assemble X S n (insertFamilyEquiv X S p hp n φ).2)
  rw [assemble_apply, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact (LinearMap.congr_fun
    (extension_trans X (Set.singleton_subset_iff.mpr q.property)
      (insertRestSubset X S p) n)
        ((insertFamilyEquiv X S p hp n φ).2 q)).symm

/-- Actual binary support additivity implies the canonical finite assembly theorem. -/
theorem assemble_bijective_of_insert (n : ℕ)
    (hbinary : ∀ [DecidableEq X] (S : Finset X) (p : X), p ∉ S →
      Function.Bijective (insertBinaryMap X S p n)) (S : Finset X) :
    Function.Bijective (assemble X S n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · intro φ ψ _
        funext p
        exact False.elim (Finset.notMem_empty p.val p.property)
      · intro z
        refine ⟨fun p ↦ False.elim (Finset.notMem_empty p.val p.property), ?_⟩
        have hz : IsZero (Supported X ((∅ : Finset X) : Set X) n) := by
          simpa only [Finset.coe_empty] using empty_isZero X n
        exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ z
  | @insert p S hp ih =>
      let e := insertFamilyEquiv X S p hp n
      let m := (LinearEquiv.refl ℚ (Supported X ({p} : Set X) n)).prodCongr
        (LinearEquiv.ofBijective (assemble X S n) ih)
      have hb := (hbinary S p hp).comp (m.bijective.comp e.bijective)
      have heq : (assemble X (insert p S) n : Family X (insert p S) n → _) =
          (insertBinaryMap X S p n) ∘ m ∘ e := by
        funext φ
        exact assemble_insert X S p hp n φ
      rw [heq]
      exact hb

/-- Literal equality of boundary subcomplexes retains the original extension sum. -/
theorem relativeBinary_bijective_of_eq (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (C : (singular X).Subcomplex)
    (hC : C = SingularSubcomplexes.subsetSingular (space X) (U ∩ V))
    (hCU : C ≤ SingularSubcomplexes.subsetSingular (space X) U)
    (hCV : C ≤ SingularSubcomplexes.subsetSingular (space X) V) (n : ℕ) :
    Function.Bijective
      (((homologyMap (RelativeAdditivity.extension C
          (SingularSubcomplexes.subsetSingular (space X) U) hCU) n).hom).coprod
        ((homologyMap (RelativeAdditivity.extension C
          (SingularSubcomplexes.subsetSingular (space X) V) hCV) n).hom)) := by
  subst C
  exact RelativeAdditivity.sumMap_bijective (space X) U V hU hV hcover n

/-- The disjoint singleton and remaining finite support have a genuine open complement cover. -/
theorem insertBinaryMap_bijective [T1Space X] [DecidableEq X]
    (S : Finset X) (p : X) (hp : p ∉ S) (n : ℕ) :
    Function.Bijective (insertBinaryMap X S p n) := by
  let U : Set X := ({p} : Set X)ᶜ
  let V : Set X := (S : Set X)ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hV : IsOpen V := S.finite_toSet.isClosed.isOpen_compl
  have hcover : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = p
    · right
      subst x
      exact hp
    · left
      exact hx
  have hC : boundary X (insert p S : Finset X) =
      SingularSubcomplexes.subsetSingular (space X) (U ∩ V) := by
    apply congrArg (SingularSubcomplexes.subsetSingular (space X))
    ext x
    simp only [U, V, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_insert,
      Set.mem_inter_iff, Set.mem_singleton_iff, not_or]
  have hCU : boundary X (insert p S : Finset X) ≤
      SingularSubcomplexes.subsetSingular (space X) U := by
    simpa only [SSet.Subcomplex.preimage_id] using
      extensionCondition X (insertSingletonSubset X S p)
  have hCV : boundary X (insert p S : Finset X) ≤
      SingularSubcomplexes.subsetSingular (space X) V := by
    simpa only [SSet.Subcomplex.preimage_id] using
      extensionCondition X (insertRestSubset X S p)
  change Function.Bijective
    (((homologyMap (RelativeAdditivity.extension (boundary X (insert p S : Finset X))
        (SingularSubcomplexes.subsetSingular (space X) U) hCU) n).hom).coprod
      ((homologyMap (RelativeAdditivity.extension (boundary X (insert p S : Finset X))
        (SingularSubcomplexes.subsetSingular (space X) V) hCV) n).hom))
  exact relativeBinary_bijective_of_eq X U V hU hV hcover _ hC hCU hCV n

/-- Canonical finite assembly is bijective on the original relative groups in every degree. -/
theorem assemble_bijective [T1Space X] (S : Finset X) (n : ℕ) :
    Function.Bijective (assemble X S n) := by
  apply assemble_bijective_of_insert X n _ S
  intro _ T p hp
  exact insertBinaryMap_bijective X T p hp n

/-- The forward equivalence is the actual canonical sum of singleton support extensions. -/
def assembleEquiv [T1Space X] (S : Finset X) (n : ℕ) :
    Family X S n ≃ₗ[ℚ] Supported X (S : Set X) n :=
  LinearEquiv.ofBijective (assemble X S n) (assemble_bijective X S n)

theorem assembleEquiv_toLinearMap [T1Space X] (S : Finset X) (n : ℕ) :
    (assembleEquiv X S n).toLinearMap = assemble X S n := rfl

def assembleIso [T1Space X] (S : Finset X) (n : ℕ) :
    ModuleCat.of ℚ (Family X S n) ≅ Supported X (S : Set X) n :=
  (assembleEquiv X S n).toModuleIso

theorem assembleIso_hom [T1Space X] (S : Finset X) (n : ℕ) :
    (assembleIso X S n).hom.hom = assemble X S n := rfl

end HodgeConjecture.SingularSupports

end
