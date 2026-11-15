module

public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section

/-!
# Restrict actual supported chain operators and homotopies

The complexes are the native chain complexes of the original simplicial
subcomplexes. Operators lift through the existing supported-range
equivalence; injectivity of the original inclusion proves the chain and
homotopy identities. This construction is independent of any cover.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SubcomplexChainCoordinates

open CategoryTheory HomologicalComplex SingularChainCoordinates
open scoped Simplicial

variable {S T : SSet.{0}} (A : S.Subcomplex) (B : T.Subcomplex)

/-- Check a supported linear operator once on the original unit simplex generators. -/
theorem map_mem_chainSubmodule (i j : ℕ)
    (f : (complex S).X i →ₗ[ℚ] (complex T).X j)
    (hf : ∀ σ ∈ A.obj (Opposite.op ⦋i⦌),
      f (coordinates S i (Finsupp.single σ 1)) ∈ chainSubmodule B j)
    (c : (complex S).X i) (hc : c ∈ chainSubmodule A i) :
    f c ∈ chainSubmodule B j := by
  obtain ⟨c, rfl⟩ := (coordinates S i).surjective c
  rw [mem_chainSubmodule_iff, LinearEquiv.symm_apply_apply] at hc
  have hle : supportedCoordinates A i ≤
      (chainSubmodule B j).comap (f.comp (coordinates S i).toLinearMap) := by
    rw [supportedCoordinates, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact hle hc

/-- Restrict an operator between original chain objects to its supported ranges. -/
def restrictOperator (i j : ℕ) (f : (complex S).X i →ₗ[ℚ] (complex T).X j)
    (hf : ∀ c, c ∈ chainSubmodule A i → f c ∈ chainSubmodule B j) :
    (complex (A : SSet)).X i →ₗ[ℚ] (complex (B : SSet)).X j :=
  (chainSubmoduleEquiv B j).symm.toLinearMap.comp
    ((f.comp ((inclusion A).f i).hom).codRestrict (chainSubmodule B j) (fun c ↦
      hf _ (by rw [← chainSubmoduleEquiv_coe]; exact (chainSubmoduleEquiv A i c).property)))

theorem inclusion_restrictOperator (i j : ℕ)
    (f : (complex S).X i →ₗ[ℚ] (complex T).X j)
    (hf : ∀ c, c ∈ chainSubmodule A i → f c ∈ chainSubmodule B j)
    (c : (complex (A : SSet)).X i) :
    (inclusion B).f j (restrictOperator A B i j f hf c) = f ((inclusion A).f i c) := by
  rw [← chainSubmoduleEquiv_coe]
  change ((chainSubmoduleEquiv B j) ((chainSubmoduleEquiv B j).symm _) : (complex T).X j) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem inclusion_d (i j : ℕ) (c : (complex (A : SSet)).X i) :
    (inclusion A).f j ((complex (A : SSet)).d i j c) =
      (complex S).d i j ((inclusion A).f i c) :=
  (congrArg (fun f : (complex (A : SSet)).X i ⟶ (complex S).X j ↦ f c)
    ((inclusion A).comm i j)).symm

/-- Restrict an actual chain map that preserves the original supported ranges. -/
def restrictMap (f : complex S ⟶ complex T)
    (hf : ∀ n c, c ∈ chainSubmodule A n → f.f n c ∈ chainSubmodule B n) :
    complex (A : SSet) ⟶ complex (B : SSet) where
  f n := ModuleCat.ofHom (restrictOperator A B n n (f.f n).hom (hf n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply inclusion_injective B j
    change (inclusion B).f j ((complex (B : SSet)).d i j
      (restrictOperator A B i i (f.f i).hom (hf i) c)) =
      (inclusion B).f j (restrictOperator A B j j (f.f j).hom (hf j)
        ((complex (A : SSet)).d i j c))
    rw [inclusion_d, inclusion_restrictOperator, inclusion_restrictOperator, inclusion_d]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun q ↦ q.hom ((inclusion A).f i c)) (f.comm i j)

theorem restrictMap_inclusion (f : complex S ⟶ complex T)
    (hf : ∀ n c, c ∈ chainSubmodule A n → f.f n c ∈ chainSubmodule B n) :
    restrictMap A B f hf ≫ inclusion B = inclusion A ≫ f := by
  ext n c
  change (inclusion B).f n (restrictOperator A B n n (f.f n).hom (hf n) c) =
    f.f n ((inclusion A).f n c)
  exact inclusion_restrictOperator A B n n (f.f n).hom (hf n) c

@[simp]
theorem restrictMap_id : restrictMap A A (𝟙 (complex S)) (fun _ _ hc ↦ hc) =
    𝟙 (complex (A : SSet)) := by
  ext n c
  apply inclusion_injective A n
  change (inclusion A).f n
      (restrictOperator A A n n LinearMap.id (fun _ hc ↦ hc) c) = (inclusion A).f n c
  exact inclusion_restrictOperator A A n n LinearMap.id (fun _ hc ↦ hc) c

/-- A supported native homotopy restricts to the same native subcomplex chains. -/
def restrictHomotopy {f g : complex S ⟶ complex T}
    (hf : ∀ n c, c ∈ chainSubmodule A n → f.f n c ∈ chainSubmodule B n)
    (hg : ∀ n c, c ∈ chainSubmodule A n → g.f n c ∈ chainSubmodule B n)
    (h : Homotopy f g)
    (hh : ∀ i j c, c ∈ chainSubmodule A i → h.hom i j c ∈ chainSubmodule B j) :
    Homotopy (restrictMap A B f hf) (restrictMap A B g hg) where
  hom i j := ModuleCat.ofHom (restrictOperator A B i j (h.hom i j).hom (hh i j))
  zero i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply inclusion_injective B j
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    change (inclusion B).f j (restrictOperator A B i j (h.hom i j).hom (hh i j) c) = 0
    rw [inclusion_restrictOperator, h.zero i j hij, ModuleCat.hom_zero, LinearMap.zero_apply]
  comm i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply inclusion_injective B i
    change (inclusion B).f i (restrictOperator A B i i (f.f i).hom (hf i) c) =
      (inclusion B).f i
        (restrictOperator A B ((ComplexShape.down ℕ).next i) i
            (h.hom ((ComplexShape.down ℕ).next i) i).hom (hh _ _)
              ((complex (A : SSet)).d i ((ComplexShape.down ℕ).next i) c) +
          (complex (B : SSet)).d ((ComplexShape.down ℕ).prev i) i
            (restrictOperator A B i ((ComplexShape.down ℕ).prev i)
              (h.hom i ((ComplexShape.down ℕ).prev i)).hom (hh _ _) c) +
            restrictOperator A B i i (g.f i).hom (hg i) c)
    rw [map_add, map_add, inclusion_restrictOperator, inclusion_restrictOperator,
      inclusion_restrictOperator, inclusion_d, inclusion_d, inclusion_restrictOperator]
    have hc := congrArg (fun q ↦ q.hom ((inclusion A).f i c)) (h.comm i)
    change f.f i ((inclusion A).f i c) =
      h.hom ((ComplexShape.down ℕ).next i) i
          ((complex S).d i ((ComplexShape.down ℕ).next i) ((inclusion A).f i c)) +
        (complex T).d ((ComplexShape.down ℕ).prev i) i
          (h.hom i ((ComplexShape.down ℕ).prev i) ((inclusion A).f i c)) +
        g.f i ((inclusion A).f i c) at hc
    exact hc

end HodgeConjecture.SubcomplexChainCoordinates
