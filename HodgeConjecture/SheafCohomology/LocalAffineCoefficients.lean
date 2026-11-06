module

public import HodgeConjecture.SheafCohomology.AffineCoefficients

@[expose] public section

/-!
# Affine acyclicity from an actual local trivialization

Only the opens below the chosen affine open enter the basis induction.
A restriction-compatible identification with a quasi-coherent module on
those opens therefore suffices; no global identification of the coefficient
object with an `𝒪`-module and no derived restriction comparison is required.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology

open Cohomology.Basis Cohomology.BasisCycles
open HodgeConjecture.SheafCohomology.CategoryTheory.CechComplex

noncomputable section

universe u v w

section Cochains

variable {X : Type u} [TopologicalSpace X] (U : Opens X)
  (P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (e : ∀ (V : Opens X), V ≤ U → P.obj (op V) ≃+ Q.obj (op V))
  {κ : Type u} (Y : κ → Opens X) (hY : ∀ i, Y i ≤ U)

include hY in
/-- Every nonempty tuple intersection remains below the trivializing open. -/
theorem localIntersection_le (q : ℕ) (x : Fin (q + 1) → κ) : inter Y x ≤ U :=
  (leOfHom (interπ Y x 0)).trans (hY (x 0))

/-- Local equivalences identify all cochain groups of a cover inside the open. -/
def localCochainEquiv (q : ℕ) : Cochain Y P q ≃+ Cochain Y Q q where
  toFun s := mk Y Q fun x => e (inter Y x) (localIntersection_le U Y hY q x) (comp Y P s x)
  invFun s := mk Y P fun x => (e (inter Y x) (localIntersection_le U Y hY q x)).symm (comp Y Q s x)
  left_inv s := cochain_ext Y P _ _ fun x => by simp
  right_inv s := cochain_ext Y Q _ _ fun x => by simp
  map_add' s t := cochain_ext Y Q _ _ fun x => by simp

@[simp]
theorem localCochainEquiv_apply (q : ℕ) (s : Cochain Y P q) :
    localCochainEquiv U P Q e Y hY q s =
      mk Y Q (fun x => e (inter Y x) (localIntersection_le U Y hY q x) (comp Y P s x)) := rfl

variable
  (he : ∀ {V W : Opens X} (hVW : V ≤ W) (hWU : W ≤ U) (s : P.obj (op W)),
    e V (hVW.trans hWU) (res P hVW s) = res Q hVW (e W hWU s))

include he in
/-- Actual restriction naturality makes the local cochain equivalence commute with d. -/
theorem localCochainEquiv_dd (q : ℕ) (s : Cochain Y P q) :
    localCochainEquiv U P Q e Y hY (q + 1) (dd Y P s) =
      dd Y Q (localCochainEquiv U P Q e Y hY q s) := by
  apply cochain_ext Y Q
  intro x
  simp only [localCochainEquiv_apply, comp_mk, comp_dd, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_zsmul, he]

include e hY he in
/-- Čech acyclicity transports through the actual local restriction-compatible equivalence. -/
theorem cechSurj_of_localEquiv (q : ℕ) (hQ : CechSurj Y Q q) : CechSurj Y P q := by
  intro s hs
  have hz : dd Y Q (localCochainEquiv U P Q e Y hY (q + 1) s) = 0 := by
    rw [← localCochainEquiv_dd U P Q e Y hY he, hs, map_zero]
  obtain ⟨b, hb⟩ := hQ _ hz
  refine ⟨(localCochainEquiv U P Q e Y hY q).symm b, ?_⟩
  apply (localCochainEquiv U P Q e Y hY (q + 1)).injective
  rw [localCochainEquiv_dd U P Q e Y hY he, AddEquiv.apply_symm_apply, hb]

end Cochains

variable (X : Scheme.{u})
  {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- Affine acyclicity needs only a local trivialization on all opens below
the chosen affine open; the right-derived functor stays in the original
ambient coefficient category. -/
theorem isZero_coefficientCohomology_of_localAffineEquiv
    (hacyc : CechAcyclicInjectives T) (A : 𝒜) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : ∀ (V : X.Opens), V ≤ U → (abPresheaf T A).obj (op V) ≃+ F.presheaf.obj (op V))
    (he : ∀ {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U)
      (s : (abPresheaf T A).obj (op W)),
      e V (hVW.trans hWU) (res (abPresheaf T A) hVW s) =
        res F.presheaf hVW (e W hWU s))
    (n : ℕ) (hn : 0 < n) : IsZero (Hobj T U n A) := by
  let B : Set X.Opens := {V | IsAffineOpen V ∧ V ≤ U}
  let Cov : Set (OpenCover X) := {C | C ∈ Cohomology.Cech.standardCovers X ∧ C.carrier ≤ U}
  refine isZero_Hobj_of_le.{v, w, u, u} T hacyc A B Cov (fun C hC => ?_)
    (fun V hV W hWV => ?_) (fun C hC q hq => ?_)
    (InjectiveResolution.of A) n U ⟨hU, le_rfl⟩ n hn le_rfl
  · obtain ⟨haff, hmem, hinter⟩ := Cohomology.Cech.affineOpens_of_mem_standardCovers C hC.1
    refine ⟨⟨haff, hC.2⟩, fun i => ⟨hmem i, (C.obj_le i).trans hC.2⟩, fun q s => ?_⟩
    exact ⟨hinter q s, (iInf_le (fun j => C.obj (s j)) 0).trans ((C.obj_le _).trans hC.2)⟩
  · obtain ⟨C, hC, hCV, hCW⟩ := Cohomology.Cech.exists_mem_standardCovers_refines hV.1 W hWV
    exact ⟨C, ⟨hC, hCV.symm ▸ hV.2⟩, hCV, hCW⟩
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    apply (cechSurj_iff_isZero_homology C.obj (abPresheaf T A) q).1
    apply cechSurj_of_localEquiv U (abPresheaf T A) F.presheaf e C.obj
      (fun i => (C.obj_le i).trans hC.2) he q
    exact (cechSurj_iff_isZero_homology C.obj F.presheaf q).2
      (Cohomology.Cech.cechCohomologyIsZero_of_mem_standardCovers F C hC.1
        (q + 1) (Nat.succ_pos q))

end

end HodgeConjecture.SheafCohomology
