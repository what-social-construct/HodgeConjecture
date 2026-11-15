module

public import HodgeConjecture.Realization.Betti.SingularPresheaf
public import HodgeConjecture.Realization.Betti.SingularContractible
public import Mathlib.Topology.Homotopy.LocallyContractible
public import HodgeConjecture.SheafCohomology.ConstantLift

@[expose] public section

/-!
# Local exactness of the original rational singular cochains

Contractible neighborhood bases give actual cochain primitives after
restriction to a smaller open set. Neighborhoods in the basis need not
themselves be open: the primitive is constructed there, then restricted.
The degree-zero statement uses the existing path-connected calculation.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory TopologicalSpace Opposite Topology Filter

/-- The constant zero-cochain on the original singular simplices. -/
def constantCochain (X : TopCat.{0}) : ℚ →ₗ[ℚ] Cochain X 0 where
  toFun q := fun _ ↦ q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem differential_constantCochain (X : TopCat.{0}) (q : ℚ) :
    differential X 0 (constantCochain X q) = 0 := by
  funext σ
  rw [differential_apply, Fin.sum_univ_two]
  simp [constantCochain]

@[simp]
theorem pullback_constantCochain {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℚ) :
    (pullback f).f 0 (constantCochain Y q) = constantCochain X q := rfl

theorem constantCochain_injective (X : TopCat.{0}) [Nonempty X] :
    Function.Injective (constantCochain X) := by
  intro a b h
  exact congrFun h ((SingularDegreeZero.simplexEquivSingularSet X 0)
    (SingularDegreeZero.pointSimplex X (Classical.choice ‹Nonempty X›)))

/-- This uses the same constant presheaf as the holomorphic augmentation. -/
def constantPresheafMap (X : TopCat.{0}) :
    SheafCohomology.ConstantLift.presheaf ℚ X ⟶ presheaf X 0 where
  app U := ModuleCat.ofHom (constantCochain ((Opens.toTopCat X).obj U.unop))
  naturality _ _ _ := rfl

theorem constantPresheafMap_differential (X : TopCat.{0}) :
    constantPresheafMap X ≫ presheafDifferential X 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact differential_constantCochain _

variable (X : TopCat.{0}) [StronglyLocallyContractibleSpace X]

/-- Closed original positive cochains have actual local primitives. -/
theorem locally_exact_positive (n : ℕ) (U : Opens X)
    (z : Cochain ((Opens.toTopCat X).obj U) (n + 1))
    (hz : differential ((Opens.toTopCat X).obj U) (n + 1) z = 0)
    (p : X) (hp : p ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), p ∈ V ∧
      ∃ b : Cochain ((Opens.toTopCat X).obj V) n,
        differential ((Opens.toTopCat X).obj V) n b =
          (presheaf X (n + 1)).map (homOfLE hVU).op z := by
  have hpos (S : TopCat.{0}) [ContractibleSpace S] (j : ℕ)
      (w : (complex S).X (j + 1)) (hw : (complex S).d (j + 1) (j + 2) w = 0) :
      ∃ b : (complex S).X j, (complex S).d j (j + 1) b = w := by
    rw [complex_d] at hw
    obtain ⟨b, hb⟩ := SingularContractible.exists_primitive S j w hw
    refine ⟨b, ?_⟩
    rw [complex_d]
    exact hb
  have hz' : (presheafDifferential X (n + 1)).app (op U) z = 0 := by
    change (complex ((Opens.toTopCat X).obj U)).d (n + 1) (n + 2) z = 0
    rw [complex_d]
    exact hz
  obtain ⟨V, hVU, hpV, b, hb⟩ :=
    SheafCohomology.CochainPresheaf.locally_exact_positive ℚ functor X hpos n U z hz' p hp
  refine ⟨V, hVU, hpV, b, ?_⟩
  change (complex ((Opens.toTopCat X).obj V)).d n (n + 1) b = _ at hb
  rw [complex_d] at hb
  exact hb

/-- Closed zero-cochains restrict to literal constants on a neighborhood. -/
theorem locally_constant_zero (U : Opens X)
    (z : Cochain ((Opens.toTopCat X).obj U) 0)
    (hz : differential ((Opens.toTopCat X).obj U) 0 z = 0)
    (p : X) (hp : p ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), p ∈ V ∧ ∃ q : ℚ,
      constantCochain ((Opens.toTopCat X).obj V) q =
        (presheaf X 0).map (homOfLE hVU).op z := by
  have hzero (S : TopCat.{0}) [ContractibleSpace S] (x : S) (w : (complex S).X 0)
      (hw : (complex S).d 0 1 w = 0) : ∃ q : ℚ, constantCochain S q = w := by
    let a : Cocycle S 0 := ⟨w, by
      rw [LinearMap.mem_ker]
      rw [complex_d] at hw
      exact hw⟩
    refine ⟨SingularDegreeZero.eval S (kernelZeroCoordinates S a) x, ?_⟩
    apply (continuousCochainEquiv S 0).injective
    exact congrArg Subtype.val (SingularDegreeZero.constantClass_eval S x (kernelZeroCoordinates S a))
  have hz' : (presheafDifferential X 0).app (op U) z = 0 := by
    change (complex ((Opens.toTopCat X).obj U)).d 0 1 z = 0
    rw [complex_d]
    exact hz
  exact SheafCohomology.CochainPresheaf.locally_constant_zero ℚ functor X constantCochain
    (fun f q ↦ pullback_constantCochain f q) hzero U z hz' p hp

end HodgeConjecture.SingularCochains
