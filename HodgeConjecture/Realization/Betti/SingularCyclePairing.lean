module

public import HodgeConjecture.Realization.Betti.CochainDualCoordinates
public import HodgeConjecture.Realization.Betti.ChainHomologyClasses
public import Mathlib.Algebra.Homology.ConcreteCategory

@[expose] public section

/-!
# Actual rational singular cycle evaluation

An original cochain evaluates on a finite chain through the proved native
chain-coordinate duality. A closed chain kills all coboundaries. The native
homology cokernel therefore descends this evaluation to actual singular
cohomology, retaining cocycle representatives and original simplicial maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularCyclePairing

open CategoryTheory HomologicalComplex Opposite Simplicial

/-- Evaluate an original cochain on an original native finite chain. -/
def evaluation (S : SSet.{0}) (n : ℕ) (c : (SingularChainCoordinates.complex S).X n) :
    SubcomplexCochains.Cochain S n →ₗ[ℚ] ℚ where
  toFun φ := (CochainDualCoordinates.coordinates S n).symm φ c
  map_add' φ ψ := by simp
  map_smul' q φ := by simp

@[simp]
theorem evaluation_add (S : SSet.{0}) (n : ℕ)
    (c d : (SingularChainCoordinates.complex S).X n)
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S n (c + d) φ = evaluation S n c φ + evaluation S n d φ :=
  map_add ((CochainDualCoordinates.coordinates S n).symm φ) c d

@[simp]
theorem evaluation_smul (S : SSet.{0}) (n : ℕ) (q : ℚ)
    (c : (SingularChainCoordinates.complex S).X n)
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S n (q • c) φ = q • evaluation S n c φ :=
  map_smul ((CochainDualCoordinates.coordinates S n).symm φ) q c

/-- Evaluation is the actual finite sum of original simplex values. -/
theorem evaluation_coordinates (S : SSet.{0}) (n : ℕ)
    (c : S.obj (op ⦋n⦌) →₀ ℚ) (φ : SubcomplexCochains.Cochain S n) :
    evaluation S n (SingularChainCoordinates.coordinates S n c) φ =
      Finsupp.llift ℚ ℚ ℚ (S.obj (op ⦋n⦌)) φ c := by
  change (CochainDualCoordinates.coordinates S n).symm φ
    (SingularChainCoordinates.coordinates S n c) = _
  rw [CochainDualCoordinates.coordinates_symm_apply,
    LinearEquiv.symm_apply_apply]

@[simp]
theorem evaluation_single (S : SSet.{0}) (n : ℕ)
    (σ : S.obj (op ⦋n⦌)) (a : ℚ) (φ : SubcomplexCochains.Cochain S n) :
    evaluation S n (SingularChainCoordinates.coordinates S n (Finsupp.single σ a)) φ =
      a * φ σ := CochainDualCoordinates.coordinates_symm_coordinates_single S n φ σ a

/-- Evaluation of a coboundary equals evaluation on the original chain boundary. -/
theorem evaluation_differential (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S (n + 1) c (SubcomplexCochains.differential S n φ) =
      evaluation S n ((SingularChainCoordinates.complex S).d (n + 1) n c) φ := by
  have h := CochainDualCoordinates.coordinates_differential S n
    ((CochainDualCoordinates.coordinates S n).symm φ)
  rw [LinearEquiv.apply_symm_apply] at h
  have he := congrArg (fun ψ ↦ (CochainDualCoordinates.coordinates S (n + 1)).symm ψ c) h
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- Actual coboundaries evaluate to zero on an actual closed chain. -/
theorem evaluation_differential_eq_zero (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0)
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S (n + 1) c (SubcomplexCochains.differential S n φ) = 0 := by
  rw [evaluation_differential, hc]
  change ((CochainDualCoordinates.coordinates S n).symm φ) 0 = 0
  exact map_zero _

/-- An actual closed cochain annihilates every original chain boundary. -/
theorem evaluation_boundary_eq_zero (S : SSet.{0}) (n : ℕ)
    (b : (SingularChainCoordinates.complex S).X (n + 1))
    (φ : SubcomplexCochains.Cochain S n)
    (hφ : SubcomplexCochains.differential S n φ = 0) :
    evaluation S n ((SingularChainCoordinates.complex S).d (n + 1) n b) φ = 0 := by
  rw [← evaluation_differential, hφ, map_zero]

/-- Original simplicial pullback is adjoint to the original native chain map. -/
theorem evaluation_pullback {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X n)
    (φ : SubcomplexCochains.Cochain T n) :
    evaluation S n c ((SubcomplexCochains.pullback f).f n φ) =
      evaluation T n ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n c) φ := by
  have h := CochainDualCoordinates.coordinates_naturality f n
    ((CochainDualCoordinates.coordinates T n).symm φ)
  rw [LinearEquiv.apply_symm_apply] at h
  have he := congrArg (fun ψ ↦ (CochainDualCoordinates.coordinates S n).symm ψ c) h
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- The original cocycle-functional annihilates the native incoming boundary map. -/
theorem toCycles_evaluation_eq_zero (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0) :
    ((SubcomplexCochains.complex S).sc (n + 1)).toCycles ≫
      (SubcomplexCochains.complex S).iCycles (n + 1) ≫
        ModuleCat.ofHom (evaluation S (n + 1) c) = 0 := by
  change (((SubcomplexCochains.complex S).sc (n + 1)).toCycles ≫
    ((SubcomplexCochains.complex S).sc (n + 1)).iCycles) ≫
      ModuleCat.ofHom (evaluation S (n + 1) c) = 0
  rw [ShortComplex.toCycles_i]
  change (SubcomplexCochains.complex S).d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) ≫
    ModuleCat.ofHom (evaluation S (n + 1) c) = 0
  rw [← HomologicalComplex.XIsoOfEq_hom_comp_d (SubcomplexCochains.complex S)
    (CochainComplex.prev_nat_succ n) (n + 1), Category.assoc]
  have hz : (SubcomplexCochains.complex S).d n (n + 1) ≫
      ModuleCat.ofHom (evaluation S (n + 1) c) = 0 := by
    rw [SubcomplexCochains.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact evaluation_differential_eq_zero S n c hc φ
  rw [hz]
  simp

/-- The actual rational Kronecker functional of an original positive-degree closed chain. -/
def pairing (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0) :
    (SubcomplexCochains.complex S).homology (n + 1) ⟶ ModuleCat.of ℚ ℚ :=
  ((SubcomplexCochains.complex S).sc (n + 1)).descHomology
    ((SubcomplexCochains.complex S).iCycles (n + 1) ≫
      ModuleCat.ofHom (evaluation S (n + 1) c))
    (toCycles_evaluation_eq_zero S n c hc)

/-- The descended pairing evaluates every actual native cocycle representative. -/
theorem pairing_homologyπ (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0) :
    (SubcomplexCochains.complex S).homologyπ (n + 1) ≫ pairing S n c hc =
      (SubcomplexCochains.complex S).iCycles (n + 1) ≫
        ModuleCat.ofHom (evaluation S (n + 1) c) :=
  ShortComplex.π_descHomology _ _ _

/-- Pairing with a native `π(cyclesMk φ)` class is the literal original cochain evaluation. -/
theorem pairing_cocycleClass (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0)
    (φ : SubcomplexCochains.Cochain S (n + 1))
    (hφ : SubcomplexCochains.differential S (n + 1) φ = 0) :
    pairing S n c hc
      ((SubcomplexCochains.complex S).homologyπ (n + 1)
        ((SubcomplexCochains.complex S).cyclesMk φ ((n + 1) + 1) (by simp)
          (by rw [SubcomplexCochains.complex_d]
              change SubcomplexCochains.differential S (n + 1) φ = 0
              exact hφ))) =
      evaluation S (n + 1) c φ := by
  have h := congrArg (fun f ↦ f
    ((SubcomplexCochains.complex S).cyclesMk φ ((n + 1) + 1) (by simp)
      (by rw [SubcomplexCochains.complex_d]
          change SubcomplexCochains.differential S (n + 1) φ = 0
          exact hφ)))
    (pairing_homologyπ S n c hc)
  change pairing S n c hc _ = evaluation S (n + 1) c
    ((SubcomplexCochains.complex S).iCycles (n + 1) _) at h
  have hi := (SubcomplexCochains.complex S).i_cyclesMk φ ((n + 1) + 1) (by simp)
    (by rw [SubcomplexCochains.complex_d]
        change SubcomplexCochains.differential S (n + 1) φ = 0
        exact hφ)
  change (SubcomplexCochains.complex S).iCycles (n + 1) _ = φ at hi
  rw [hi] at h
  exact h

/-- The original simplicial chain map sends an actual closed chain to an actual closed chain. -/
theorem chainMap_closed {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0) :
    (SingularChainCoordinates.complex T).d (n + 1) n
      ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f (n + 1) c) = 0 := by
  have h := congrArg (fun p ↦ p c)
    ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).comm (n + 1) n)
  change (SingularChainCoordinates.complex T).d (n + 1) n
    ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f (n + 1) c) =
    (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n
      ((SingularChainCoordinates.complex S).d (n + 1) n c) at h
  rw [h, hc, map_zero]

/-- The descended actual cohomology pairing is natural for original simplicial maps.
This includes full-to-small restriction paired with the original small-chain inclusion. -/
theorem pairing_pullback {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0)
    (hb : (SingularChainCoordinates.complex T).d (n + 1) n
      ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f (n + 1) c) = 0) :
    homologyMap (SubcomplexCochains.pullback f) (n + 1) ≫ pairing S n c hc =
      pairing T n ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f (n + 1) c) hb := by
  apply (cancel_epi ((SubcomplexCochains.complex T).homologyπ (n + 1))).mp
  rw [homologyπ_naturality_assoc, pairing_homologyπ, pairing_homologyπ,
    cyclesMap_i_assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact evaluation_pullback f (n + 1) c φ

end HodgeConjecture.SingularCyclePairing
