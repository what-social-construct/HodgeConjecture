module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import HodgeConjecture.Realization.Transfer
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

/-!
# Native singular cochains of a topological split double cover

Every actual singular simplex in a topological disjoint sum lies in one
sheet, by connectedness of the standard simplex. Extension by zero and
restriction decompose the original singular cochain complex and therefore
its original categorical cohomology. Transfer is the sum of the two actual
inclusion pullbacks. No scheme, Chow group, or Hodge coordinates are used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularDoubleCover

open Classical CategoryTheory Opposite Simplicial HomologicalComplex
open SingularCochains

variable (X : TopCat.{0})

/-- The actual topological disjoint sum of two copies of the original space. -/
abbrev space : TopCat.{0} := TopCat.of (X ⊕ X)

def inclusion (sheet : Bool) : X ⟶ space X :=
  TopCat.ofHom (if sheet then ⟨Sum.inr, continuous_inr⟩ else ⟨Sum.inl, continuous_inl⟩)

def fold : space X ⟶ X :=
  TopCat.ofHom ⟨Sum.elim id id,
    continuous_sum_dom.mpr ⟨continuous_id, continuous_id⟩⟩

def sheet : C(space X, Bool) :=
  ⟨Sum.elim (fun _ ↦ false) (fun _ ↦ true),
    continuous_sum_dom.mpr ⟨continuous_const, continuous_const⟩⟩

@[simp]
theorem inclusion_fold (b : Bool) : inclusion X b ≫ fold X = 𝟙 X := by
  cases b <;> rfl

def simplexBase (n : ℕ) : SimplexCategory.toTop.{0}.obj ⦋n⦌ :=
  Classical.choice inferInstance

def simplexMap (Y : TopCat.{0}) (n : ℕ) (σ : Simplex Y n) :
    SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ Y := σ.down

/-- A sheet label read on the actual singular simplex, rather than supplied
as an additional coordinate on cohomology. -/
def simplexSheet (n : ℕ) (σ : Simplex (space X) n) : Bool :=
  sheet X (simplexMap (space X) n σ (simplexBase n))

theorem simplexSheet_at (n : ℕ) (σ : Simplex (space X) n)
    (t : SimplexCategory.toTop.{0}.obj ⦋n⦌) :
    sheet X (simplexMap (space X) n σ t) = simplexSheet X n σ := by
  haveI : ConnectedSpace (SimplexCategory.toTop.{0}.obj ⦋n⦌) := by
    change ConnectedSpace (ULift (Convexity.StdSimplex ℝ (Fin (n + 1))))
    exact (Homeomorph.connectedSpace_iff
      (Homeomorph.ulift : ULift (Convexity.StdSimplex ℝ (Fin (n + 1))) ≃ₜ _)).mpr
      inferInstance
  exact PreconnectedSpace.constant inferInstance
    ((sheet X).continuous.comp (simplexMap (space X) n σ).hom.continuous)

theorem simplexSheet_face (n : ℕ) (σ : Simplex (space X) (n + 1))
    (i : Fin (n + 2)) :
    simplexSheet X n (face (space X) σ i) = simplexSheet X (n + 1) σ := by
  change sheet X (simplexMap (space X) (n + 1) σ
    ((SimplexCategory.toTop.map (SimplexCategory.δ i))
    (simplexBase n))) = simplexSheet X (n + 1) σ
  exact simplexSheet_at X (n + 1) σ _

@[simp]
theorem simplexSheet_inclusion (n : ℕ) (b : Bool) (σ : Simplex X n) :
    simplexSheet X n ((TopCat.toSSet.map (inclusion X b)).app (op ⦋n⦌) σ) = b := by
  change sheet X (inclusion X b (simplexMap X n σ (simplexBase n))) = b
  cases b <;> rfl

@[simp]
theorem fold_inclusion_simplex (n : ℕ) (b : Bool) (σ : Simplex X n) :
    (TopCat.toSSet.map (fold X)).app (op ⦋n⦌)
      ((TopCat.toSSet.map (inclusion X b)).app (op ⦋n⦌) σ) = σ := by
  apply ULift.ext
  change simplexMap X n σ ≫ inclusion X b ≫ fold X = simplexMap X n σ
  rw [inclusion_fold, Category.comp_id]

private theorem inclusion_fold_of_sheet (b : Bool) (x : space X)
    (h : sheet X x = b) : inclusion X b (fold X x) = x := by
  cases b <;> cases x <;> simp_all [sheet, inclusion, fold]

/-- A simplex factors through its actual sheet inclusion. -/
theorem inclusion_fold_simplex (n : ℕ) (b : Bool) (σ : Simplex (space X) n)
    (h : simplexSheet X n σ = b) :
    (TopCat.toSSet.map (inclusion X b)).app (op ⦋n⦌)
      ((TopCat.toSSet.map (fold X)).app (op ⦋n⦌) σ) = σ := by
  apply ULift.ext
  change simplexMap (space X) n σ ≫ fold X ≫ inclusion X b = simplexMap (space X) n σ
  ext t : 1
  change inclusion X b (fold X (simplexMap (space X) n σ t)) =
    simplexMap (space X) n σ t
  exact inclusion_fold_of_sheet X b _ ((simplexSheet_at X n σ t).trans h)

/-- Extension by zero from one actual sheet, using the original folded simplex. -/
def extensionLinear (b : Bool) (n : ℕ) : Cochain X n →ₗ[ℚ] Cochain (space X) n where
  toFun φ σ := if simplexSheet X n σ = b then (pullback (fold X)).f n φ σ else 0
  map_add' φ ψ := by
    funext σ
    by_cases h : simplexSheet X n σ = b <;> simp [h]
  map_smul' r φ := by
    funext σ
    by_cases h : simplexSheet X n σ = b <;> simp [h]

@[simp]
theorem extensionLinear_apply (b : Bool) (n : ℕ) (φ : Cochain X n)
    (σ : Simplex (space X) n) :
    extensionLinear X b n φ σ =
      if simplexSheet X n σ = b then (pullback (fold X)).f n φ σ else 0 := rfl

theorem differential_extension (b : Bool) (n : ℕ) (φ : Cochain X n) :
    differential (space X) n (extensionLinear X b n φ) =
      extensionLinear X b (n + 1) (differential X n φ) := by
  funext σ
  have hc := congrFun (differential_pullback (fold X) n φ) σ
  rw [differential_apply] at hc
  rw [differential_apply]
  simp only [extensionLinear_apply, simplexSheet_face]
  by_cases h : simplexSheet X (n + 1) σ = b
  · simpa only [ite_eq_left h] using hc
  · simp only [ite_eq_right h, smul_zero, Finset.sum_const_zero]

/-- A morphism of the original singular cochain complexes, proved from the
actual alternating differential. -/
def extension (b : Bool) : complex X ⟶ complex (space X) :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (extensionLinear X b n)) (by
    intro n
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact differential_extension X b n φ)

theorem extension_restriction_same (b : Bool) :
    extension X b ≫ pullback (inclusion X b) = 𝟙 (complex X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change (if simplexSheet X n
      ((TopCat.toSSet.map (inclusion X b)).app (op ⦋n⦌) σ) = b then
    φ ((TopCat.toSSet.map (fold X)).app (op ⦋n⦌)
      ((TopCat.toSSet.map (inclusion X b)).app (op ⦋n⦌) σ)) else 0) = φ σ
  simp only [simplexSheet_inclusion, fold_inclusion_simplex, ite_true]

theorem extension_restriction_other (b c : Bool) (h : c ≠ b) :
    extension X b ≫ pullback (inclusion X c) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change (if simplexSheet X n
      ((TopCat.toSSet.map (inclusion X c)).app (op ⦋n⦌) σ) = b then _ else 0) = 0
  simp only [simplexSheet_inclusion, ite_eq_right h]

/-- The original cochains are recovered from their two actual restrictions. -/
theorem cochain_reassembly :
    pullback (inclusion X false) ≫ extension X false +
      pullback (inclusion X true) ≫ extension X true = 𝟙 (complex (space X)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change (if simplexSheet X n σ = false then
      φ ((TopCat.toSSet.map (inclusion X false)).app (op ⦋n⦌)
        ((TopCat.toSSet.map (fold X)).app (op ⦋n⦌) σ)) else 0) +
    (if simplexSheet X n σ = true then
      φ ((TopCat.toSSet.map (inclusion X true)).app (op ⦋n⦌)
        ((TopCat.toSSet.map (fold X)).app (op ⦋n⦌) σ)) else 0) = φ σ
  cases h : simplexSheet X n σ
  · simp only [Bool.false_eq_true, ite_true, ite_false, add_zero]
    rw [inclusion_fold_simplex X n false σ h]
  · simp only [Bool.true_eq_false, ite_true, ite_false, zero_add]
    rw [inclusion_fold_simplex X n true σ h]

/-- Actual singular restriction to one summand. -/
def restriction (b : Bool) (n : ℕ) : Cohomology (space X) n →ₗ[ℚ] Cohomology X n :=
  (cohomologyPullback (inclusion X b) n).hom

/-- The map on original categorical cohomology induced by extension of cochains. -/
def cohomologyExtension (b : Bool) (n : ℕ) :
    Cohomology X n →ₗ[ℚ] Cohomology (space X) n :=
  (HomologicalComplex.homologyMap (extension X b) n).hom

theorem restriction_extension_same (b : Bool) (n : ℕ) :
    (restriction X b n).comp (cohomologyExtension X b n) = LinearMap.id := by
  have h := congrArg (fun f : complex X ⟶ complex X ↦
    (HomologicalComplex.homologyMap f n).hom)
    (extension_restriction_same X b)
  simpa only [homologyMap_comp, homologyMap_id, ModuleCat.hom_comp,
    ModuleCat.hom_id, restriction, cohomologyExtension, cohomologyPullback] using h

theorem restriction_extension_other (b c : Bool) (hbc : c ≠ b) (n : ℕ) :
    (restriction X c n).comp (cohomologyExtension X b n) = 0 := by
  have h := congrArg (fun f : complex X ⟶ complex X ↦
    (HomologicalComplex.homologyMap f n).hom)
    (extension_restriction_other X b c hbc)
  simpa only [homologyMap_comp, homologyMap_zero, ModuleCat.hom_comp,
    ModuleCat.hom_zero, restriction, cohomologyExtension, cohomologyPullback] using h

theorem cohomology_reassembly (n : ℕ) :
    (cohomologyExtension X false n).comp (restriction X false n) +
      (cohomologyExtension X true n).comp (restriction X true n) = LinearMap.id := by
  have h := congrArg (fun f : complex (space X) ⟶ complex (space X) ↦
    (HomologicalComplex.homologyMap f n).hom)
    (cochain_reassembly X)
  simpa only [homologyMap_add, homologyMap_comp, homologyMap_id,
    ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, restriction,
    cohomologyExtension, cohomologyPullback] using h

/-- Native singular cohomology of an actual double sum decomposes by actual
inclusion pullbacks, independently of every Chow construction. -/
def cohomologyEquiv (n : ℕ) :
    Cohomology (space X) n ≃ₗ[ℚ] Cohomology X n × Cohomology X n where
  toFun a := (restriction X false n a, restriction X true n a)
  invFun a := cohomologyExtension X false n a.1 + cohomologyExtension X true n a.2
  left_inv a := by
    exact LinearMap.congr_fun (cohomology_reassembly X n) a
  right_inv a := by
    apply Prod.ext
    · change restriction X false n (_ + _) = a.1
      rw [map_add]
      have h₁ := LinearMap.congr_fun (restriction_extension_same X false n) a.1
      have h₂ := LinearMap.congr_fun
        (restriction_extension_other X true false Bool.false_ne_true n) a.2
      exact (congrArg₂ (· + ·) h₁ h₂).trans (add_zero _)
    · change restriction X true n (_ + _) = a.2
      rw [map_add]
      have h₁ := LinearMap.congr_fun
        (restriction_extension_other X false true (Ne.symm Bool.false_ne_true) n) a.1
      have h₂ := LinearMap.congr_fun (restriction_extension_same X true n) a.2
      exact (congrArg₂ (· + ·) h₁ h₂).trans (zero_add _)
  map_add' _ _ := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' _ _ := Prod.ext (map_smul _ _ _) (map_smul _ _ _)

/-- Transfer is defined on the actual cochain complex as the sum of its
two geometric restriction maps. -/
def cochainPush : complex (space X) ⟶ complex X :=
  pullback (inclusion X false) + pullback (inclusion X true)

/-- The degree-two identity already holds on the original singular cochain
complex, before passing to cohomology. -/
theorem cochainPush_pullback :
    pullback (fold X) ≫ cochainPush X = 𝟙 (complex X) + 𝟙 (complex X) := by
  rw [cochainPush, Preadditive.comp_add, ← pullback_comp, ← pullback_comp]
  simp only [inclusion_fold, pullback_id]

def actualPush (n : ℕ) : Cohomology (space X) n →ₗ[ℚ] Cohomology X n :=
  restriction X false n + restriction X true n

theorem actualPush_eq_homologyMap (n : ℕ) :
    actualPush X n = (HomologicalComplex.homologyMap (cochainPush X) n).hom := by
  simp only [actualPush, cochainPush, homologyMap_add]
  rfl

def actualPull (n : ℕ) : Cohomology X n →ₗ[ℚ] Cohomology (space X) n :=
  (cohomologyPullback (fold X) n).hom

theorem restriction_actualPull (b : Bool) (n : ℕ) :
    (restriction X b n).comp (actualPull X n) = LinearMap.id := by
  have h := cohomologyPullback_comp (inclusion X b) (fold X) n
  rw [inclusion_fold, cohomologyPullback_id] at h
  exact congrArg ModuleCat.Hom.hom h.symm

theorem actualPush_actualPull (n : ℕ) :
    (actualPush X n).comp (actualPull X n) = (2 : ℚ) • LinearMap.id := by
  rw [actualPush, LinearMap.add_comp, restriction_actualPull, restriction_actualPull]
  simp only [two_smul]

def degreeTransfer (n : ℕ) :
    RationalDegreeTransfer (Cohomology (space X) n) (Cohomology X n) where
  pull := actualPull X n
  push := actualPush X n
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := actualPush_actualPull X n

end HodgeConjecture.SingularDoubleCover

end
