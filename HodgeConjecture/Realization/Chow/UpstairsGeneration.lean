import HodgeConjecture.Realization.HodgeClasses
import HodgeConjecture.Realization.Chow.TransferProjector

/-!
# Upstairs cycle recipes and prescribed Hodge classes

The generation condition uses a specified cycle recipe, the independently
defined downstairs Hodge subspace, and a supplied cohomological pullback.
It asks only for representatives of pulled-back downstairs Hodge classes.
The indexed version allows the chosen recipe and cover to vary with the
class, while their maps are fixed before the class is quantified.

The forward implication reuses `RationalDegreeTransfer` and an explicit
cycle-class/pushforward comparison. No new transfer or projector package is
introduced. These are conditional statements about supplied maps, not a
construction of finite étale covers or of their geometric Chow--Betti maps.
In particular, the generation predicate is an obligation, not an axiom or
an automatically inhabited instance.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe x h y k c i

variable {ChowX : Type x} {HX : Type h}
variable [AddCommGroup ChowX] [Module ℚ ChowX]
variable [AddCommGroup HX] [Module ℚ HX]

section FixedRecipe

variable {ChowY : Type y} {HY : Type k} {Coeff : Type c}
variable [AddCommGroup ChowY] [Module ℚ ChowY]
variable [AddCommGroup HY] [Module ℚ HY]
variable [AddCommGroup Coeff] [Module ℚ Coeff]

/-- The specified recipe represents all pulled-back downstairs Hodge classes;
it need not represent all upstairs Hodge classes or all upstairs cycles. -/
def HodgePullbackGeneratedBy
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ChowY →ₗ[ℚ] HY) (pull : HX →ₗ[ℚ] HY)
    (recipe : Coeff →ₗ[ℚ] ChowY) : Prop :=
  Submodule.map pull M.hodgeClasses ≤ LinearMap.range (clY.comp recipe)

/-- Elementwise form, with the Hodge class specified before its recipe coefficient. -/
theorem hodgePullbackGeneratedBy_iff
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ChowY →ₗ[ℚ] HY) (pull : HX →ₗ[ℚ] HY)
    (recipe : Coeff →ₗ[ℚ] ChowY) :
    HodgePullbackGeneratedBy M clY pull recipe ↔
      ∀ α : HX, IsRationalHodgeClass M α →
        ∃ c : Coeff, clY (recipe c) = pull α := by
  constructor
  · intro h α hα
    exact h ⟨α, hα, rfl⟩
  · intro h b hb
    obtain ⟨α, hα, rfl⟩ := hb
    exact h α hα

/-- The actual normalized Chow pushforward of an upstairs representative
has the prescribed downstairs cycle class, assuming the two transfer laws. -/
theorem normalizedPushforward_cycleClass
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ChowY →ₗ[ℚ] HY) (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX)
    (hPush : M.cycleClass.comp pushCH = T.push.comp clY)
    (z : ChowY) (α : HX) (hz : clY z = T.pull α) :
    M.cycleClass ((T.degree : ℚ)⁻¹ • pushCH z) = α := by
  have hd : (T.degree : ℚ) ≠ 0 := by exact_mod_cast T.degree_ne_zero
  have hc := LinearMap.congr_fun hPush z
  have ht := LinearMap.congr_fun T.push_comp_pull α
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hc ht
  rw [map_smul, hc, hz, ht, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- A proved upstairs recipe-generation condition descends to the existing
Hodge target. It requires neither a deck group nor residual surjectivity. -/
theorem rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ChowY →ₗ[ℚ] HY) (T : RationalDegreeTransfer HY HX)
    (pushCH : ChowY →ₗ[ℚ] ChowX)
    (hPush : M.cycleClass.comp pushCH = T.push.comp clY)
    (recipe : Coeff →ₗ[ℚ] ChowY)
    (generation : HodgePullbackGeneratedBy M clY T.pull recipe) :
    RationalHodgeConjectureAt M := by
  intro α hα
  obtain ⟨c, hc⟩ := (hodgePullbackGeneratedBy_iff M clY T.pull recipe).mp generation α hα
  exact ⟨(T.degree : ℚ)⁻¹ • pushCH (recipe c),
    normalizedPushforward_cycleClass M clY T pushCH hPush (recipe c) α hc⟩

end FixedRecipe

section IndexedRecipes

variable {Index : Type i}
variable {ChowY : Index → Type y} {HY : Index → Type k} {Coeff : Index → Type c}
variable [∀ j, AddCommGroup (ChowY j)] [∀ j, Module ℚ (ChowY j)]
variable [∀ j, AddCommGroup (HY j)] [∀ j, Module ℚ (HY j)]
variable [∀ j, AddCommGroup (Coeff j)] [∀ j, Module ℚ (Coeff j)]

/-- Every independently specified downstairs Hodge class is represented by
one of the supplied upstairs recipes. The index and coefficient may depend
on the class; the maps for each index are fixed in advance. -/
def ClassDependentChowBettiGeneration
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ∀ j, ChowY j →ₗ[ℚ] HY j)
    (pull : ∀ j, HX →ₗ[ℚ] HY j)
    (recipe : ∀ j, Coeff j →ₗ[ℚ] ChowY j) : Prop :=
  ∀ α : HX, IsRationalHodgeClass M α →
    ∃ j : Index, ∃ c : Coeff j, clY j (recipe j c) = pull j α

/-- A single successful recipe supplies the indexed generation condition. -/
theorem classDependentChowBettiGeneration_of_fixed
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ∀ j, ChowY j →ₗ[ℚ] HY j)
    (pull : ∀ j, HX →ₗ[ℚ] HY j)
    (recipe : ∀ j, Coeff j →ₗ[ℚ] ChowY j)
    (j : Index) (generation : HodgePullbackGeneratedBy M (clY j) (pull j) (recipe j)) :
    ClassDependentChowBettiGeneration M clY pull recipe := by
  intro α hα
  obtain ⟨c, hc⟩ := (hodgePullbackGeneratedBy_iff M (clY j) (pull j) (recipe j)).mp
    generation α hα
  exact ⟨j, c, hc⟩

/-- Class-dependent upstairs generation descends through the chosen
positive-degree transfer; all cycle-class comparisons remain explicit. -/
theorem rationalHodgeConjectureAt_of_classDependentChowBettiGeneration
    (M : RationalHodgeCycleClassModel ChowX HX)
    (clY : ∀ j, ChowY j →ₗ[ℚ] HY j)
    (T : ∀ j, RationalDegreeTransfer (HY j) HX)
    (pushCH : ∀ j, ChowY j →ₗ[ℚ] ChowX)
    (hPush : ∀ j, M.cycleClass.comp (pushCH j) = (T j).push.comp (clY j))
    (recipe : ∀ j, Coeff j →ₗ[ℚ] ChowY j)
    (generation : ClassDependentChowBettiGeneration M clY (fun j => (T j).pull) recipe) :
    RationalHodgeConjectureAt M := by
  intro α hα
  obtain ⟨j, c, hc⟩ := generation α hα
  exact ⟨((T j).degree : ℚ)⁻¹ • pushCH j (recipe j c),
    normalizedPushforward_cycleClass M (clY j) (T j) (pushCH j) (hPush j)
      (recipe j c) α hc⟩

end IndexedRecipes

end

end HodgeConjecture
