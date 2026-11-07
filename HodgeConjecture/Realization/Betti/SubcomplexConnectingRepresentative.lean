module

public import HodgeConjecture.Realization.Betti.SubcomplexCochains
public import Mathlib.Algebra.Homology.ConcreteCategory

@[expose] public section

/-!
# Representatives for the original simplicial-cover connecting morphism

The native connecting morphism sends an overlap cocycle to the class of
the differential of any actual pair-cochain lift. The sign is positive:
the pair differential is the restriction of the resulting union cocycle.
Existence below follows from the original degreewise exact cochain sequence,
and supplies an actual representative rather than only a dimension argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SubcomplexConnectingRepresentative

open CategoryTheory HomologicalComplex SubcomplexCochains

universe u

/-- Actual closed simplex-function cochains. -/
abbrev Cocycle (S : SSet.{u}) (n : ℕ) := LinearMap.ker (differential S n)

/-- The native cohomology class of an actual cocycle representative. -/
def cocycleClass (S : SSet.{u}) (n : ℕ) (φ : Cocycle S n) : (complex S).homology n :=
  (complex S).homologyπ n
    ((complex S).cyclesMk φ.val (n + 1) (by simp) (by
      rw [complex_d]
      change differential S n φ.val = 0
      exact φ.property))

/-- Every actual cohomology class has an original closed simplex-function representative. -/
theorem cocycleClass_surjective (S : SSet.{u}) (n : ℕ) :
    Function.Surjective (cocycleClass S n) := by
  intro z
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((complex S).homologyπ n)).mp inferInstance z
  let φ : Cocycle S n := ⟨(complex S).iCycles n c, by
    have h := congrArg (fun g ↦ g c) ((complex S).iCycles_d n (n + 1))
    rw [complex_d] at h
    exact h⟩
  refine ⟨φ, ?_⟩
  rw [cocycleClass]
  have hcycles : (complex S).cyclesMk φ.val (n + 1) (by simp) (by
      rw [complex_d]
      exact φ.property) = c := by
    apply (ModuleCat.mono_iff_injective ((complex S).iCycles n)).mp inferInstance
    exact (complex S).i_cyclesMk (i := n) φ.val (n + 1) (by simp) (by
      rw [complex_d]
      exact φ.property)
  rw [hcycles]
  exact hc

/-- Original simplicial pullback preserves actual cocycle representatives. -/
def cocyclePullback {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ) (φ : Cocycle T n) :
    Cocycle S n :=
  ⟨(pullback f).f n φ.val, by
    have he := congrArg (fun g ↦ g.hom φ.val) ((pullback f).comm n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, complex_d] at he
    change differential S n ((pullback f).f n φ.val) =
      (pullback f).f (n + 1) (differential T n φ.val) at he
    rw [φ.property, map_zero] at he
    exact he⟩

/-- Native cocycle classes commute with the original simplicial pullback. -/
theorem cocycleClass_pullback {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ)
    (φ : Cocycle T n) :
    homologyMap (pullback f) n (cocycleClass T n φ) =
      cocycleClass S n (cocyclePullback f n φ) := by
  let c := (complex T).cyclesMk φ.val (n + 1) (by simp) (by
    rw [complex_d]
    exact φ.property)
  let d := (complex S).cyclesMk (cocyclePullback f n φ).val (n + 1) (by simp) (by
    rw [complex_d]
    exact (cocyclePullback f n φ).property)
  have hc : (complex T).iCycles n c = φ.val :=
    (complex T).i_cyclesMk (i := n) φ.val (n + 1) (by simp) (by
      rw [complex_d]
      exact φ.property)
  have hd : (complex S).iCycles n d = (cocyclePullback f n φ).val :=
    (complex S).i_cyclesMk (i := n) (cocyclePullback f n φ).val (n + 1) (by simp) (by
      rw [complex_d]
      exact (cocyclePullback f n φ).property)
  have hcycles : cyclesMap (pullback f) n c = d := by
    apply (ModuleCat.mono_iff_injective ((complex S).iCycles n)).mp inferInstance
    have h := congrArg (fun g ↦ g c) (cyclesMap_i (pullback f) n)
    change (complex S).iCycles n (cyclesMap (pullback f) n c) =
      (pullback f).f n ((complex T).iCycles n c) at h
    rw [hc] at h
    exact h.trans hd.symm
  have h := congrArg (fun g ↦ g c) (homologyπ_naturality (pullback f) n)
  change homologyMap (pullback f) n ((complex T).homologyπ n c) =
    (complex S).homologyπ n (cyclesMap (pullback f) n c) at h
  rw [hcycles] at h
  exact h

variable {S : SSet.{u}} (A B : S.Subcomplex)

/-- An actual cochain lifting an overlap cocycle has a closed differential on the union. -/
theorem differential_eq_zero_of_restriction_eq (n : ℕ) (v : PairCochain A B n)
    (w : Cochain ((A ⊔ B : S.Subcomplex) : SSet) (n + 1))
    (hw : coverRestrictionLinear A B (n + 1) w = pairDifferential A B n v) :
    differential ((A ⊔ B : S.Subcomplex) : SSet) (n + 1) w = 0 := by
  have h := (coverShortComplex_shortExact A B).d_eq_zero_of_f_eq_d_apply n (n + 1) v w
    (by
      change (coverRestriction A B).f (n + 1) w = (pairComplex A B).d n (n + 1) v
      rw [pairComplex_d]
      exact hw)
    ((n + 1) + 1)
  change (complex ((A ⊔ B : S.Subcomplex) : SSet)).d (n + 1) ((n + 1) + 1) w = 0 at h
  rw [complex_d] at h
  exact h

/-- The actual native boundary is represented by the differential of an actual pair lift.
There is no extra sign in this convention. -/
theorem connecting_cocycleClass (n : ℕ)
    (u : Cocycle ((A ⊓ B : S.Subcomplex) : SSet) n)
    (v : PairCochain A B n)
    (w : Cocycle ((A ⊔ B : S.Subcomplex) : SSet) (n + 1))
    (hv : coverDifferenceLinear A B n v = u.val)
    (hw : coverRestrictionLinear A B (n + 1) w.val = pairDifferential A B n v) :
    connecting A B n (cocycleClass _ n u) = cocycleClass _ (n + 1) w := by
  exact (coverShortComplex_shortExact A B).δ_apply n (n + 1) (by simp)
    u.val (by
      change (complex ((A ⊓ B : S.Subcomplex) : SSet)).d n (n + 1) u.val = 0
      rw [complex_d]
      exact u.property) v hv w.val
    (by
      change (coverRestriction A B).f (n + 1) w.val = (pairComplex A B).d n (n + 1) v
      rw [pairComplex_d]
      exact hw) ((n + 1) + 1) (by simp)

/-- Every original overlap cocycle has an actual pair lift and a closed union
representative whose restrictions are precisely the differential of that lift. -/
theorem exists_connecting_representative (n : ℕ)
    (u : Cocycle ((A ⊓ B : S.Subcomplex) : SSet) n) :
    ∃ (v : PairCochain A B n)
      (w : Cocycle ((A ⊔ B : S.Subcomplex) : SSet) (n + 1)),
      coverDifferenceLinear A B n v = u.val ∧
      coverRestrictionLinear A B (n + 1) w.val = pairDifferential A B n v ∧
      connecting A B n (cocycleClass _ n u) = cocycleClass _ (n + 1) w := by
  obtain ⟨v, hv⟩ := coverDifferenceLinear_surjective A B n u.val
  have hc : coverDifferenceLinear A B (n + 1) (pairDifferential A B n v) = 0 := by
    have h := (coverDifference A B).comm n (n + 1)
    have he := congrArg (fun f ↦ f.hom v) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, complex_d, pairComplex_d] at he
    change differential ((A ⊓ B : S.Subcomplex) : SSet) n
      (coverDifferenceLinear A B n v) =
        coverDifferenceLinear A B (n + 1) (pairDifferential A B n v) at he
    rw [hv, u.property] at he
    exact he.symm
  let w := glueFunction A B (n + 1) (pairDifferential A B n v)
  have hw : coverRestrictionLinear A B (n + 1) w = pairDifferential A B n v :=
    coverRestrictionLinear_glueFunction A B (n + 1) _ hc
  let z : Cocycle ((A ⊔ B : S.Subcomplex) : SSet) (n + 1) :=
    ⟨w, differential_eq_zero_of_restriction_eq A B n v w hw⟩
  exact ⟨v, z, hv, hw, connecting_cocycleClass A B n u v z hv hw⟩

end HodgeConjecture.SubcomplexConnectingRepresentative
