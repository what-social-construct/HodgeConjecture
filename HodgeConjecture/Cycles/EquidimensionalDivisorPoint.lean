/-
The coheight argument adapts FlatPullbackPrincipalDivisor.lean from
AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.Cycles.FlatComponents
public import HodgeConjecture.Cycles.DimensionFunction

@[expose] public section

/-! Points one degree below all the component generic points have
one-dimensional actual stalks, for the existing dimension function. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

noncomputable section

universe u

/-- A component containing the given point, with membership in its actual closed set. -/
theorem exists_component_containing {X : Scheme.{u}} (x : X) :
    ∃ W : irreducibleComponents X, x ∈ (W : Set X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
    mem_irreducibleComponent⟩

/-- A constant degree on component generic points bounds the degree of every point. -/
theorem dimensionFunction_le_of_component_eq {X : Scheme.{u}} (δ : DimensionFunction X)
    {n : ℤ} (hgen : ∀ W : irreducibleComponents X, δ W.2.1.genericPoint = n) (x : X) :
    δ x ≤ n := by
  obtain ⟨W, hxW⟩ := exists_component_containing x
  rw [← hgen W]
  have hspec := (genericPoints.isGenericPoint_ofComponent W).specializes hxW
  by_cases heq : x = W.2.1.genericPoint
  · rw [heq]
  · apply (δ.strictMono (lt_iff_le_not_ge.mpr
      ⟨Scheme.le_iff_specializes.mpr hspec, ?_⟩)).le
    intro hback
    exact heq ((Scheme.le_iff_specializes.mp hback).antisymm hspec).eq

/-- Every strict generalization of a point one degree below the components is maximal. -/
theorem isMax_of_degree_eq_component_sub_one {X : Scheme.{u}} (δ : DimensionFunction X)
    {n : ℤ} (hgen : ∀ W : irreducibleComponents X, δ W.2.1.genericPoint = n)
    {x z : X} (hx : δ x = n - 1) (hxz : x < z) : IsMax z := by
  have hdz : δ z = n := by
    have hlt := δ.strictMono hxz
    have hle := dimensionFunction_le_of_component_eq δ hgen z
    omega
  intro w hzw
  by_contra hwz
  have hlt := δ.strictMono (lt_of_le_not_ge hzw hwz)
  have hle := dimensionFunction_le_of_component_eq δ hgen w
  omega

/-- One degree below the components is actual specialization coheight one. -/
theorem coheight_eq_one_of_degree_eq_component_sub_one {X : Scheme.{u}}
    (δ : DimensionFunction X) {n : ℤ}
    (hgen : ∀ W : irreducibleComponents X, δ W.2.1.genericPoint = n)
    {x : X} (hx : δ x = n - 1) : coheight x = 1 := by
  refine le_antisymm (coheight_le_coe_iff.mpr fun z hxz ↦ ?_) ?_
  · rw [IsMax.coheight_eq_zero (isMax_of_degree_eq_component_sub_one δ hgen hx hxz)]
    norm_num
  · obtain ⟨W, hxW⟩ := exists_component_containing x
    have hle : x ≤ W.2.1.genericPoint := Scheme.le_iff_specializes.mpr
      ((genericPoints.isGenericPoint_ofComponent W).specializes hxW)
    have hne : x ≠ W.2.1.genericPoint := by
      intro h
      have := hgen W
      rw [← h, hx] at this
      omega
    have hlt : x < W.2.1.genericPoint := lt_iff_le_not_ge.mpr ⟨hle, fun hback ↦
      hne ((Scheme.le_iff_specializes.mp hback).antisymm
        (Scheme.le_iff_specializes.mp hle)).eq⟩
    have h := coheight_add_one_le hlt
    rwa [IsMax.coheight_eq_zero (isMax_of_degree_eq_component_sub_one δ hgen hx hlt),
      zero_add] at h

/-- The coheight calculation is the dimension of the original scheme's local ring. -/
theorem stalkDim_eq_one_of_degree_eq_component_sub_one {X : Scheme.{u}}
    (δ : DimensionFunction X) {n : ℤ}
    (hgen : ∀ W : irreducibleComponents X, δ W.2.1.genericPoint = n)
    {x : X} (hx : δ x = n - 1) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [← point_coheight_eq_stalkDim, coheight_eq_one_of_degree_eq_component_sub_one δ hgen hx]
  rfl

end

end HodgeConjecture.SchemeCycles
