module

public import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality

/-!
# Open covers pulled back from a product's second factor

The original subtype of `X × Y` where the second coordinate lies in an open
set `W` is homeomorphic to `X × W`. For a two-open cover of `Y`, these
subtypes form an actual two-open cover of `X × Y`; its overlap has the
corresponding product topology. The H⁰ difference is surjective when both
factors of the overlap are path connected.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProductSecondFactorCover

open CategoryTheory

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The open subset of `X × Y` determined by the second coordinate. -/
def chart (W : Set Y) : Set (X × Y) := Prod.snd ⁻¹' W

/-- The original subtype chart is the topological product with `W`. -/
def chartHomeomorph (W : Set Y) : ↥(chart (X := X) W) ≃ₜ X × W where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p with | mk x y => cases y; rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem isOpen_chart (W : Set Y) (hW : IsOpen W) : IsOpen (chart (X := X) W) :=
  hW.preimage continuous_snd

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem chart_inter (U V : Set Y) :
    chart (X := X) U ∩ chart V = chart (U ∩ V) := by
  ext p
  simp [chart]

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem chart_cover (U V : Set Y) (hcover : U ∪ V = Set.univ) :
    chart (X := X) U ∪ chart V = Set.univ := by
  ext p
  have hp : p.2 ∈ U ∪ V := by rw [hcover]; trivial
  simpa only [chart, Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true] using hp

theorem chart_inter_pathConnected (U V : Set Y)
    [PathConnectedSpace X] [PathConnectedSpace ↥(U ∩ V)] :
    PathConnectedSpace ↥(chart (X := X) U ∩ chart V) := by
  rw [chart_inter]
  exact (chartHomeomorph (X := X) (U ∩ V)).symm.pathConnectedSpace

/-- Connectedness of the actual product overlap makes every degree-zero
singular class a constant class. -/
theorem overlapH0_eq_constant (U V : Set Y)
    [PathConnectedSpace X] [PathConnectedSpace ↥(U ∩ V)]
    (x : X) (p : ↥(U ∩ V))
    (z : SingularCochains.Cohomology
      (TopCat.of ↥(chart (X := X) U ∩ chart V)) 0) :
    ∃ q : ℚ, z = SingularDegreeZeroNaturality.constantClass
      ↥(chart (X := X) U ∩ chart V) q := by
  letI : PathConnectedSpace ↥(chart (X := X) U ∩ chart V) :=
    chart_inter_pathConnected U V
  let p0 : ↥(chart (X := X) U ∩ chart V) :=
    ⟨(x, p.1), ⟨p.2.1, p.2.2⟩⟩
  let h := (SingularCochains.cohomologyZeroIso
    ↥(chart (X := X) U ∩ chart V)).hom z
  let q := SingularDegreeZero.equivConstants _ p0 h
  refine ⟨q, ?_⟩
  apply (SingularCochains.cohomologyZeroIso _).toLinearEquiv.injective
  have hh : h = SingularDegreeZero.constantClass _ q := by
    calc
      h = (SingularDegreeZero.equivConstants _ p0).symm q := by
        exact ((SingularDegreeZero.equivConstants _ p0).symm_apply_apply h).symm
      _ = SingularDegreeZero.constantClass _ q :=
        SingularDegreeZero.equivConstants_symm_apply _ p0 q
  change (SingularCochains.cohomologyZeroIso _).hom z =
    (SingularCochains.cohomologyZeroIso _).hom
      ((SingularCochains.cohomologyZeroIso _).inv
        (SingularDegreeZero.constantClass _ q))
  rw [Iso.inv_hom_id_apply]
  exact hh

/-- For the second-factor product cover, the original degree-zero
Mayer–Vietoris difference is surjective. -/
theorem difference_zero_surjective (U V : Set Y)
    [PathConnectedSpace X] [PathConnectedSpace ↥(U ∩ V)]
    (x : X) (p : ↥(U ∩ V)) :
    Function.Surjective
      (SingularMayerVietoris.difference
        (TopCat.of (X × Y)) (chart U) (chart V) 0) := by
  intro z
  obtain ⟨q, rfl⟩ := overlapH0_eq_constant U V x p z
  refine ⟨(SingularDegreeZeroNaturality.constantClass ↥(chart U) q, 0), ?_⟩
  rw [SingularMayerVietoris.difference_apply]
  simp only [map_zero, sub_zero]
  let inc : C(↥(chart (X := X) U ∩ chart V), ↥(chart U)) :=
    ⟨fun w ↦ ⟨w.val, w.property.1⟩,
      continuous_subtype_val.subtype_mk (fun w ↦ w.property.1)⟩
  change SingularCochains.cohomologyPullback (TopCat.ofHom inc) 0
      (SingularDegreeZeroNaturality.constantClass ↥(chart U) q) =
    SingularDegreeZeroNaturality.constantClass
      ↥(chart (X := X) U ∩ chart V) q
  exact SingularDegreeZeroNaturality.pullback_constantClass inc q

end HodgeConjecture.ProductSecondFactorCover

end
