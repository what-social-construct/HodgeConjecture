import HodgeConjecture.Cycles.FunctionFieldMap

/-! # Generic-stalk maps on affine coordinates -/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- A nonempty open subscheme of an irreducible scheme is dominant. -/
instance openImmersion_isDominant_of_nonempty
    {X Y : Scheme.{u}} [Nonempty X] [IrreducibleSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- The actual generic-stalk map of an affine morphism extends its ring map. -/
theorem functionFieldMapOfDominant_spec_algebraMap
    {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (f : R ⟶ S) [IsDominant (Spec.map f)] (r : R) :
    functionFieldMapOfDominant (Spec.map f)
        (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (f r) := by
  have h : StructureSheaf.toStalk R (genericPoint (Spec R)) ≫
      functionFieldMapOfDominant (Spec.map f) =
      f ≫ StructureSheaf.toStalk S (genericPoint (Spec S)) := by
    unfold functionFieldMapOfDominant
    rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
    erw [StructureSheaf.toStalk_stalkSpecializes]
    exact stalkMap_toStalk f _
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r

/-- The actual affine chart map carries generic germs to the standard fractions. -/
theorem functionFieldMapOfDominant_fromSpec_germ
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (b : Γ(X, U)) :
    functionFieldMapOfDominant hU.fromSpec (X.germToFunctionField U b) =
      algebraMap Γ(X, U) (Spec Γ(X, U)).functionField b := by
  have h := functionFieldMapOfDominant_germ hU.fromSpec U
  rw [hU.fromSpec_app_self, Category.assoc] at h
  simp only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res] at h
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) b

/-- Injectivity of the affine ring map supplies dominance of its spectrum map. -/
theorem specMap_isDominant_of_injective
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : Function.Injective f) :
    IsDominant (Spec.map f) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.hom).mpr
  intro r hr
  have hr0 : r = 0 := hf (by simpa using hr)
  simp [hr0]

end

end HodgeConjecture.SchemeCycles
