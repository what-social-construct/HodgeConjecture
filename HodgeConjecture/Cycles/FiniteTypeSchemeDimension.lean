module

public import HodgeConjecture.Cycles.FiniteTypeDimension
public import HodgeConjecture.Cycles.SupportDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Finite dimension for actual finite-type schemes over a field

The algebraic finite bound on an affine chart extends to a quasi-compact
scheme through an actual finite affine subcover. Open immersions preserve
point coheight because their actual local-ring maps are isomorphisms.
The global dimension is therefore bounded by the maximum of the finite
chart dimensions.

The structural morphism supplies finite generation on each affine chart;
no separate algebra structure or dimension bound on its global sections
is an input. A locally finite-type, quasi-compact morphism to the spectrum
of a field thus has finite-dimensional source, including an empty source.
This is a finiteness theorem, not a higher-dimensional cover-step theorem
or an identification with transcendence degree.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The actual stalk isomorphism of an open immersion preserves point coheight. -/
theorem point_coheight_eq_of_isOpenImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (x : X) :
    Order.coheight x = Order.coheight (i.base x) := by
  apply WithBot.coe_injective
  rw [point_coheight_eq_stalkDim, point_coheight_eq_stalkDim]
  exact (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim.symm

/-- A finite open cover by finite-dimensional schemes gives a finite
global dimension, without an integrality or Noetherian hypothesis. -/
theorem topologicalKrullDim_lt_top_of_finite_openCover {X : Scheme.{u}}
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (h𝒰 : ∀ i, topologicalKrullDim (𝒰.X i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  letI := Fintype.ofFinite 𝒰.I₀
  let b : WithBot ℕ∞ := Finset.univ.sup (fun i ↦ topologicalKrullDim (𝒰.X i))
  have hb : b < ⊤ := (Finset.sup_lt_iff bot_lt_top).mpr (fun i _ ↦ h𝒰 i)
  refine lt_of_le_of_lt ?_ hb
  rw [topologicalKrullDim_eq_pointKrullDim, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  rw [← point_coheight_eq_of_isOpenImmersion (𝒰.f i) y]
  have hy : (Order.coheight y : WithBot ℕ∞) ≤ topologicalKrullDim (𝒰.X i) := by
    rw [topologicalKrullDim_eq_pointKrullDim]
    exact Order.coheight_le_krullDim y
  exact hy.trans (Finset.le_sup (f := fun i ↦ topologicalKrullDim (𝒰.X i))
    (Finset.mem_univ i))

/-- A structural finite-type morphism supplies the actual algebra on
the global sections of an affine source and hence its finite dimension. -/
theorem affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    topologicalKrullDim X < ⊤ := by
  let q : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of k) := X.isoSpec.inv ≫ p
  haveI : LocallyOfFiniteType q := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective q
  change Spec.map φ = q at hφ
  have h : RingHom.FiniteType φ.hom := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  algebraize [φ.hom]
  exact affine_topologicalKrullDim_lt_top_of_finiteType k X

/-- Finite dimension of an actual quasi-compact scheme locally of finite
type over a field, proved using its finite affine subcover. -/
theorem topologicalKrullDim_lt_top_of_compact_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u}) [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    topologicalKrullDim X < ⊤ := by
  let 𝒰 := X.affineCover.finiteSubcover
  apply topologicalKrullDim_lt_top_of_finite_openCover 𝒰
  intro i
  exact affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType k (𝒰.X i) (𝒰.f i ≫ p)

/-- Finite type means locally finite type and quasi-compact. The latter
supplies the required compactness of the source over the affine field base. -/
theorem topologicalKrullDim_lt_top_of_finiteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    topologicalKrullDim X < ⊤ := by
  letI := QuasiCompact.compactSpace_of_compactSpace p
  exact topologicalKrullDim_lt_top_of_compact_locallyOfFiniteType k X p

end

end HodgeConjecture.SchemeCycles
