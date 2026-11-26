module

public import HodgeConjecture.LinearAlgebra.Harmonic.Equivalence
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Harmonic certificates for closed finite cochains

The copied cellular Hodge operators come from `homotopical-encrypt` at the
revision cited in `Hodge.lean`. This extension packages their class-verification
consequence: closed representatives have the same native quotient class exactly
when their harmonic projections agree. Only the harmonic representative is
unique; no uniqueness of an exact primitive is asserted.

These are finite real cochains. A comparison with a scheme's Betti cohomology
and its rational/Hodge structures is separate geometric data.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.Harmonic.CellularSheaf

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face} (F : CellularSheaf X)

theorem harmonicOneProjection_isHarmonic (c : F.C1) :
    F.IsHarmonicOneCochain (F.harmonicOneProjection c) :=
  F.harmonicOneSubspace.starProjection_apply_mem c

theorem harmonicOneProjection_of_harmonic {h : F.C1}
    (hh : F.IsHarmonicOneCochain h) : F.harmonicOneProjection h = h :=
  F.harmonicOneSubspace.starProjection_eq_self_iff.mpr hh

theorem harmonicOneProjection_delta0 (a : F.C0) :
    F.harmonicOneProjection (F.delta0 a) = 0 := by
  apply F.harmonicOneSubspace.starProjection_apply_eq_zero_iff.mpr
  intro h hh
  rw [real_inner_comm]
  exact F.inner_delta0_harmonic_eq_zero a (LinearMap.mem_ker.mp hh)

theorem harmonicOneProjection_of_exact {c : F.C1}
    (hc : F.IsExactOneCochain c) : F.harmonicOneProjection c = 0 := by
  obtain ⟨a, rfl⟩ := hc
  exact F.harmonicOneProjection_delta0 a

/-- Closedness removes the coexact component; the residual is genuinely exact. -/
theorem sub_harmonicOneProjection_exact {c : F.C1}
    (hc : F.IsOneCocycle c) :
    F.IsExactOneCochain (c - F.harmonicOneProjection c) := by
  let e := F.exactOneSubspace.starProjection c
  have he : e ∈ F.exactOneSubspace :=
    F.exactOneSubspace.starProjection_apply_mem c
  obtain ⟨a, ha⟩ := he
  have heClosed : F.delta1 e = 0 :=
    F.isOneCocycle_of_isExactOneCochain ⟨a, ha⟩
  have horth : c - e ∈ LinearMap.ker F.delta0.adjoint := by
    rw [← LinearMap.orthogonal_range]
    exact F.exactOneSubspace.sub_starProjection_mem_orthogonal c
  have hh : F.IsHarmonicOneCochain (c - e) := by
    apply (F.degreeOneLaplacian_apply_eq_zero_iff _).mpr
    exact ⟨LinearMap.mem_ker.mp horth, by rw [map_sub, hc, heClosed, sub_self]⟩
  have hPe : F.harmonicOneProjection e = 0 :=
    F.harmonicOneProjection_of_exact ⟨a, ha⟩
  have hp : F.harmonicOneProjection c = c - e := by
    simpa only [map_sub, hPe, sub_zero] using F.harmonicOneProjection_of_harmonic hh
  change c - F.harmonicOneProjection c ∈ F.exactOneSubspace
  rw [hp, sub_sub_cancel]
  exact ⟨a, ha⟩

/-- The representative is unique; its primitive is deliberately existential. -/
theorem existsUnique_harmonic_representative {c : F.C1}
    (hc : F.IsOneCocycle c) :
    ∃! h : F.C1, F.IsHarmonicOneCochain h ∧ F.IsExactOneCochain (c - h) := by
  refine ⟨F.harmonicOneProjection c,
    ⟨F.harmonicOneProjection_isHarmonic c, F.sub_harmonicOneProjection_exact hc⟩, ?_⟩
  intro h hh
  have hz := F.harmonicOneProjection_of_exact hh.2
  rw [map_sub, F.harmonicOneProjection_of_harmonic hh.1] at hz
  exact (sub_eq_zero.mp hz).symm

/-- A complete class-equality criterion on closed representatives. -/
theorem harmonicOneProjection_eq_iff_exact_sub {c c' : F.C1}
    (hc : F.IsOneCocycle c) (hc' : F.IsOneCocycle c') :
    F.harmonicOneProjection c = F.harmonicOneProjection c' ↔
      F.IsExactOneCochain (c - c') := by
  constructor
  · intro h
    have hsub := F.exactOneSubspace.sub_mem
      (F.sub_harmonicOneProjection_exact hc) (F.sub_harmonicOneProjection_exact hc')
    have heq : (c - F.harmonicOneProjection c) -
        (c' - F.harmonicOneProjection c') = c - c' := by
      rw [h]
      abel
    rwa [heq] at hsub
  · intro h
    have hz := F.harmonicOneProjection_of_exact h
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- Exact cochains inside the existing closed-cochain submodule. -/
def exactClosedOneSubspace : Submodule ℝ (LinearMap.ker F.delta1) :=
  F.exactOneSubspace.comap (LinearMap.ker F.delta1).subtype

/-- The criterion uses the native kernel/range quotient, not a replacement relation. -/
theorem quotient_class_eq_iff_harmonicOneProjection_eq
    (c c' : LinearMap.ker F.delta1) :
    (Submodule.Quotient.mk c : (LinearMap.ker F.delta1) ⧸ F.exactClosedOneSubspace) =
      Submodule.Quotient.mk c' ↔
    F.harmonicOneProjection c = F.harmonicOneProjection c' := by
  rw [Submodule.Quotient.eq]
  exact (F.harmonicOneProjection_eq_iff_exact_sub c.property c'.property).symm

/-- Faithful harmonic realizations turn an exact-difference certificate into equality. -/
theorem eq_of_exact_harmonicWitness_sub
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (W : V →ₗ[ℚ] F.harmonicOneSubspace) (faithful : Function.Injective W)
    {x y : V}
    (certificate : F.IsExactOneCochain ((W x : F.C1) - (W y : F.C1))) : x = y := by
  apply faithful
  apply Subtype.ext
  have hx := (F.isHarmonicOneCochain_iff_coclosed_and_cocycle _).mp (W x).property
  have hy := (F.isHarmonicOneCochain_iff_coclosed_and_cocycle _).mp (W y).property
  have h := (F.harmonicOneProjection_eq_iff_exact_sub hx.2 hy.2).mpr certificate
  rwa [F.harmonicOneProjection_of_harmonic (W x).property,
    F.harmonicOneProjection_of_harmonic (W y).property] at h

end HodgeConjecture.Harmonic.CellularSheaf

end
