module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-!
# Length under a local homomorphism

For a local homomorphism `A → B` with finite residue-field extension, the
length over `A` of a finite-length `B`-module is its length over `B` times
the residue degree. This is the local case of Stacks Project, Tag 02M0:
https://stacks.math.columbia.edu/tag/02M0

The proof uses a composition series and the actual residue-field scalar
actions. No Noetherian, domain, normality or freeness hypothesis is needed.
This does not yet give the semilocal sum over localizations in Tag 02M0.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B]
  [Algebra A B] [IsLocalRing B]

private theorem length_simple_restrictScalars
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [IsSimpleModule B M] :
    Module.length A M = Module.length A (IsLocalRing.ResidueField B) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule B M)
  have h := IsLocalRing.eq_maximalIdeal hI
  subst I
  exact (e.restrictScalars A).length_eq

/-- Every simple factor over the local ring `B` contributes the length
over `A` of its residue field. The base ring need not be local. -/
theorem length_restrictScalars_of_isLocalRing
    (M : Type w) [AddCommGroup M] [Module B M]
    (hM : IsFiniteLength B M) : ∀ [Module A M] [IsScalarTower A B M],
    Module.length A M = Module.length B M * Module.length A (IsLocalRing.ResidueField B) := by
  induction hM with
  | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars A)
      (N.mkQ.restrictScalars A) N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)]
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)]
    rw [ih, length_simple_restrictScalars A B (M ⧸ N),
      Module.length_eq_one B (M ⧸ N), add_mul, one_mul]

variable [IsLocalRing A] [IsLocalHom (algebraMap A B)]
  [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

/-- The residue field of `B` has length over `A` equal to the degree of the
induced residue-field extension (the residue-field case of Stacks 00IY). -/
theorem length_residueField :
    Module.length A (IsLocalRing.ResidueField B) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  let b := Module.finBasis (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  rw [(b.equivFun.restrictScalars A).length_eq, Module.length_pi]
  have : IsSimpleModule A (IsLocalRing.ResidueField A) := by
    change IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A)
    exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal A).1
  simp

/-- Restriction of scalars multiplies finite length by the actual residue
degree. This is the local-ring specialization of Stacks 02M0. -/
theorem length_restrictScalars_of_localHom
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) :
    Module.length A M =
      (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℕ∞) *
        Module.length B M := by
  rw [length_restrictScalars_of_isLocalRing A B M hM, length_residueField A B, mul_comm]

/-- A finite-length module remains finite length over the base when the
local homomorphism has finite residue degree. -/
theorem isFiniteLength_restrictScalars_of_localHom
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) : IsFiniteLength A M := by
  apply Module.length_ne_top_iff.mp
  rw [length_restrictScalars_of_localHom A B M hM,
    ← ENat.coe_toNat (Module.length_ne_top_iff.mpr hM), ← Nat.cast_mul]
  exact ENat.coe_ne_top _

end

end HodgeConjecture.CommutativeAlgebra
