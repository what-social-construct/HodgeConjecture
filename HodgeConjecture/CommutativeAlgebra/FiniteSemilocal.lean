import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Finite algebras over a local ring

A finite algebra over a local ring has finitely many maximal ideals. Each
contracts to the base maximal ideal and has finite residue degree. The proof
uses the finite algebra over the residue field obtained by quotienting by
the extended maximal ideal; this algebra is Artinian and thus has finitely
many maximal ideals (Stacks Tag 00J7,
https://stacks.math.columbia.edu/tag/00J7).

For integral extensions of domains, dimension at most one also ascends.
These are derived hypotheses for the norm--order formula of Stacks 02MJ:
https://stacks.math.columbia.edu/tag/02MJ
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

/-- A maximal ideal of a finite algebra over a local ring contracts to its maximal ideal. -/
theorem finiteAlgebra_maximal_liesOver [IsLocalRing R] [Module.Finite R B]
    (q : MaximalSpectrum B) : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := by
  constructor
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q.asIdeal)).symm

attribute [local instance] finiteAlgebra_maximal_liesOver

/-- Residue degrees in a finite algebra over a local ring are finite. -/
theorem finiteAlgebra_residue_finite [IsLocalRing R] [Module.Finite R B]
    (q : MaximalSpectrum B) :
    Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q.asIdeal) := by
  exact Module.Finite.of_restrictScalars_finite R _ _

/-- A finite algebra over a local ring is semilocal, with no Noetherian assumption. -/
theorem finiteAlgebra_maximalSpectrum_finite [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  let m := IsLocalRing.maximalIdeal R
  let I := m.map (algebraMap R B)
  let C := B ⧸ I
  letI : Algebra (R ⧸ m) C := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  letI : IsScalarTower R (R ⧸ m) C :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (R ⧸ m) C := Module.Finite.of_restrictScalars_finite R _ _
  letI := Ideal.Quotient.field m
  letI : IsArtinianRing C := IsArtinianRing.of_finite (R ⧸ m) C
  have hle (q : MaximalSpectrum B) : I ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.over_def q.asIdeal m).le
  let f : MaximalSpectrum B → MaximalSpectrum C := fun q =>
    ⟨q.asIdeal.map (Ideal.Quotient.mk I),
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
        simpa only [Ideal.mk_ker] using hle q)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply MaximalSpectrum.ext
  have h := congrArg (fun t : MaximalSpectrum C => t.asIdeal.comap (Ideal.Quotient.mk I)) hpq
  simpa only [f, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_of_le_left (hle p), sup_of_le_left (hle q)] using h

/-- For integral extensions of domains, dimension at most one ascends. -/
theorem integralAlgebra_krullDimLE_one [IsDomain R] [IsDomain B]
    [Algebra.IsIntegral R B] [Ring.KrullDimLE 1 R] : Ring.KrullDimLE 1 B := by
  apply Ring.KrullDimLE.mk₁'
  intro q hq hprime
  letI := hprime
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
  exact (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹Ring.KrullDimLE 1 R›)
    (q.comap (algebraMap R B))
    (fun h => hq (Ideal.eq_bot_of_comap_eq_bot h)) inferInstance

end

end HodgeConjecture.CommutativeAlgebra
