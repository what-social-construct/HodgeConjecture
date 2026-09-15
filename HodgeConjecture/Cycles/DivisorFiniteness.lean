import HodgeConjecture.Cycles.DivisorSupport
import HodgeConjecture.Cycles.HeightOneFiniteness
import HodgeConjecture.Cycles.RationalFunctionPresentation
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Local finiteness of actual prime-divisor supports

On an affine chart, write a nonzero rational function as a fraction of
nonzero sections. A nonzero local coefficient must lie over a height-one
prime containing the numerator or denominator. There are only finitely
many such primes in a Noetherian domain.

An integral closed support meets an open set exactly when its ambient
generic point belongs to that open set. Thus the affine result gives local
finiteness of the actual closed supports, not merely point-finiteness.
Quasi-compactness then gives finite coefficient support. No normality,
absolute-dimension grading, principal-divisor cycle, or relation is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Topology

noncomputable section

universe u

/-- A rational function has only finitely many nonzero divisor coefficients
whose generic points lie in a given affine chart. -/
theorem finite_divisorPoints_in_affine (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] {U : X.Opens}
    (hU : IsAffineOpen U) (f : X.functionFieldˣ) :
    Set.Finite {x : DivisorPoint X | x.val ∈ U ∧ divisorOrder X x f ≠ 0} := by
  classical
  by_cases hne : Nonempty U
  · letI := hne
    letI : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨a, b, ha, hb, hf⟩ := exists_affine_fraction X hU f
    let T : Set (PrimeSpectrum Γ(X, U)) :=
      {p | p.asIdeal.height = 1 ∧ (a ∈ p.asIdeal ∨ b ∈ p.asIdeal)}
    have hT : T.Finite := finite_heightOne_primes_containing_either Γ(X, U) a b ha hb
    let S : Set (DivisorPoint X) :=
      {x | x.val ∈ U ∧ divisorOrder X x f ≠ 0}
    let q : S → T := fun x ↦ ⟨hU.primeIdealOf ⟨x.val.val, x.property.1⟩, by
      constructor
      · let y : U := ⟨x.val.val, x.property.1⟩
        letI := X.presheaf.algebra_section_stalk y
        letI := hU.isLocalization_stalk y
        have hd := x.val.property
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height
          (hU.primeIdealOf y).asIdeal] at hd
        exact WithBot.coe_injective hd
      · by_contra hn
        push_neg at hn
        exact x.property.2 (divisorOrder_eq_zero_of_affine_fraction
          X hU x.val x.property.1 f a b hf hn.1 hn.2)⟩
    have hq : Function.Injective q := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      have hp := congrArg (fun p : T ↦ hU.fromSpec.base p.val) h
      simpa only [q, IsAffineOpen.fromSpec_primeIdealOf] using hp
    letI : Finite T := hT.to_subtype
    letI : Finite S := Finite.of_injective q hq
    exact Set.toFinite S
  · have he : {x : DivisorPoint X | x.val ∈ U ∧ divisorOrder X x f ≠ 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hne ⟨⟨x.val, hx.1⟩⟩
    rw [he]
    exact Set.finite_empty

/-- The nonzero coefficients index a locally finite family of actual
integral closed supports. Quasi-compactness is not needed here. -/
theorem primeDivisorSupports_locallyFinite (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionFieldˣ) :
    LocallyFinite (fun Z : {Z : PrimeDivisor X // primeDivisorOrder X Z f ≠ 0} ↦
      (Z.val.val.val.support : Set X)) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
  refine ⟨U, U.isOpen.mem_nhds hxU, ?_⟩
  refine Set.Finite.of_injOn
    (f := fun Z : {Z : PrimeDivisor X // primeDivisorOrder X Z f ≠ 0} ↦
      (divisorPointEquivPrimeDivisor X).symm Z.val) ?_ ?_
    (finite_divisorPoints_in_affine X hU f)
  · intro Z hZ
    exact ⟨((ambientGenericPoint_isGenericPoint Z.val.val).mem_open_set_iff
      U.isOpen).mpr hZ, Z.property⟩
  · intro Z _ W _ h
    exact Subtype.ext ((divisorPointEquivPrimeDivisor X).symm.injective h)

/-- On a quasi-compact integral locally Noetherian scheme, only finitely
many actual prime divisors have nonzero coefficient. -/
theorem finite_primeDivisorOrder_support (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    Set.Finite {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} := by
  have h := (primeDivisorSupports_locallyFinite X f).finite_of_compact
    (fun Z ↦ ⟨ambientGenericPoint Z.val.val,
      (ambientGenericPoint_isGenericPoint Z.val.val).mem⟩)
  exact (h.image Subtype.val).subset (fun Z hZ ↦ ⟨⟨Z, hZ⟩, Set.mem_univ _, rfl⟩)

/-- The equivalent original point-indexed coefficient function also has
finite support under quasi-compactness. -/
theorem finite_divisorOrder_support (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    Set.Finite {x : DivisorPoint X | divisorOrder X x f ≠ 0} := by
  have h := (finite_primeDivisorOrder_support X f).preimage
    (divisorPointEquivPrimeDivisor X).injective.injOn
  apply h.subset
  intro x hx
  change primeDivisorOrder X (divisorPointEquivPrimeDivisor X x) f ≠ 0
  simpa only [primeDivisorOrder_pointSupport] using hx

end

end HodgeConjecture.SchemeCycles
