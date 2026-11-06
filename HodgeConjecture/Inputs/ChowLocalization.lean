module

public import HodgeConjecture.Boundary.ProjectorClosureDefect
public import HodgeConjecture.Cycles.ChowLocalization

@[expose] public section

/-!
# The selected rational-linear conclusion of Chow localization

Stacks Project, Tag 02RX, supplies the geometric Chow localization sequence
under its stated hypotheses. This interface records only the rational-linear
exactness and surjectivity needed by the consumers below. A geometric
application must supply this named package for its actual maps; there is no
automatic instance identifying arbitrary modules with Chow groups.
`ChowLocalization.ofOpenComplement` now proves the package for the actual
rational Chow maps of a Noetherian scheme and its constructed reduced
closed complement. It is a named theorem, not a global source instance.

Localization supplies raw class lifts and places the difference of two lifts
in the boundary image. For projector closures, the multiplicative restriction
is separately supplied as an algebra homomorphism. Its existing restriction-
of-defect theorem then puts every raw closure defect in that boundary image.
Neither localization nor this membership statement makes the defect vanish.
-/

set_option autoImplicit false

namespace HodgeConjecture

universe u v w t

/-- The selected rational-linear localization conclusion for boundary
pushforward `i` and open restriction `r`. Every consumer requests this
package explicitly for the two maps it uses. -/
class ChowLocalizationHypotheses
    {B : Type u} {C : Type v} {U : Type w}
    [AddCommGroup B] [Module ℚ B]
    [AddCommGroup C] [Module ℚ C]
    [AddCommGroup U] [Module ℚ U]
    (i : B →ₗ[ℚ] C) (r : C →ₗ[ℚ] U) : Prop where
  range_eq_ker : LinearMap.range i = LinearMap.ker r
  restriction_surjective : Function.Surjective r

namespace ChowLocalization

open AlgebraicGeometry CategoryTheory SchemeCycles in
/-- Instantiate the existing localization consumers on the actual rational
Chow sequence. All exactness and finiteness inputs are proved. -/
theorem ofOpenComplement {X U : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    letI := openImmersion_isNoetherian j
    ChowLocalizationHypotheses
      (rationalChowClosedImmersionPushforward
        (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
        (openComplementIdeal j).subschemeι
        (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n)
      (rationalChowOpenRestriction δ j n) := by
  letI := openImmersion_isNoetherian j
  exact {
    range_eq_ker := range_rationalChowOpenComplementPushforward_eq_ker δ j n
    restriction_surjective := rationalChowOpenRestriction_surjective δ j n }

section Linear

variable {B : Type u} {C : Type v} {U : Type w}
variable [AddCommGroup B] [Module ℚ B]
variable [AddCommGroup C] [Module ℚ C]
variable [AddCommGroup U] [Module ℚ U]

/-- Localization supplies a raw lift of every class on the open locus. -/
theorem exists_lift (i : B →ₗ[ℚ] C) (r : C →ₗ[ℚ] U)
    [ChowLocalizationHypotheses i r] (a : U) :
    ∃ c : C, r c = a :=
  ChowLocalizationHypotheses.restriction_surjective (i := i) (r := r) a

/-- Two lifts of the same open class differ by the pushforward of a
boundary class, without requiring injectivity of boundary pushforward. -/
theorem two_lifts_differ_by_boundary (i : B →ₗ[ℚ] C) (r : C →ₗ[ℚ] U)
    [ChowLocalizationHypotheses i r]
    {a : U} {c₁ c₂ : C} (h₁ : r c₁ = a) (h₂ : r c₂ = a) :
    ∃ b : B, i b = c₁ - c₂ := by
  have hker : c₁ - c₂ ∈ LinearMap.ker r := by
    rw [LinearMap.mem_ker, map_sub, h₁, h₂, sub_self]
  rw [← ChowLocalizationHypotheses.range_eq_ker (i := i) (r := r)] at hker
  exact hker

end Linear

section Algebra

variable {B : Type u} {C : Type v} {U : Type w}
variable [AddCommGroup B] [Module ℚ B]
variable [Ring C] [Algebra ℚ C] [Ring U] [Algebra ℚ U]

/-- Canonical raw closure data: its witnesses are precisely the fiber over
the given generic idempotent. The algebra restriction and generic idempotence
are supplied separately; defining this fiber needs no localization premise. -/
def projectorClosure (r : C →ₐ[ℚ] U) (e : U) (he : IsIdempotentElem e) :
    AlgebraProjectorClosure U C e where
  genericProjector_isIdempotent := he
  restriction := r
  Closure := {c : C // r c = e}
  closureClass := Subtype.val
  closureClass_restricts := Subtype.property

@[simp]
theorem projectorClosure_restriction (r : C →ₐ[ℚ] U) (e : U)
    (he : IsIdempotentElem e) :
    (projectorClosure r e he).restriction = r := rfl

@[simp]
theorem projectorClosure_closureClass (r : C →ₐ[ℚ] U) (e : U)
    (he : IsIdempotentElem e) (x : (projectorClosure r e he).Closure) :
    (projectorClosure r e he).closureClass x = x.val := rfl

/-- The localization package makes the canonical raw-closure fiber nonempty.
This asserts existence of a class lift, not an idempotent class lift. -/
theorem projectorClosure_nonempty (i : B →ₗ[ℚ] C) (r : C →ₐ[ℚ] U)
    [ChowLocalizationHypotheses i r.toLinearMap] (e : U) (he : IsIdempotentElem e) :
    Nonempty (projectorClosure r e he).Closure := by
  obtain ⟨c, hc⟩ := exists_lift i r.toLinearMap e
  exact ⟨⟨c, hc⟩⟩

/-- For any existing raw closure package, exactness places the convolution
defect in the boundary image. Multiplicativity is supplied by that package's
algebra restriction, not by the localization hypothesis. -/
theorem convolutionDefect_mem_range {e : U}
    (i : B →ₗ[ℚ] C) (P : AlgebraProjectorClosure.{w, v, t} U C e)
    [ChowLocalizationHypotheses i P.restriction.toLinearMap] (x : P.Closure) :
    P.convolutionDefect x ∈ LinearMap.range i := by
  rw [ChowLocalizationHypotheses.range_eq_ker (i := i) (r := P.restriction.toLinearMap)]
  change P.restriction (P.convolutionDefect x) = 0
  exact P.restriction_convolutionDefect x

/-- Boundary support is exhibited by a boundary preimage, without asserting
that this preimage or its pushforward vanishes. -/
theorem exists_boundary_of_convolutionDefect {e : U}
    (i : B →ₗ[ℚ] C) (P : AlgebraProjectorClosure.{w, v, t} U C e)
    [ChowLocalizationHypotheses i P.restriction.toLinearMap] (x : P.Closure) :
    ∃ b : B, i b = P.convolutionDefect x :=
  convolutionDefect_mem_range i P x

end Algebra

end ChowLocalization

end HodgeConjecture
