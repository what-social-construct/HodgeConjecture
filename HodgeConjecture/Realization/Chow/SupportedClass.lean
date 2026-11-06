module

public import HodgeConjecture.Realization.HodgeClasses
public import HodgeConjecture.Cycles.OpenClosedLocalization
public import HodgeConjecture.Cycles.RationalChow
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

/-!+# Extracting an actual cycle from a supported cohomology class

For a closed immersion `i : Z ⟶ X`, expand a supplied supported class in a
basis indexed by actual integral supports on `Z`. Mathlib's `Basis.constr`
forms the finite rational combination of their fundamental cycles. Push
this cycle into `X` using the existing graded closed pushforward and take
its existing rational Chow class. A comparison on basis vectors computes
the class of this explicit cycle.

Cohomological localization (`range forgetSupport = ker restrictH`), the
basis, and its fundamental-class comparison are explicit inputs. Actual
cycle support and open vanishing are proved using the scheme maps. No
general Betti theory, purity theorem, or support-existence assertion is
introduced here, and no new cycle carrier or realization record is needed.

Classically, for smooth projective complex `X` of dimension `d` and a
closed algebraic `Z` of codimension at least `p`, supported cohomology in
degree `2p` has the fundamental classes of the `(d-p)`-dimensional
components as a basis. Localization then turns vanishing off `Z` into a
cycle representing the class. See Voisin, *Hodge and generalized Hodge
conjectures, coniveau and algebraic cycles*, sections 4.1--4.2, especially
Definition 4.1 and the explanation following Conjecture 4.6:
https://webusers.imj-prg.fr/~claire.voisin/Articlesweb/JOMP_V01N01P02Paper.pdf
The geometric source statements remain unformalized. In this file `n` is
the existing dimension degree (classically `d-p`), not cohomological degree.
In particular, a divisor does not automatically provide the basis for `p>1`.
-/

set_option autoImplicit false

namespace HodgeConjecture.SupportedClass

open AlgebraicGeometry CategoryTheory SchemeCycles Module

noncomputable section

universe u v w t

variable {X Z U : Scheme.{u}} [IsNoetherian X]
variable (δ : DimensionFunction X) (n : ℤ)
variable (i : Z ⟶ X) [IsClosedImmersion i]
variable {ι : Type v} {HZ : Type w} {HX HU : Type t}
variable [AddCommGroup HZ] [Module ℚ HZ]
variable [AddCommGroup HX] [Module ℚ HX] [AddCommGroup HU] [Module ℚ HU]
variable (W : ι → IntegralClosedSubscheme Z)
variable (hW : ∀ k, supportDegree (δ.comapClosedImmersion i) (W k) = n)
variable (b : Basis ι ℚ HZ)

/-- Compute the class of the component expansion. The basis comparison
identifies each geometric fundamental cycle, not just an abstract span. -/
theorem cycleClass_componentExpansion
    (cl : RationalChowGroup δ n →ₗ[ℚ] HX) (forgetSupport : HZ →ₗ[ℚ] HX)
    (hBasis : ∀ k, cl (rationalClassMap δ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
        ⟨fundamentalCycle ℚ (W k),
          fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩)) =
        forgetSupport (b k))
    (γ : HZ) :
    cl (rationalClassMap δ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
        (b.constr ℚ (fun k ↦
          (⟨fundamentalCycle ℚ (W k),
            fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩ :
              cyclesOfDegree ℚ (δ.comapClosedImmersion i) n)) γ))) =
      forgetSupport γ := by
  let C : ι → cyclesOfDegree ℚ (δ.comapClosedImmersion i) n := fun k ↦
    ⟨fundamentalCycle ℚ (W k),
      fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩
  let push := gradedClosedImmersionPushforwardWithCoefficients ℚ
    (δ.comapClosedImmersion i) δ i
    (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
  have h : ((cl.comp (rationalClassMap δ n)).comp push).comp (b.constr ℚ C) =
      forgetSupport := by
    apply b.ext
    intro k
    simpa only [LinearMap.comp_apply, Basis.constr_basis] using hBasis k
  exact LinearMap.congr_fun h γ

/-- A class vanishing on the actual complementary open gives a finite
homogeneous cycle on the closed scheme. Its pushforward represents the
class and restricts to zero already as a cycle. Only the cohomological
localization and component-basis comparisons are supplied. -/
theorem exists_supported_cycle_of_vanishing
    (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ)
    (cl : RationalChowGroup δ n →ₗ[ℚ] HX)
    (forgetSupport : HZ →ₗ[ℚ] HX) (restrictH : HX →ₗ[ℚ] HU)
    (hExact : LinearMap.range forgetSupport = LinearMap.ker restrictH)
    (hBasis : ∀ k, cl (rationalClassMap δ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
        ⟨fundamentalCycle ℚ (W k),
          fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩)) =
        forgetSupport (b k))
    (α : HX) (hα : restrictH α = 0) :
    ∃ c : cyclesOfDegree ℚ (δ.comapClosedImmersion i) n,
      let z := gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n c
      cl (rationalClassMap δ n z) = α ∧ gradedOpenRestriction ℚ δ j n z = 0 := by
  have hmem : α ∈ LinearMap.range forgetSupport := by
    rw [hExact]
    exact hα
  obtain ⟨γ, hγ⟩ := hmem
  let c := b.constr ℚ (fun k ↦
    (⟨fundamentalCycle ℚ (W k),
      fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩ :
        cyclesOfDegree ℚ (δ.comapClosedImmersion i) n)) γ
  refine ⟨c, (cycleClass_componentExpansion δ n i W hW b cl forgetSupport hBasis γ).trans hγ, ?_⟩
  have hc : gradedClosedImmersionPushforwardWithCoefficients ℚ
      (δ.comapClosedImmersion i) δ i
      (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n c ∈
      LinearMap.range (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n) := ⟨c, rfl⟩
  rw [range_gradedClosedPushforward_eq_ker_gradedOpenRestriction ℚ δ i j hcomp n] at hc
  exact hc

/-- With the cycle-class/restriction square, vanishing is equivalent to
representation by an actual cycle on the closed support. The open map is
stated on homogeneous cycles, so no extra Chow group or Noetherian-source
hypothesis is required. This is a conditional criterion, not a construction
of supports for arbitrary Hodge classes. -/
theorem vanishing_iff_supported_cycle
    (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ)
    (cl : RationalChowGroup δ n →ₗ[ℚ] HX)
    (forgetSupport : HZ →ₗ[ℚ] HX) (restrictH : HX →ₗ[ℚ] HU)
    (hExact : LinearMap.range forgetSupport = LinearMap.ker restrictH)
    (hBasis : ∀ k, cl (rationalClassMap δ n
      (gradedClosedImmersionPushforwardWithCoefficients ℚ
        (δ.comapClosedImmersion i) δ i
        (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
        ⟨fundamentalCycle ℚ (W k),
          fundamentalCycle_mem_cyclesOfDegree ℚ _ n (W k) (hW k)⟩)) =
        forgetSupport (b k))
    (clOpen : cyclesOfDegree ℚ (δ.comapOpenImmersion j) n →ₗ[ℚ] HU)
    (hRestrict : clOpen.comp (gradedOpenRestriction ℚ δ j n) =
      restrictH.comp (cl.comp (rationalClassMap δ n))) (α : HX) :
    restrictH α = 0 ↔
      ∃ c : cyclesOfDegree ℚ (δ.comapClosedImmersion i) n,
        cl (rationalClassMap δ n
          (gradedClosedImmersionPushforwardWithCoefficients ℚ
            (δ.comapClosedImmersion i) δ i
            (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n c)) = α := by
  constructor
  · intro hα
    obtain ⟨c, hc, _⟩ := exists_supported_cycle_of_vanishing
      δ n i W hW b j hcomp cl forgetSupport restrictH hExact hBasis α hα
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    let push := gradedClosedImmersionPushforwardWithCoefficients ℚ
      (δ.comapClosedImmersion i) δ i
      (fun V ↦ (supportDegree_comapClosedImmersion δ i V).symm) n
    have hz : gradedOpenRestriction ℚ δ j n (push c) = 0 := by
      have hc : push c ∈ LinearMap.range push := ⟨c, rfl⟩
      rw [range_gradedClosedPushforward_eq_ker_gradedOpenRestriction ℚ δ i j hcomp n] at hc
      exact hc
    have h := LinearMap.congr_fun hRestrict (push c)
    simp only [LinearMap.comp_apply, hz, map_zero] at h
    exact h.symm

end

end HodgeConjecture.SupportedClass
