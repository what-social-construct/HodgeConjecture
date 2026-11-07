module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# Abstract cycle-class models for the rational Hodge conjecture

This module isolates the cycle-class-surjectivity schema underlying the
rational Hodge conjecture.  For a fixed smooth projective complex variety `X`
and a codimension `p`, the intended interpretation of
`RationalHodgeCycleClassModel Chow H` is

* `Chow = CH^p(X)_ℚ`;
* `H = H^(2p)(X, ℚ)`;
* `hodgeClasses = H^(2p)(X, ℚ) ∩ H^(p,p)`;
* `cycleClass` is the rational cycle-class map.

Once those data have been constructed, `RationalHodgeConjectureAt M` has
exactly the usual fixed-`(X,p)` logical form: every rational Hodge class in the
modeled codimension is algebraic.  `RationalHodgeConjectureForModel M`
quantifies that statement over every codimension of one modeled variety, and
`RationalHodgeConjectureForFamily M` also quantifies over an indexing type of
modeled varieties.

For a general `X`, the concrete Chow groups, Betti cohomology, Hodge
structure, and cycle-class map remain explicit geometric data. This file
does not define the indexing type of all smooth projective complex
varieties. The repository's `Betti.Examples.SplitTateBlock` instantiates
the fixed-codimension model for finite split complex schemes in degree zero.
`DeRham.ProjectiveLineHodgeCycleClass` supplies a degree-two model from
the computed P¹ geometric filtration and its bounded period comparison.
Surjectivity is not a field of the model, so constructing its data does not
assume the conjecture.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

/--
Rational Chow classes, rational cohomology, rational Hodge classes, and the
cycle-class map in one fixed codimension.

The Hodge-class submodule is specified independently of the cycle-class map.
The only built-in compatibility is the standard inclusion saying that every
rational cycle class has Hodge type `(p,p)`.
-/
structure RationalHodgeCycleClassModel
    (Chow : Type u) (H : Type v)
    [AddCommGroup Chow] [Module ℚ Chow]
    [AddCommGroup H] [Module ℚ H] where
  /-- Rational `(p,p)` Hodge classes inside degree `2p` cohomology. -/
  hodgeClasses : Submodule ℚ H
  /-- The rational cycle-class map in the fixed codimension. -/
  cycleClass : Chow →ₗ[ℚ] H
  /-- Every rational cycle class has Hodge type `(p,p)`. -/
  cycleClass_lands : LinearMap.range cycleClass ≤ hodgeClasses

variable {Chow : Type u} {H : Type v}
variable [AddCommGroup Chow] [Module ℚ Chow]
variable [AddCommGroup H] [Module ℚ H]

/-- Membership in the independently specified rational Hodge-class subspace. -/
def IsRationalHodgeClass
    (M : RationalHodgeCycleClassModel Chow H) (α : H) : Prop :=
  α ∈ M.hodgeClasses

/-- A cohomology class is algebraic when it lies in the cycle-class image. -/
def IsAlgebraicHodgeClass
    (M : RationalHodgeCycleClassModel Chow H) (α : H) : Prop :=
  α ∈ LinearMap.range M.cycleClass

/--
The rational Hodge conjecture in one codimension: every rational Hodge class
is in the image of the rational cycle-class map.
-/
def RationalHodgeConjectureAt
    (M : RationalHodgeCycleClassModel Chow H) : Prop :=
  M.hodgeClasses ≤ LinearMap.range M.cycleClass

/-- Elementwise form of the rational Hodge conjecture in one codimension. -/
theorem rationalHodgeConjectureAt_iff
    (M : RationalHodgeCycleClassModel Chow H) :
    RationalHodgeConjectureAt M ↔
      ∀ α : H, IsRationalHodgeClass M α →
        ∃ z : Chow, M.cycleClass z = α :=
  Iff.rfl

/--
Because cycle classes are already known to be Hodge, the conjecture is
equivalent to equality of the cycle-class image and the Hodge-class subspace.
-/
theorem rationalHodgeConjectureAt_iff_range_eq
    (M : RationalHodgeCycleClassModel Chow H) :
    RationalHodgeConjectureAt M ↔
      LinearMap.range M.cycleClass = M.hodgeClasses := by
  constructor
  · intro h
    exact le_antisymm M.cycleClass_lands h
  · intro h
    change M.hodgeClasses ≤ LinearMap.range M.cycleClass
    rw [h]

/-- Every algebraic class in the model is a rational Hodge class. -/
theorem isRationalHodgeClass_of_isAlgebraicHodgeClass
    (M : RationalHodgeCycleClassModel Chow H)
    {α : H} (hα : IsAlgebraicHodgeClass M α) :
    IsRationalHodgeClass M α :=
  M.cycleClass_lands hα

section Graded

variable {ChowByCodim : ℕ → Type u}
variable {Cohomology : ℕ → Type v}
variable [∀ p, AddCommGroup (ChowByCodim p)]
variable [∀ p, Module ℚ (ChowByCodim p)]
variable [∀ n, AddCommGroup (Cohomology n)]
variable [∀ n, Module ℚ (Cohomology n)]

/--
The rational Hodge conjecture for one modeled variety in every codimension.
The model at codimension `p` uses cohomological degree `2 * p` explicitly.
This does not quantify over all smooth projective complex varieties.
-/
def RationalHodgeConjectureForModel
    (M : ∀ p,
      RationalHodgeCycleClassModel
        (ChowByCodim p) (Cohomology (2 * p))) : Prop :=
  ∀ p, RationalHodgeConjectureAt (M p)

/--
Short backwards-compatible name for the all-codimension conjecture attached
to one model.  It is not the universal quantification over all varieties.
-/
abbrev RationalHodgeConjecture
    (M : ∀ p,
      RationalHodgeCycleClassModel
        (ChowByCodim p) (Cohomology (2 * p))) : Prop :=
  RationalHodgeConjectureForModel M

end Graded

section Family

universe x

variable {Variety : Type x}
variable {ChowByVarietyCodim : Variety → ℕ → Type u}
variable {CohomologyByVarietyDegree : Variety → ℕ → Type v}
variable [∀ X p, AddCommGroup (ChowByVarietyCodim X p)]
variable [∀ X p, Module ℚ (ChowByVarietyCodim X p)]
variable [∀ X n, AddCommGroup (CohomologyByVarietyDegree X n)]
variable [∀ X n, Module ℚ (CohomologyByVarietyDegree X n)]

/--
The rational Hodge conjecture for an indexed family of modeled varieties, in
every codimension.  To recover the classical universal statement,
`Variety` must itself index all smooth projective complex varieties and the
models must be their genuine Chow/cohomology/Hodge-class data.
-/
def RationalHodgeConjectureForFamily
    (M : ∀ X p,
      RationalHodgeCycleClassModel
        (ChowByVarietyCodim X p)
        (CohomologyByVarietyDegree X (2 * p))) : Prop :=
  ∀ X p, RationalHodgeConjectureAt (M X p)

end Family

end


end HodgeConjecture
