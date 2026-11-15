module

public import HodgeConjecture.Geometry.Holomorphic.Forms
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# Holomorphic forms above the actual coordinate dimension

The native alternating coefficients vanish above the complex dimension.
Consequently the already constructed holomorphic section spaces vanish
there too. The curve case has no positive terms beyond degree one.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem coefficient_eq_zero_of_finrank_lt {n : ℕ} (hn : Module.finrank ℂ E < n)
    (α : Coeff E n) : α = 0 := by
  ext v
  apply α.toAlternatingMap.map_linearDependent
  intro hv
  have h := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  exact (not_le_of_gt hn) h

theorem section_eq_zero_of_finrank_lt {U : Opens E} {n : ℕ} (hn : Module.finrank ℂ E < n)
    (η : Sections U n) : η = 0 := by
  apply ContMDiffMap.ext
  intro x
  exact coefficient_eq_zero_of_finrank_lt hn (η x)

theorem complexLine_section_eq_zero {U : Opens ℂ} {n : ℕ} (hn : 2 ≤ n)
    (η : Sections U n) : η = 0 :=
  section_eq_zero_of_finrank_lt (by simpa using Nat.lt_of_lt_of_le (by decide : 1 < 2) hn) η

end HodgeConjecture.HolomorphicForms
