module

public import HodgeConjecture.Boundary.ProjectorClosureDefect
public import HodgeConjecture.Correspondence.FilteredProjectorDefect

@[expose] public section

/-!
# The filtered detector of the existing closure defect

Specialize the cyclic filtered module to the original closure class. Its
injective embedding retains equality in that same compactified algebra.
The existing restriction theorem kills the whole module, not just its
distinguished generator. Nothing identifies this algebraic degree
filtration with a Hodge filtration or supplies a connection across a
geometric boundary.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.AlgebraProjectorClosure

universe u v w

variable {G : Type u} {A : Type v}
variable [Ring G] [Algebra ℚ G] [Ring A] [Algebra ℚ A] {e : G}
variable (C : AlgebraProjectorClosure G A e) (x : C.Closure)

/-- The native cyclic module of the same existing compactified closure defect. -/
abbrev DefectModule := ProjectorDefectModule.Carrier (C.closureClass x)

/-- Its canonical polynomial-degree filtration, without a new carrier. -/
abbrev defectFiltration := ProjectorDefectModule.filtration (C.closureClass x)

/-- The original compactified algebra is the target of this injective inclusion. -/
abbrev defectEmbedding := ProjectorDefectModule.embedding (C.closureClass x)

theorem defectModule_detects :
    Subsingleton (C.DefectModule x) ↔ C.convolutionDefect x = 0 :=
  ProjectorDefectModule.subsingleton_iff_defect_eq_zero (C.closureClass x)

theorem defectModule_detects_idempotence :
    Subsingleton (C.DefectModule x) ↔ IsIdempotentElem (C.closureClass x) :=
  ProjectorDefectModule.subsingleton_iff_isIdempotent (C.closureClass x)

/-- Every actual element of the detector vanishes under the original restriction. -/
@[simp]
theorem restriction_defectEmbedding (z : C.DefectModule x) :
    C.restriction (C.defectEmbedding x z) = 0 := by
  obtain ⟨p, rfl⟩ := ProjectorDefectModule.presentation_surjective (C.closureClass x) z
  rw [ProjectorDefectModule.embedding_presentation, map_mul]
  change _ * C.restriction (C.convolutionDefect x) = 0
  rw [C.restriction_convolutionDefect, mul_zero]

theorem defectEmbedding_range_le_kernel :
    LinearMap.range (C.defectEmbedding x) ≤ LinearMap.ker C.restriction.toLinearMap := by
  rintro _ ⟨z, rfl⟩
  exact C.restriction_defectEmbedding x z

/-- Each finite filtration stage is carried to zero by the same restriction. -/
theorem defectFiltration_map_restriction (n : ℕ) :
    ((C.defectFiltration x n).map (C.defectEmbedding x)).map C.restriction.toLinearMap = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨_, ⟨z, _, rfl⟩, rfl⟩
  exact C.restriction_defectEmbedding x z

/-- Vanishing of the constructed object supplies the existing extension witness. -/
def zeroDefectWitness (h : Subsingleton (C.DefectModule x)) : C.ZeroDefectWitness :=
  ⟨x, (C.defectModule_detects x).mp h⟩

end HodgeConjecture.AlgebraProjectorClosure
