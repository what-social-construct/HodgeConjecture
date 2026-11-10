module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Opposite

@[expose] public section

/-!
# Quasi-isomorphisms on kernels of actual short exact sequences

The native third-term comparison theorem, applied to opposite complexes,
gives the corresponding first-term theorem. This will carry the actual
full-to-small cochain comparison to the actual relative kernels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ShortExactQuasiIso

open CategoryTheory HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S T : ShortComplex (HomologicalComplex C c)}

/-- A morphism of actual short exact sequences is a quasi-isomorphism on its
kernel term when it is one on the middle and quotient terms. -/
theorem left (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  let F := HomologicalComplex.opFunctor C c
  let ψ : T.op.map F ⟶ S.op.map F := F.mapShortComplex.map (ShortComplex.opMap φ)
  have : Mono S.op.f := hS.op.mono_f
  have : Epi S.op.g := hS.op.epi_g
  have : Mono T.op.f := hT.op.mono_f
  have : Epi T.op.g := hT.op.epi_g
  have hs := hS.op.map F
  have ht := hT.op.map F
  have h₁' : QuasiIso ψ.τ₁ := by
    change QuasiIso (F.map φ.τ₃.op)
    exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₃).mpr h₃
  have h₂' : QuasiIso ψ.τ₂ := by
    change QuasiIso (F.map φ.τ₂.op)
    exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₂).mpr h₂
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ ht hs h₁' h₂'
  change QuasiIso (F.map φ.τ₁.op) at h
  exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h

end HodgeConjecture.ShortExactQuasiIso
