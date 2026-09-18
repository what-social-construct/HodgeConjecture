import HodgeConjecture.Boundary.Normalization.NormalClosure
import Mathlib.FieldTheory.SeparableClosure

/-!
# Constructing marked finite normal closures

A finite field extension constructs its marked normal closure inside the
algebraic closure of the upstairs field.  The distinguished embedding is the
canonical upstairs-field inclusion.  Separability passes from a marked
extension to any supplied normal closure, so a separable marked extension
gives a Galois normal closure without requiring a perfect base field.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations.NormalClosureData

noncomputable section

universe uK uL uN

/-- A finite extension constructs a marked finite normal closure inside the
algebraic closure of its upstairs field. -/
def ofAlgebraicClosure (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    NormalClosureData K L
      (IntermediateField.normalClosure K L (AlgebraicClosure L)) := by
  letI : Nonempty (L →ₐ[K] AlgebraicClosure L) :=
    ⟨IsScalarTower.toAlgHom K L (AlgebraicClosure L)⟩
  exact {
    embedding := IsScalarTower.toAlgHom K L _
    normalClosure := inferInstance
    finiteIntermediate := inferInstance
    finiteNormal := inferInstance }

/-- The marked embedding is the original inclusion of the upstairs field
into its algebraic closure. -/
theorem ofAlgebraicClosure_embedding_apply (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) :
    ((ofAlgebraicClosure K L).embedding x : AlgebraicClosure L) =
      algebraMap L (AlgebraicClosure L) x := rfl

variable {K : Type uK} {L : Type uL} {N : Type uN}
  [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]

/-- A marked normal closure of a separable extension is separable over the
base field. -/
theorem isSeparable [Algebra.IsSeparable K L] (D : NormalClosureData K L N) :
    Algebra.IsSeparable K N := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : IsNormalClosure K L N := D.normalClosure
  have hNormalClosure : IntermediateField.normalClosure K L N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff
      (F := K) (K := L) (L := N)).mp inferInstance |>.2
  have hle : IntermediateField.normalClosure K L N ≤ separableClosure K N := by
    rw [normalClosure_le_iff]
    intro f
    letI : Algebra.IsSeparable K f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    exact le_separableClosure K N f.fieldRange
  apply (separableClosure.eq_top_iff K N).mp
  apply top_unique
  rw [← hNormalClosure]
  exact hle

/-- A marked normal closure of a separable extension is Galois; perfectness
of the base field is not required. -/
theorem isGalois_of_isSeparable [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N) : IsGalois K N := by
  letI : Algebra.IsSeparable K N := D.isSeparable
  letI : Normal K N := D.normal
  exact IsGalois.mk

end

end HodgeConjecture.CollisionFoundations.NormalClosureData
