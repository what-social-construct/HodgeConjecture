import HodgeConjecture.Boundary.Normalization.NormalClosure

/-!
# Constructing marked finite normal closures

A finite field extension constructs its marked normal closure inside the
algebraic closure of the upstairs field.  The distinguished embedding is the
canonical upstairs-field inclusion. The imported normal-closure core proves
separability and Galoisness from separability of the marked extension.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations.NormalClosureData

noncomputable section

universe uK uL

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

end

end HodgeConjecture.CollisionFoundations.NormalClosureData
