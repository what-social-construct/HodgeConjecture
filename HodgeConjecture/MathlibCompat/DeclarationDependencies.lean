module

public meta import Lean.Util.FoldConsts
public meta import Lean.Environment

public meta section

/-! Checked declaration traversal for research dependency audits.

Lean's public axiom collector returns cached axiom names. Dependency audits
also need the transitive declarations in statement types and definition or
proof bodies, including private imported declarations. This traversal keeps
that separate information without relying on the collector's private state.
-/

namespace HodgeConjecture.Research

partial def visitDeclarations (env : Lean.Environment)
    (pending : List Lean.Name) (seen : Lean.NameSet) : Lean.NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then visitDeclarations env rest seen
    else
      let dependencies := match env.checked.get.find? name with
        | some (.inductInfo info) => info.type.getUsedConstants.toList ++ info.ctors
        | some (.quotInfo _) => []
        | some info => info.type.getUsedConstants.toList ++
            ((info.value? (allowOpaque := true)).map Lean.Expr.getUsedConstants
              |>.getD #[]).toList
        | none => []
      visitDeclarations env (dependencies ++ rest) (seen.insert name)

/-- All transitive constants used by a declaration, including its type. -/
def declarationDependencies (env : Lean.Environment) (endpoint : Lean.Name) : Lean.NameSet :=
  visitDeclarations (env.setExporting false) [endpoint] {}

end HodgeConjecture.Research
