module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# The analytic topology on actual complex-valued scheme points

Selected definition and proof adaptation from AxiomMath/Weil, revision
`27cdb2049be62ee2911429b47f54774078450e32`:
`Weil/Definitions.lean` (complex points only) and
`Weil/Defs/AlgebraicGeometry/ComplexPoints/AnalyticTopology.lean`.
Apache-2.0; see `third_party/axiom-weil/LICENSE`.
The monolithic definitions import and metadata attributes are omitted.

Points are actual scheme sections over the complex base. The topology is
constructed from affine-open regular-function evaluations in the usual
complex topology. This defines the topological space needed for a general
Betti target; it does not construct a holomorphic structure sheaf, a
Betti–de Rham comparison or a geometric purity theorem.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The complex points `Y(ℂ)` of a scheme `Y` over `ℂ` with structure morphism `y`: the
sections `p : Spec ℂ ⟶ Y` of `y`. -/
def ComplexPoints {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) : Type :=
  {p : Spec (.of ℂ) ⟶ Y // p ≫ y = 𝟙 _}

namespace ComplexPoints

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- The underlying morphism `Spec ℂ ⟶ Y` of a complex point. -/
def hom (p : ComplexPoints y) : Spec (.of ℂ) ⟶ Y := p.1

/-- The point `p ∈ Y(ℂ)` lies in `U(ℂ)`: the preimage of `U` under `p` is all of `Spec ℂ`. -/
def Mem (p : ComplexPoints y) (U : Y.Opens) : Prop := p.hom ⁻¹ᵁ U = ⊤

/-- The value `g(p) ∈ ℂ` of a regular function `g ∈ Γ(Y, U)` at a point `p ∈ U(ℂ)`: the image of
`g` under `p^* : Γ(Y, U) → Γ(Spec ℂ, ⊤) ≅ ℂ`. -/
noncomputable def eval {U : Y.Opens} (g : Γ(Y, U)) (p : ComplexPoints y) (hp : p.Mem U) : ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom (p.hom.appLE U ⊤ hp.ge g)

/-- The generating sets of the analytic topology: `{p ∈ U(ℂ) | g(p) ∈ V}`. -/
def basicSet (U : Y.Opens) (g : Γ(Y, U)) (V : Set ℂ) : Set (ComplexPoints y) :=
  {p | ∃ hp : p.Mem U, eval g p hp ∈ V}

/-- The family of generating sets of the analytic topology: `basicSet U g V` for `U` an affine
open of `Y`, `g ∈ Γ(Y, U)` and `V ⊆ ℂ` open. -/
def basicSets (y : Y ⟶ Spec (.of ℂ)) : Set (Set (ComplexPoints y)) :=
  {s | ∃ (U : Y.Opens) (_ : IsAffineOpen U) (g : Γ(Y, U)) (V : Set ℂ) (_ : IsOpen V),
    s = basicSet U g V}

/-- The analytic topology on `Y(ℂ)`: the coarsest topology for which `U(ℂ)` is open and every
`g ∈ Γ(Y, U)` is continuous on `U(ℂ)`, for every affine open `U` of `Y`. -/
instance instTopologicalSpace : TopologicalSpace (ComplexPoints y) :=
  TopologicalSpace.generateFrom (basicSets y)

end ComplexPoints

end AlgebraicGeometry.Scheme

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

namespace ComplexPoints

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

@[ext]
theorem ext {p q : ComplexPoints y} (h : p.hom = q.hom) : p = q := Subtype.ext h

@[simp]
theorem hom_comp (p : ComplexPoints y) : p.hom ≫ y = 𝟙 _ := p.2

theorem isOpen_basicSet {U : Y.Opens} (hU : IsAffineOpen U) (g : Γ(Y, U)) {V : Set ℂ}
    (hV : IsOpen V) : IsOpen (basicSet (y := y) U g V) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨U, hU, g, V, hV, rfl⟩

/-- A map into `Y(ℂ)` is continuous iff the preimage of every generating set
`{p ∈ U(ℂ) | g(p) ∈ V}` is open. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → ComplexPoints y} :
    Continuous f ↔ ∀ (U : Y.Opens), IsAffineOpen U → ∀ (g : Γ(Y, U)) (V : Set ℂ), IsOpen V →
      IsOpen (f ⁻¹' basicSet U g V) := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro h U hU g V hV
    exact h _ ⟨U, hU, g, V, hV, rfl⟩
  · rintro h _ ⟨U, hU, g, V, hV, rfl⟩
    exact h U hU g V hV

/-- A complex point lies in `U(ℂ)` iff the image of the unique point of `Spec ℂ` lies in `U`. -/
theorem mem_iff {p : ComplexPoints y} {U : Y.Opens} (x : Spec (.of ℂ)) :
    p.Mem U ↔ p.hom.base x ∈ U := by
  have : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  constructor
  · intro h
    have : x ∈ p.hom ⁻¹ᵁ U := by rw [h]; trivial
    exact this
  · intro h
    refine eq_top_iff.2 fun z _ => ?_
    rw [Subsingleton.elim z x]
    exact h

/-- With `V = ℂ`, the set `{p ∈ U(ℂ) | g(p) ∈ V}` is `U(ℂ)`. -/
theorem basicSet_univ (U : Y.Opens) (g : Γ(Y, U)) :
    basicSet (y := y) U g Set.univ = {p | p.Mem U} := by
  ext p; simp [basicSet]

/-- `U(ℂ)` is open for every affine open `U`. -/
theorem isOpen_setOf_mem_of_isAffineOpen {U : Y.Opens} (hU : IsAffineOpen U) :
    IsOpen {p : ComplexPoints y | p.Mem U} := by
  rw [← basicSet_univ U 0]
  exact isOpen_basicSet hU 0 isOpen_univ

/-- `U(ℂ)` is open for every open `U` of `Y`. -/
theorem isOpen_setOf_mem (U : Y.Opens) : IsOpen {p : ComplexPoints y | p.Mem U} := by
  have : {p : ComplexPoints y | p.Mem U} =
      ⋃ (V : Y.affineOpens) (_ : (V : Y.Opens) ≤ U), {p : ComplexPoints y | p.Mem V} := by
    ext p
    obtain ⟨x⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_iff x]
    constructor
    · intro h
      obtain ⟨V, hV, hxV, hVU⟩ :=
        (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) h
      exact ⟨⟨V, hV⟩, hVU, hxV⟩
    · rintro ⟨V, hVU, h⟩
      exact hVU h
  rw [this]
  exact isOpen_iUnion fun V => isOpen_iUnion fun _ => isOpen_setOf_mem_of_isAffineOpen V.2

/-- A regular function `g` on an affine open `U` is continuous as a function `U(ℂ) → ℂ`. -/
theorem continuous_eval {U : Y.Opens} (hU : IsAffineOpen U) (g : Γ(Y, U)) :
    Continuous fun p : {p : ComplexPoints y // p.Mem U} => eval g p.1 p.2 := by
  rw [continuous_def]
  intro V hV
  convert (isOpen_basicSet (y := y) hU g hV).preimage continuous_subtype_val using 1
  ext p
  exact ⟨fun h => ⟨p.2, h⟩, fun ⟨_, h⟩ => h⟩

end ComplexPoints

end AlgebraicGeometry.Scheme
