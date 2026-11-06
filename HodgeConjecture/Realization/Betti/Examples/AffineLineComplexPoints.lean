module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# Actual complex points of the affine line

A complex point of the affine line is a complex-algebra homomorphism
`ℂ[X] →ₐ[ℂ] ℂ`. Its topology is induced by evaluation of all regular
functions with values in the usual complex topology. Evaluation at the
coordinate `X` is proved to be a homeomorphism with the complex plane.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

namespace AffineLineComplexPoints

open Topology AlgebraicGeometry CategoryTheory Polynomial

/-- Complex-valued points of the actual affine-line coordinate ring. -/
abbrev Point := ℂ[X] →ₐ[ℂ] ℂ

/-- The complex point defined by evaluating polynomials at `z`. -/
def evalPoint (z : ℂ) : Point := Polynomial.aeval z

@[simp]
theorem evalPoint_apply (z : ℂ) (f : ℂ[X]) :
    evalPoint z f = Polynomial.aeval z f := rfl

@[simp]
theorem evalPoint_X (z : ℂ) : evalPoint z Polynomial.X = z := by
  simp [evalPoint]

/-- Every actual algebra-valued point is evaluation at its coordinate. -/
@[simp]
theorem evalPoint_coordinate (p : Point) : evalPoint (p Polynomial.X) = p :=
  (Polynomial.aevalEquiv ℂ ℂ).apply_symm_apply p

/-- Algebraic classification by the value of the coordinate. -/
def coordinateEquiv : Point ≃ ℂ := (Polynomial.aevalEquiv ℂ ℂ).symm

@[simp]
theorem coordinateEquiv_apply (p : Point) : coordinateEquiv p = p Polynomial.X := rfl

@[simp]
theorem coordinateEquiv_symm_apply (z : ℂ) :
    coordinateEquiv.symm z = evalPoint z := rfl

instance pointNonempty : Nonempty Point := ⟨evalPoint 0⟩

/-- The topology induced by all regular-function evaluations in the usual
complex topology, rather than transported from an algebraic classification. -/
instance pointTopology : TopologicalSpace Point :=
  TopologicalSpace.induced (fun p : Point ↦ (p : ℂ[X] → ℂ)) inferInstance

/-- The actual point space is a subspace of the space of regular-function
evaluations. -/
theorem isEmbedding_evaluation :
    IsEmbedding (fun p : Point ↦ (p : ℂ[X] → ℂ)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

instance pointT2Space : T2Space Point := isEmbedding_evaluation.t2Space

/-- Each regular function is continuous on the actual complex point space. -/
theorem continuous_evaluation (f : ℂ[X]) : Continuous (fun p : Point ↦ p f) :=
  (continuous_apply f).comp isEmbedding_evaluation.continuous

/-- Polynomial evaluation varies continuously with the complex coordinate. -/
theorem continuous_evalPoint : Continuous evalPoint := by
  apply isEmbedding_evaluation.isInducing.continuous_iff.mpr
  exact continuous_pi fun f ↦ f.continuous_aeval

/-- The actual complex points of the affine line are homeomorphic to the
usual complex plane by evaluation at the coordinate. -/
def coordinateHomeomorph : Point ≃ₜ ℂ where
  toEquiv := coordinateEquiv
  continuous_toFun := continuous_evaluation Polynomial.X
  continuous_invFun := continuous_evalPoint

@[simp]
theorem coordinateHomeomorph_apply (p : Point) :
    coordinateHomeomorph p = p Polynomial.X := rfl

@[simp]
theorem coordinateHomeomorph_symm_apply (z : ℂ) :
    coordinateHomeomorph.symm z = evalPoint z := rfl

/-- Path connectedness follows from the proven homeomorphism for the
regular-function evaluation topology. -/
instance pointPathConnectedSpace : PathConnectedSpace Point :=
  letI : PathConnectedSpace ℂ := IsTopologicalAddGroup.pathConnectedSpace
  coordinateHomeomorph.symm.pathConnectedSpace

/-- Polynomial substitution induces the actual map on algebra-valued
complex points by precomposition of algebra homomorphisms. -/
def map (f : ℂ[X]) (p : Point) : Point := p.comp (Polynomial.aeval f)

@[simp]
theorem map_apply (f g : ℂ[X]) (p : Point) :
    map f p g = p (Polynomial.aeval f g) := rfl

@[simp]
theorem map_X (f : ℂ[X]) (p : Point) : map f p Polynomial.X = p f := by
  simp [map]

@[simp]
theorem map_evalPoint (f : ℂ[X]) (z : ℂ) :
    map f (evalPoint z) = evalPoint (Polynomial.aeval z f) := by
  apply Polynomial.algHom_ext
  simp

/-- The polynomial point map is continuous in the actual evaluation topology. -/
theorem map_continuous (f : ℂ[X]) : Continuous (map f) := by
  apply isEmbedding_evaluation.isInducing.continuous_iff.mpr
  exact continuous_pi fun g ↦ continuous_evaluation (Polynomial.aeval f g)

/-- The continuous self-map of the actual complex affine line defined by
a polynomial. -/
def mapContinuous (f : ℂ[X]) : C(Point, Point) := ⟨map f, map_continuous f⟩

@[simp]
theorem mapContinuous_apply (f : ℂ[X]) (p : Point) : mapContinuous f p = map f p := rfl

@[simp]
theorem coordinateHomeomorph_map (f : ℂ[X]) (p : Point) :
    coordinateHomeomorph (map f p) = p f := map_X f p

/-- The affine line as an actual affine scheme. -/
def scheme : Scheme := Spec (.of ℂ[X])

/-- The structure morphism to the complex base. -/
def toBase : scheme ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ[X]))

/-- Each algebra-valued point defines an actual affine-scheme morphism. -/
def schemeMorphism (p : Point) : Spec (.of ℂ) ⟶ scheme :=
  Spec.map (CommRingCat.ofHom p.toRingHom)

/-- The actual affine-scheme self-map whose coordinate pullback is
polynomial substitution. -/
def schemeMap (f : ℂ[X]) : scheme ⟶ scheme :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval f).toRingHom)

/-- Precomposition of algebra-valued points agrees with composition of
the corresponding actual affine-scheme morphisms. -/
@[simp, reassoc]
theorem schemeMorphism_map (f : ℂ[X]) (p : Point) :
    schemeMorphism p ≫ schemeMap f = schemeMorphism (map f p) := by
  unfold schemeMorphism schemeMap
  rw [← Spec.map_comp]
  rfl

/-- The associated affine-scheme morphism is over the complex base. -/
@[simp, reassoc]
theorem schemeMorphism_toBase (p : Point) :
    schemeMorphism p ≫ toBase = 𝟙 (Spec (.of ℂ)) := by
  unfold schemeMorphism toBase
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of ℂ) using 1
  congr 1
  ext c
  exact p.commutes c

end AffineLineComplexPoints

end

end HodgeConjecture
