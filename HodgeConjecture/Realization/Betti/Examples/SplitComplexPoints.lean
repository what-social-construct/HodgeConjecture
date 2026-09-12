import HodgeConjecture.CommutativeAlgebra.SplitFieldQuotient
import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual complex points of finite split schemes

The point space consists of complex-algebra homomorphisms from the coordinate
ring, with its topology induced by evaluation of regular functions. Prime-kernel
classification identifies every such homomorphism with evaluation at a unique
component. This proves, rather than declares, that the point space is finite
and discrete.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

namespace SplitComplexPoints

open Classical Topology AlgebraicGeometry CategoryTheory

variable (I : Type)

/-- Complex-valued points of the actual split affine coordinate ring. -/
abbrev Point := (I → ℂ) →ₐ[ℂ] ℂ

/-- The rational complex point given by evaluation at a component. -/
def evalPoint (i : I) : Point I := Pi.evalAlgHom ℂ (fun _ : I ↦ ℂ) i

@[simp]
theorem evalPoint_apply (i : I) (a : I → ℂ) : evalPoint I i a = a i := rfl

theorem evalPoint_injective : Function.Injective (evalPoint I) := by
  intro i j h
  by_contra hij
  have h' := congrArg (fun p : Point I ↦ p (Pi.single i 1)) h
  simp [Ne.symm hij] at h'

variable [Finite I]

/-- Every complex point of the finite split affine scheme is a unique
component evaluation, established from the actual homomorphism's prime kernel. -/
theorem existsUnique_eq_evalPoint (p : Point I) : ∃! i : I, p = evalPoint I i := by
  letI : (RingHom.ker p.toRingHom).IsPrime := RingHom.ker_isPrime p.toRingHom
  obtain ⟨i, hi, _⟩ := SplitFieldQuotient.existsUnique_prime_eq_ker_eval ℂ I
    (RingHom.ker p.toRingHom)
  have hp : p = evalPoint I i := by
    ext a
    have hmem : a - algebraMap ℂ (I → ℂ) (a i) ∈ RingHom.ker p.toRingHom := by
      rw [hi]
      simp [RingHom.mem_ker]
    have hz : p a - a i = 0 := by simpa [RingHom.mem_ker] using hmem
    exact sub_eq_zero.mp hz
  exact ⟨i, hp, fun j hj ↦ evalPoint_injective I (hj.symm.trans hp)⟩

/-- The classification equivalence from labels to actual algebra-valued points. -/
def labelEquiv : I ≃ Point I :=
  Equiv.ofBijective (evalPoint I) ⟨evalPoint_injective I, fun p ↦ by
    obtain ⟨i, hi, _⟩ := existsUnique_eq_evalPoint I p
    exact ⟨i, hi.symm⟩⟩

@[simp]
theorem labelEquiv_apply (i : I) : labelEquiv I i = evalPoint I i := rfl

@[simp]
theorem labelEquiv_symm_evalPoint (i : I) :
    (labelEquiv I).symm (evalPoint I i) = i :=
  (labelEquiv I).symm_apply_apply i

instance : Finite (Point I) := Finite.of_equiv I (labelEquiv I)

instance pointFintype [Fintype I] : Fintype (Point I) :=
  Fintype.ofEquiv I (labelEquiv I)

variable {I}
variable {S : Type}

/-- The actual map on complex points, obtained by precomposing algebra maps
with the pullback map of coordinate rings. -/
def map (f : S → I) (p : Point S) : Point I :=
  p.comp (SplitPointGeometry.precompose ℂ f)

omit [Finite I] in
@[simp]
theorem map_apply (f : S → I) (p : Point S) (a : I → ℂ) :
    map f p a = p (a ∘ f) := rfl

omit [Finite I] in
@[simp]
theorem map_evalPoint (f : S → I) (s : S) :
    map f (evalPoint S s) = evalPoint I (f s) := rfl

@[simp]
theorem map_labelEquiv [Finite S] (f : S → I) (s : S) :
    map f (labelEquiv S s) = labelEquiv I (f s) := rfl

/-- The actual affine-scheme morphism corresponding to the complex algebra point. -/
def schemeMorphism (p : Point I) : Spec (.of ℂ) ⟶ SplitPointGeometry.scheme ℂ I :=
  Spec.map (CommRingCat.ofHom p.toRingHom)

omit [Finite I] in
@[simp]
theorem schemeMorphism_evalPoint (i : I) :
    schemeMorphism (evalPoint I i) = SplitPointGeometry.pointInclusion ℂ I i := rfl

omit [Finite I] in
/-- Naturality holds for the corresponding actual scheme morphisms as well. -/
@[simp, reassoc]
theorem schemeMorphism_map (f : S → I) (p : Point S) :
    schemeMorphism p ≫ SplitPointGeometry.mapOfFunction ℂ f =
      schemeMorphism (map f p) := by
  unfold schemeMorphism SplitPointGeometry.mapOfFunction
  rw [← Spec.map_comp]
  rfl

omit [Finite I] in
/-- Complex-algebra points are scheme morphisms over the complex base. -/
@[simp, reassoc]
theorem schemeMorphism_toBase (p : Point I) :
    schemeMorphism p ≫ SplitPointGeometry.toBase ℂ I = 𝟙 (Spec (.of ℂ)) := by
  unfold schemeMorphism SplitPointGeometry.toBase
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of ℂ) using 1
  congr 1
  ext c
  exact p.commutes c

variable (I)

/-- The topology induced by evaluating all actual regular functions, using
the ordinary complex topology on their values. -/
instance pointTopology : TopologicalSpace (Point I) :=
  TopologicalSpace.induced (fun p : Point I ↦ (p : (I → ℂ) → ℂ)) inferInstance

omit [Finite I] in
/-- The point space is genuinely a subspace of the space of regular-function
evaluations, not a topology transported from its labels. -/
theorem isEmbedding_evaluation :
    IsEmbedding (fun p : Point I ↦ (p : (I → ℂ) → ℂ)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

instance pointT2Space : T2Space (Point I) := (isEmbedding_evaluation I).t2Space

instance pointDiscreteTopology : DiscreteTopology (Point I) := inferInstance

omit [Finite I] in
/-- Evaluation of each regular function is continuous in the complex-point
topology. -/
theorem continuous_evaluation (a : I → ℂ) : Continuous (fun p : Point I ↦ p a) :=
  (continuous_apply a).comp (isEmbedding_evaluation I).continuous

/-- The actual complex point space is homeomorphic to the discrete label set. -/
def labelHomeomorph [TopologicalSpace I] [DiscreteTopology I] : I ≃ₜ Point I where
  toEquiv := labelEquiv I
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp]
theorem labelHomeomorph_apply [TopologicalSpace I] [DiscreteTopology I] (i : I) :
    labelHomeomorph I i = evalPoint I i := rfl

variable {I}

omit [Finite I] in
/-- The algebraically induced point map is continuous in the actual
regular-function evaluation topologies. -/
theorem map_continuous [Finite S] (f : S → I) : Continuous (map f) :=
  continuous_of_discreteTopology

/-- The induced continuous map on complex point spaces. -/
def mapContinuous [Finite S] (f : S → I) : C(Point S, Point I) :=
  ⟨map f, map_continuous f⟩

omit [Finite I] in
@[simp]
theorem mapContinuous_apply [Finite S] (f : S → I) (p : Point S) :
    mapContinuous f p = map f p := rfl

variable (I) (J : Type) [Finite J]

/-- Product-point classification, induced by the proven classification of
the actual algebra-valued points in each factor. -/
def productEquiv : Point (I × J) ≃ Point I × Point J :=
  (labelEquiv (I × J)).symm.trans ((labelEquiv I).prodCongr (labelEquiv J))

/-- The product comparison for actual complex point spaces. -/
def productHomeomorph : Point (I × J) ≃ₜ Point I × Point J where
  toEquiv := productEquiv I J
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp]
theorem productHomeomorph_fst (p : Point (I × J)) :
    (productHomeomorph I J p).1 = map Prod.fst p := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (labelEquiv (I × J)).surjective p
  simp [productHomeomorph, productEquiv]

@[simp]
theorem productHomeomorph_snd (p : Point (I × J)) :
    (productHomeomorph I J p).2 = map Prod.snd p := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (labelEquiv (I × J)).surjective p
  simp [productHomeomorph, productEquiv]

end SplitComplexPoints

end

end HodgeConjecture
