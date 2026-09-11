import HodgeConjecture.Correspondence.EtaleClasses
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Split finite schemes and point-supported projectors

For a finite set `I`, the scheme `Spec (I → K)` is a finite étale, hence
proper, scheme over `Spec K`. Each component gives an actual finite étale
span whose convolution square is isomorphic to itself.

The resulting idempotent lies in the free finite-étale span algebra. No
identification with a Chow group or a Betti cycle-class map is asserted.
For `I = Fin 2` and `i = 0`, this is the geometric span underlying the
two-point matrix unit `e₀₀`; proving a cycle realization between this
construction and the matrix model remains a separate task. In particular,
the free span algebra does not impose disjoint-union additivity or identify
the empty span with its additive zero.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K] (I : Type u) [Finite I]

/-- The finite split scheme indexed by `I`. -/
def scheme : Scheme.{u} := Spec (.of (I → K))

/-- Its structure map is induced by the constant-functions algebra map. -/
def toBase : scheme K I ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (I → K)))

instance : IsFinite (toBase K I) := by
  apply (IsFinite.SpecMap_iff _).2
  change (algebraMap K (I → K)).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

omit [Finite I] in
/-- The finite coproduct presentation respects the structure map. -/
theorem sigmaSpec_comp_toBase :
    sigmaSpec (fun _ : I ↦ CommRingCat.of K) ≫ toBase K I =
      Sigma.desc (fun _ : I ↦ 𝟙 (Spec (.of K))) := by
  apply Sigma.hom_ext
  intro i
  simp only [ι_sigmaSpec_assoc, Sigma.ι_desc]
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : I ↦ K) i)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (I → K))) = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap K (I → K)) ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I ↦ K) i) =
      𝟙 (CommRingCat.of K) := by
    ext x
    rfl
  rw [h, Spec.map_id]

instance : IsEtale (toBase K I) := by
  apply (MorphismProperty.cancel_left_of_respectsIso @IsEtale
    (sigmaSpec (fun _ : I ↦ CommRingCat.of K)) (toBase K I)).mp
  rw [sigmaSpec_comp_toBase]
  exact IsZariskiLocalAtSource.sigmaDesc
    (fun _ ↦ MorphismProperty.id_mem @IsEtale (Spec (.of K)))

/-- A finite split scheme is already proper; no boundary is needed. -/
instance : IsProper (toBase K I) := inferInstance

/-- The inclusion of the component indexed by `i`. -/
def pointInclusion (i : I) : Spec (.of K) ⟶ scheme K I :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : I ↦ K) i))

instance (i : I) : IsOpenImmersion (pointInclusion K I i) := by
  unfold pointInclusion
  infer_instance

instance (i : I) : IsClosedImmersion (pointInclusion K I i) :=
  IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval _)

instance (i : I) : IsFinite (pointInclusion K I i) := inferInstance

instance (i : I) : IsEtale (pointInclusion K I i) :=
  IsZariskiLocalAtSource.of_isOpenImmersion _

/-- The actual scheme span supported on a single diagonal point. -/
def pointSpan (i : I) : SchemeCorrespondence (toBase K I) (toBase K I) where
  carrier := Spec (.of K)
  left := pointInclusion K I i
  right := pointInclusion K I i
  over_base := rfl

omit [Finite I] in
theorem pointSpan_hasFiniteEtaleLegs (i : I) :
    SchemeCorrespondence.HasFiniteEtaleLegs (pointSpan K I i) := by
  constructor
  · constructor <;> exact inferInstanceAs (IsEtale (pointInclusion K I i))
  · exact inferInstanceAs (IsFinite (pointInclusion K I i))
  · exact inferInstanceAs (IsFinite (pointInclusion K I i))

/-- Pulling a point inclusion back along itself gives the same point. -/
def pointSpan_comp_self_iso (i : I) :
    SchemeCorrespondence.Isom
      ((pointSpan K I i).comp (pointSpan K I i)) (pointSpan K I i) where
  carrierIso := asIso (pullback.fst (pointInclusion K I i) (pointInclusion K I i))
  hom_left := rfl
  hom_right := pullback.condition

/-- The basis class of the point-supported span. -/
def pointProjector (i : I) :
    SchemeCorrespondence.FiniteEtaleFreeAlgebra (toBase K I) :=
  SchemeCorrespondence.finiteEtaleOfScheme (pointSpan K I i)
    (pointSpan_hasFiniteEtaleLegs K I i)

omit [Finite I] in
/-- Idempotence is proved by a geometric pullback isomorphism. -/
theorem pointProjector_isIdempotent (i : I) :
    IsIdempotentElem (pointProjector K I i) := by
  unfold IsIdempotentElem pointProjector SchemeCorrespondence.finiteEtaleOfScheme
  rw [MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  apply Subtype.ext
  exact (SchemeCorrespondence.classOf_eq_of_isom
    (pointSpan_comp_self_iso K I i))

end SplitPointGeometry

end

end HodgeConjecture
