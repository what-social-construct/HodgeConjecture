module

public import HodgeConjecture.Geometry.ComplexPointsFunctoriality
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

/-!
# Affine scheme points and their original algebra-valued evaluations

For an actual complex algebra A, scheme sections of Spec A over Spec ℂ
are identified with A →ₐ[ℂ] ℂ. The topology on algebra-valued points is
induced by evaluation of all elements of A, and the identification is a
homeomorphism. This does not replace the analytic topology by a topology
transported through a set equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.AffineComplexPoints

open AlgebraicGeometry CategoryTheory Topology
open AlgebraicGeometry.Scheme.ComplexPoints

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The actual affine structure map determined by the original complex-algebra map. -/
def structureMorphism : Spec (.of A) ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

/-- The evaluation topology, with no global instance on every algebra hom type. -/
@[instance_reducible]
def evaluationTopology : TopologicalSpace (A →ₐ[ℂ] ℂ) :=
  TopologicalSpace.induced (fun φ : A →ₐ[ℂ] ℂ ↦ (φ : A → ℂ)) inferInstance

attribute [local instance] evaluationTopology

/-- Original algebra homomorphisms with their independently specified evaluation topology. -/
abbrev algebraPointSpace : TopCat := TopCat.of (A →ₐ[ℂ] ℂ)

theorem isEmbedding_evaluation : IsEmbedding (fun φ : algebraPointSpace A ↦ (φ : A → ℂ)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

theorem continuous_evaluation (a : A) : Continuous (fun φ : algebraPointSpace A ↦ φ a) :=
  (continuous_apply a).comp (isEmbedding_evaluation A).continuous

/-- An actual algebra-valued point determines its scheme-valued point over ℂ. -/
def ofAlgHom (φ : A →ₐ[ℂ] ℂ) : Scheme.ComplexPoints (structureMorphism A) :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    unfold structureMorphism
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ) using 1
    congr 1
    ext c
    exact φ.commutes c⟩

/-- The original inverse of Spec supplies the algebra-valued evaluation of a scheme point. -/
def toAlgHom (p : Scheme.ComplexPoints (structureMorphism A)) : A →ₐ[ℂ] ℂ := by
  have hc := congrArg Spec.preimage p.hom_comp
  simp only [structureMorphism, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hc
  exact { (Spec.preimage p.hom).hom with
    commutes' := fun c ↦ congrArg (fun h : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ h c) hc }

@[simp]
theorem toAlgHom_ofAlgHom (φ : A →ₐ[ℂ] ℂ) : toAlgHom A (ofAlgHom A φ) = φ := by
  ext a
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom a = φ a
  rw [Spec.preimage_map]
  rfl

@[simp]
theorem ofAlgHom_toAlgHom (p : Scheme.ComplexPoints (structureMorphism A)) :
    ofAlgHom A (toAlgHom A p) = p :=
  Scheme.ComplexPoints.ext (Spec.map_preimage p.hom)

/-- Evaluation is the original ring map of the same affine scheme morphism. -/
theorem eval_ofAlgHom (φ : A →ₐ[ℂ] ℂ) (g : Γ(Spec (.of A), ⊤)) :
    eval g (ofAlgHom A φ) (mem_top _) = φ ((Scheme.ΓSpecIso (.of A)).hom g) := by
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appLE ⊤ ⊤ _ g) = _
  rw [appLE_top_top_eq_appTop]
  exact congrArg (fun h : Γ(Spec (.of A), ⊤) ⟶ CommRingCat.of ℂ ↦ h.hom g)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

theorem eval_eq_toAlgHom (p : Scheme.ComplexPoints (structureMorphism A))
    (g : Γ(Spec (.of A), ⊤)) :
    eval g p (mem_top _) = toAlgHom A p ((Scheme.ΓSpecIso (.of A)).hom g) := by
  simpa only [ofAlgHom_toAlgHom] using eval_ofAlgHom A (toAlgHom A p) g

/-- Adding the proof of membership in the whole open changes no topology. -/
def topOpenHomeomorph : Scheme.ComplexPoints (structureMorphism A) ≃ₜ
    {p : Scheme.ComplexPoints (structureMorphism A) // p.Mem ⊤} :=
  (Homeomorph.Set.univ _).symm.trans
    (Homeomorph.setCongr (Set.ext fun p ↦ ⟨fun _ ↦ mem_top p, fun _ ↦ trivial⟩))

theorem continuous_toAlgHom : Continuous (toAlgHom A : _ → algebraPointSpace A) := by
  apply (isEmbedding_evaluation A).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro a
  have h := (continuous_eval_of_isOpen ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)).comp
    (topOpenHomeomorph A).continuous
  convert h using 1
  funext p
  simp only [Function.comp_apply, topOpenHomeomorph, Homeomorph.trans_apply,
    eval_eq_toAlgHom, Iso.inv_hom_id_apply]
  rfl

theorem continuous_ofAlgHom : Continuous (ofAlgHom A : algebraPointSpace A → _) := by
  have h := (isInducing_evalMap (y := structureMorphism A) (isAffineOpen_top _)).comp
    (topOpenHomeomorph A).isInducing
  apply h.continuous_iff.mpr
  apply continuous_pi
  intro g
  convert continuous_evaluation A ((Scheme.ΓSpecIso (.of A)).hom g) using 1
  funext φ
  exact eval_ofAlgHom A φ g

/-- The analytic scheme topology agrees with the independently defined algebra-point topology. -/
def homeomorph : Scheme.ComplexPoints (structureMorphism A) ≃ₜ algebraPointSpace A where
  toFun := toAlgHom A
  invFun := ofAlgHom A
  left_inv := ofAlgHom_toAlgHom A
  right_inv := toAlgHom_ofAlgHom A
  continuous_toFun := continuous_toAlgHom A
  continuous_invFun := continuous_ofAlgHom A

end HodgeConjecture.AffineComplexPoints
