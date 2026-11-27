module

public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Polynomial.Ideal

@[expose] public section

/-!
# Actual affine normal charts at finite projective-line points

The polynomial algebra automorphism `X ↦ u * X + a` gives an actual
affine-scheme isomorphism. Following it by the original first chart of
the glued projective line gives a normal chart with the same original
open range. Its evaluation sections have exactly the coordinate
`a + u * z`. Over a field its center is the actual closed scheme point
defined by evaluation at `a`, independently of the chosen unit `u`.

No global projective-line translation or scheme automorphism is claimed.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineAffineChart

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-- The original polynomial coordinate automorphism, including its actual inverse. -/
def coordinateEquiv (a : k) (v : kˣ) : Polynomial k ≃ₐ[k] Polynomial k :=
  Polynomial.algEquivCMulXAddC (v : k) a

@[simp]
theorem coordinateEquiv_C (a c : k) (v : kˣ) :
    coordinateEquiv k a v (Polynomial.C c) = Polynomial.C c :=
  (coordinateEquiv k a v).commutes c

@[simp]
theorem coordinateEquiv_X (a : k) (v : kˣ) :
    coordinateEquiv k a v Polynomial.X =
      Polynomial.C (v : k) * Polynomial.X + Polynomial.C a := by
  simp [coordinateEquiv]

/-- The actual affine scheme isomorphism induced by the polynomial automorphism. -/
def affineIso (a : k) (v : kˣ) :
    Spec (.of (Polynomial k)) ≅ Spec (.of (Polynomial k)) :=
  Scheme.Spec.mapIso (coordinateEquiv k a v).toRingEquiv.toCommRingCatIso.op

@[simp]
theorem affineIso_hom (a : k) (v : kˣ) :
    (affineIso k a v).hom =
      Spec.map (CommRingCat.ofHom (coordinateEquiv k a v).toRingHom) := rfl

/-- The actual affine normal chart in the original glued projective line. -/
def normalChart (a : k) (v : kˣ) :
    Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  (affineIso k a v).hom ≫ projectiveLineXChart k

instance normalChart_isOpenImmersion (a : k) (v : kˣ) :
    IsOpenImmersion (normalChart k a v) := by
  unfold normalChart
  infer_instance

/-- Reparametrizing the affine chart does not change its actual scheme-point range. -/
theorem normalChart_range (a : k) (v : kˣ) :
    Set.range (normalChart k a v).base = Set.range (projectiveLineXChart k).base := by
  unfold normalChart
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    ((affineIso k a v).hom.surjective).range_comp]

/-- The actual open subscheme range remains the original finite chart. -/
theorem normalChart_opensRange (a : k) (v : kˣ) :
    (normalChart k a v).opensRange = (projectiveLineXChart k).opensRange := by
  ext x
  change x ∈ Set.range (normalChart k a v).base ↔
    x ∈ Set.range (projectiveLineXChart k).base
  rw [normalChart_range]

@[simp, reassoc]
theorem affineIso_over_base (a : k) (v : kˣ) :
    (affineIso k a v).hom ≫ projectiveLineAffineStructureMorphism k =
      projectiveLineAffineStructureMorphism k := by
  rw [affineIso_hom]
  unfold projectiveLineAffineStructureMorphism
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact coordinateEquiv_C k a c v

/-- The chart retains the actual original base structure. -/
@[simp, reassoc]
theorem normalChart_over_base (a : k) (v : kˣ) :
    normalChart k a v ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k := by
  unfold normalChart
  rw [Category.assoc, projectiveLineXChart_comp_structureMorphism, affineIso_over_base]

/-- The actual affine evaluation section at the specified scalar. -/
def affineSection (z : k) : Spec (.of k) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom z))

/-- The actual finite-coordinate section in the original glued projective line. -/
def finiteSection (z : k) : Spec (.of k) ⟶ projectiveLine k :=
  affineSection k z ≫ projectiveLineXChart k

@[simp, reassoc]
theorem affineSection_over_base (z : k) :
    affineSection k z ≫ projectiveLineAffineStructureMorphism k = 𝟙 (Spec (.of k)) := by
  unfold affineSection projectiveLineAffineStructureMorphism
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of k) using 1
  congr 1
  ext c
  exact Polynomial.eval_C

@[simp, reassoc]
theorem finiteSection_over_base (z : k) :
    finiteSection k z ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) := by
  unfold finiteSection
  rw [Category.assoc, projectiveLineXChart_comp_structureMorphism, affineSection_over_base]

/-- The actual affine coordinate isomorphism evaluates to the expected original section. -/
@[simp, reassoc]
theorem affineSection_affineIso (a z : k) (v : kˣ) :
    affineSection k z ≫ (affineIso k a v).hom = affineSection k (a + (v : k) * z) := by
  rw [affineIso_hom]
  unfold affineSection
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    simp
  · simp [add_comm]

/-- The original normal-chart evaluation is the same actual finite scheme section. -/
@[simp, reassoc]
theorem affineSection_normalChart (a z : k) (v : kˣ) :
    affineSection k z ≫ normalChart k a v = finiteSection k (a + (v : k) * z) := by
  unfold normalChart finiteSection
  rw [← Category.assoc, affineSection_affineIso]

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The actual affine prime point obtained from the original evaluation section. -/
def affineCenter (a : k) : Spec (.of (Polynomial k)) :=
  affineSection k a (default : Spec (.of k))

/-- Its original prime ideal is the actual kernel of evaluation at the center. -/
theorem affineCenter_asIdeal (a : k) :
    (affineCenter k a).asIdeal =
      Ideal.span ({Polynomial.X - Polynomial.C a} : Set (Polynomial k)) := by
  change Ideal.comap (Polynomial.evalRingHom a) (⊥ : Ideal k) = _
  rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]

@[simp]
theorem affineSection_base (a : k) (q : Spec (.of k)) :
    affineSection k a q = affineCenter k a := by
  have hq : q = (default : Spec (.of k)) := Subsingleton.elim _ _
  rw [hq]
  rfl

@[simp]
theorem affineCenter_zero : affineCenter k 0 = affineLineOrigin k := by
  apply PrimeSpectrum.ext
  rw [affineCenter_asIdeal]
  simp [affineLineOrigin]

/-- The center is the actual finite scheme point in the original first chart. -/
def center (a : k) : projectiveLine k :=
  projectiveLineXChart k (affineCenter k a)

@[simp]
theorem finiteSection_base (a : k) (q : Spec (.of k)) :
    finiteSection k a q = center k a := by
  unfold finiteSection center
  rw [Scheme.Hom.comp_apply, affineSection_base]

/-- Normal-chart evaluation at every rational affine point retains the original scheme point. -/
theorem normalChart_center (a z : k) (v : kˣ) :
    normalChart k a v (affineCenter k z) = center k (a + (v : k) * z) := by
  have h := congrArg (fun f : Spec (.of k) ⟶ projectiveLine k =>
    f (default : Spec (.of k))) (affineSection_normalChart k a z v)
  simpa only [Scheme.Hom.comp_apply, affineSection_base, finiteSection_base] using h

/-- The original affine origin maps to the same center for every nonzero coordinate scale. -/
@[simp]
theorem normalChart_origin (a : k) (v : kˣ) :
    normalChart k a v (affineLineOrigin k) = center k a := by
  simpa only [affineCenter_zero, mul_zero, add_zero] using normalChart_center k a 0 v

theorem center_eq_normalChart_origin (a : k) (v : kˣ) :
    center k a = normalChart k a v (affineLineOrigin k) := (normalChart_origin k a v).symm

@[simp]
theorem center_zero : center k 0 = projectiveLineZero k := by
  unfold center
  rw [affineCenter_zero]
  rfl

/-- These are actual closed-point sections over the field. -/
instance finiteSection_isClosedImmersion (a : k) : IsClosedImmersion (finiteSection k a) :=
  isClosedImmersion_of_comp_eq_id
    (projectiveLine k ↘ Spec (.of k)) (finiteSection k a) (finiteSection_over_base k a)

theorem finiteSection_range (a : k) :
    Set.range (finiteSection k a).base = {center k a} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact Set.mem_singleton_iff.mpr (finiteSection_base k a q)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨default, (finiteSection_base k a default).trans hx.symm⟩

/-- The center is an actual closed point of the original projective-line scheme. -/
theorem center_isClosed (a : k) : IsClosed ({center k a} : Set (projectiveLine k)) := by
  rw [← finiteSection_range]
  exact (finiteSection k a).isClosedEmbedding.isClosed_range

theorem center_ne_infinity (a : k) : center k a ≠ projectiveLineInfinity k := by
  intro h
  exact projectiveLineInfinity_notMem_range_XChart k ⟨affineCenter k a, h⟩

/-- Every finite center is nongeneric, with its actual nonzero evaluation-kernel polynomial. -/
theorem center_ne_genericPoint (a : k) : center k a ≠ genericPoint (projectiveLine k) := by
  intro h
  have hp : affineCenter k a = genericPoint (Spec (.of (Polynomial k))) :=
    projectiveLineXChart_base_injective
      (h.trans (projectiveLineXChart_genericPoint_eq (k := k)).symm)
  have hm : Polynomial.X - Polynomial.C a ∈ (affineCenter k a).asIdeal := by
    rw [affineCenter_asIdeal]
    exact Ideal.subset_span rfl
  rw [hp, genericPoint_eq_bot_of_affine] at hm
  exact Polynomial.X_sub_C_ne_zero a hm

end Field

end HodgeConjecture.ProjectiveLineAffineChart

end
