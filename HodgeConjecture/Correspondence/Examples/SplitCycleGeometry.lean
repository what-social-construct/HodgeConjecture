import HodgeConjecture.Correspondence.Examples.SplitIntegralSubschemes
import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Images of actual integral subschemes under split-scheme maps

The image operation uses the pushforward of the actual ideal-sheaf data.
On reduced rational point components its label is the image label. The
canonical morphism onto that scheme-theoretic image is an isomorphism,
providing the geometric degree-one input for zero-cycle pushforward.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]
variable {S I J : Type u} [Finite S] [Finite I] [Finite J]

omit [Finite S] [Finite I] in
/-- Scheme-theoretic image takes a point's ideal sheaf to its image point. -/
@[simp]
theorem pointIdealSheaf_map (f : S → I) (s : S) :
    (pointIdealSheaf K S s).map (mapOfFunction K f) =
      pointIdealSheaf K I (f s) := by
  simp only [pointIdealSheaf, Scheme.IdealSheafData.map_ker,
    pointInclusion_comp_mapOfFunction]

/-- The actual scheme-theoretic image of an integral closed subscheme. -/
def imageIntegralSubscheme (f : S → I) (W : IntegralClosedSubscheme K S) :
    IntegralClosedSubscheme K I :=
  ⟨W.val.map (mapOfFunction K f), by
    obtain ⟨s, hs⟩ := exists_pointIdealSheaf K S W
    rw [hs, pointIdealSheaf_map]
    exact pointIdealSheaf_isIntegral K I (f s)⟩

omit [Finite I] in
@[simp]
theorem imageIntegralSubscheme_val (f : S → I) (W : IntegralClosedSubscheme K S) :
    (imageIntegralSubscheme K f W).val = W.val.map (mapOfFunction K f) := rfl

omit [Finite I] in
@[simp]
theorem imageIntegralSubscheme_point (f : S → I) (s : S) :
    imageIntegralSubscheme K f (pointIntegralSubscheme K S s) =
      pointIntegralSubscheme K I (f s) := by
  apply Subtype.ext
  exact pointIdealSheaf_map K f s

@[simp]
theorem imageIntegralSubscheme_id (W : IntegralClosedSubscheme K S) :
    imageIntegralSubscheme K (id : S → S) W = W := by
  apply Subtype.ext
  simp

omit [Finite J] in
@[simp]
theorem imageIntegralSubscheme_comp (f : S → I) (g : I → J)
    (W : IntegralClosedSubscheme K S) :
    imageIntegralSubscheme K (g ∘ f) W =
      imageIntegralSubscheme K g (imageIntegralSubscheme K f W) := by
  apply Subtype.ext
  simp only [imageIntegralSubscheme_val, ← mapOfFunction_comp,
    Scheme.IdealSheafData.map_comp]

/-- Each integral component maps to the ambient target by a closed immersion. -/
instance integralSubscheme_comp_mapOfFunction_isClosedImmersion
    (f : S → I) (W : IntegralClosedSubscheme K S) :
    IsClosedImmersion (W.val.subschemeι ≫ mapOfFunction K f) := by
  letI := W.property
  obtain ⟨s, ⟨e, he⟩, _⟩ :=
    existsUnique_pointIso_of_isIntegral K S W.val.subschemeι
  rw [← he, Category.assoc, pointInclusion_comp_mapOfFunction]
  infer_instance

/-- The canonical morphism from the integral subscheme to its actual image. -/
def imageIntegralSubschemeMap (f : S → I) (W : IntegralClosedSubscheme K S) :
    W.val.subscheme ⟶ (imageIntegralSubscheme K f W).val.subscheme :=
  (W.val.subschemeι ≫ mapOfFunction K f).toImage

omit [Finite I] in
@[reassoc (attr := simp)]
theorem imageIntegralSubschemeMap_subschemeι
    (f : S → I) (W : IntegralClosedSubscheme K S) :
    imageIntegralSubschemeMap K f W ≫ (imageIntegralSubscheme K f W).val.subschemeι =
      W.val.subschemeι ≫ mapOfFunction K f :=
  (W.val.subschemeι ≫ mapOfFunction K f).toImage_imageι

omit [Finite I] in
/-- The canonical image morphism is the existing restricted subscheme map. -/
theorem imageIntegralSubschemeMap_eq_subschemeMap
    (f : S → I) (W : IntegralClosedSubscheme K S) :
    imageIntegralSubschemeMap K f W =
      W.val.subschemeMap (imageIntegralSubscheme K f W).val (mapOfFunction K f)
        (by rfl) := by
  rw [← cancel_mono (imageIntegralSubscheme K f W).val.subschemeι]
  rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
  exact imageIntegralSubschemeMap_subschemeι K f W

instance imageIntegralSubschemeMap_isIso
    (f : S → I) (W : IntegralClosedSubscheme K S) :
    IsIso (imageIntegralSubschemeMap K f W) := by
  unfold imageIntegralSubschemeMap
  infer_instance

/-- An integral component and its scheme-theoretic image are isomorphic. -/
def imageIntegralSubschemeIso (f : S → I) (W : IntegralClosedSubscheme K S) :
    W.val.subscheme ≅ (imageIntegralSubscheme K f W).val.subscheme :=
  asIso (imageIntegralSubschemeMap K f W)

omit [Finite I] in
@[reassoc (attr := simp)]
theorem imageIntegralSubschemeIso_hom_subschemeι
    (f : S → I) (W : IntegralClosedSubscheme K S) :
    (imageIntegralSubschemeIso K f W).hom ≫
        (imageIntegralSubscheme K f W).val.subschemeι =
      W.val.subschemeι ≫ mapOfFunction K f :=
  imageIntegralSubschemeMap_subschemeι K f W

end SplitPointGeometry

end

end HodgeConjecture
