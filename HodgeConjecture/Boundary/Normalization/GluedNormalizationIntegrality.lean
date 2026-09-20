import HodgeConjecture.Boundary.Normalization.GluedNormalizationNormality

/-!
# Integrality of the original glued normalization

The original affine normalization charts are integral. Any two meet through
a nonempty affine refinement of their base opens. Their irreducible open
images therefore give an irreducible global space. The already proved
domain stalks give reducedness, hence integrality of the same glued scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance normalizationIntegralityAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance normalizationIntegralityChart (U : NonemptyAffineChart X) :
    IsIntegral ((affineNormalizationDiagram X N).obj U) := by
  change IsIntegral (normalizedAffineModel Γ(X, U.val) N)
  unfold normalizedAffineModel
  infer_instance

/-- Any two original chart images meet through a nonempty common refinement. -/
theorem normalizationChartToGlued_range_inter_nonempty
    (U V : NonemptyAffineChart X) :
    (Set.range (normalizationChartToGlued X N U).base ∩
      Set.range (normalizationChartToGlued X N V).base).Nonempty := by
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.val.isOpen V.val.isOpen
    (Set.nonempty_coe_sort.mp U.property.2) (Set.nonempty_coe_sort.mp V.property.2)
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter
    U.property.1 V.property.1 x ⟨hxU, hxV⟩
  let W : NonemptyAffineChart X :=
    ⟨X.basicOpen r, U.property.1.basicOpen r, ⟨⟨x, hxr⟩⟩⟩
  let f : W ⟶ U := homOfLE (X.basicOpen_le r)
  let g : W ⟶ V := homOfLE (hrs.trans_le (X.basicOpen_le s))
  obtain ⟨w⟩ := (inferInstance : Nonempty ((affineNormalizationDiagram X N).obj W))
  refine ⟨(normalizationChartToGlued X N W).base w, ?_, ?_⟩
  · refine ⟨((affineNormalizationDiagram X N).map f).base w, ?_⟩
    rw [← Scheme.comp_base_apply, normalizationChartToGlued_naturality]
  · refine ⟨((affineNormalizationDiagram X N).map g).base w, ?_⟩
    rw [← Scheme.comp_base_apply, normalizationChartToGlued_naturality]

/-- The proved domain stalks make the original glued scheme reduced. -/
theorem gluedNormalizationModel_isReduced : IsReduced (gluedNormalizationModel X N) := by
  letI (z : gluedNormalizationModel X N) :
      IsDomain ((gluedNormalizationModel X N).presheaf.stalk z) :=
    gluedNormalizationModel_stalk_isDomain X N z
  exact isReduced_of_isReduced_stalk _

/-- The overlapping original integral charts make the global space irreducible. -/
theorem gluedNormalizationModel_irreducibleSpace :
    IrreducibleSpace (gluedNormalizationModel X N) := by
  have hchart (U : NonemptyAffineChart X) :
      IsIrreducible (Set.range (normalizationChartToGlued X N U).base) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ ((affineNormalizationDiagram X N).obj U)).image
        (normalizationChartToGlued X N U).base
        (normalizationChartToGlued X N U).continuous.continuousOn
  apply (irreducibleSpace_def _).mpr
  constructor
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨U, hU, hx, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by trivial)
    obtain ⟨z, _⟩ := (hchart ⟨U, hU, ⟨⟨x, hx⟩⟩⟩).nonempty
    exact ⟨z, trivial⟩
  · intro A B hA hB hAnonempty hBnonempty
    obtain ⟨a, _, ha⟩ := hAnonempty
    obtain ⟨b, _, hb⟩ := hBnonempty
    obtain ⟨U, aU, rfl⟩ := (gluedNormalizationOpenCover X N).exists_eq a
    obtain ⟨V, bV, rfl⟩ := (gluedNormalizationOpenCover X N).exists_eq b
    obtain ⟨c, hcU, hcA, hcV⟩ := (hchart U).isPreirreducible A
      (Set.range (normalizationChartToGlued X N V).base) hA
      (normalizationChartToGlued X N V).isOpenEmbedding.isOpen_range
      ⟨_, ⟨aU, rfl⟩, ha⟩ (normalizationChartToGlued_range_inter_nonempty X N U V)
    obtain ⟨d, _, hdA, hdB⟩ := (hchart V).isPreirreducible A B hA hB
      ⟨c, hcV, hcA⟩ ⟨_, ⟨bV, rfl⟩, hb⟩
    exact ⟨d, trivial, hdA, hdB⟩

/-- The original glued normalization is integral for every ambient field extension. -/
instance gluedNormalizationModel_isIntegral : IsIntegral (gluedNormalizationModel X N) := by
  letI := gluedNormalizationModel_isReduced X N
  letI := gluedNormalizationModel_irreducibleSpace X N
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end HodgeConjecture.CollisionFoundations
