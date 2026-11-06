module

public import HodgeConjecture.Realization.DeRham.SheafHypercohomology
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.Splitting
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

/-!
# The actual derived triangle of a two-term nonnegative complex

The degree-one inclusion and degree-zero projection form an actual
degreewise split short exact sequence. After extension by zero its
distinguished triangle is retained in the bounded-below derived category.
All connecting maps come from that short exact sequence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex
open scoped ZeroObject

namespace HodgeConjecture.TwoTermComplex

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))

/-- The actual degree-one term placed in degree one. -/
abbrev degreeOne : CochainComplex C ℕ :=
  (HomologicalComplex.single C (.up ℕ) 1).obj (K.X 1)

/-- The actual degree-zero term placed in degree zero. -/
abbrev degreeZero : CochainComplex C ℕ := (CochainComplex.single₀ C).obj (K.X 0)

/-- Inclusion of the actual final nonzero term into the original complex. -/
def inclusion : degreeOne K ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 (K.X 1)) (fun n hn ↦ by
    change 1 + 1 = n at hn
    subst n
    exact (hK 2 (by decide)).eq_of_tgt _ _)

/-- Projection of the original complex onto its actual degree-zero term. -/
def projection : K ⟶ degreeZero K :=
  (CochainComplex.toSingle₀Equiv K (K.X 0)).symm (𝟙 _)

/-- The concrete two-term filtration of the original complex. -/
def shortComplex : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (inclusion K hK) (projection K) (by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      exact (isZero_single_obj_X (.up ℕ) 1 (K.X 1) 0 (by decide)).eq_of_src _ _
    · exact (isZero_single_obj_X (.up ℕ) 0 (K.X 0) n hn).eq_of_tgt _ _)

/-- The filtration splits on each degree, without choosing a splitting of the complex. -/
def degreewiseSplitting (n : ℕ) :
    ((shortComplex K hK).map (HomologicalComplex.eval C (.up ℕ) n)).Splitting := by
  rcases n with _ | n
  · apply ShortComplex.Splitting.ofIsZeroOfIsIso
    · exact isZero_single_obj_X (.up ℕ) 1 (K.X 1) 0 (by decide)
    · change IsIso ((projection K).f 0)
      rw [projection, CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
      infer_instance
  rcases n with _ | n
  · apply ShortComplex.Splitting.ofIsIsoOfIsZero
    · change IsIso ((inclusion K hK).f 1)
      rw [inclusion, HomologicalComplex.mkHomFromSingle_f]
      simp only [Category.comp_id]
      infer_instance
    · exact isZero_single_obj_X (.up ℕ) 0 (K.X 0) 1 (by decide)
  · apply ShortComplex.Splitting.ofIsZero
    · exact isZero_single_obj_X (.up ℕ) 1 (K.X 1) (n + 2) (by omega)
    · exact hK (n + 2) (by omega)
    · exact isZero_single_obj_X (.up ℕ) 0 (K.X 0) (n + 2) (by omega)

/-- The original filtration is short exact. -/
theorem shortComplex_shortExact : (shortComplex K hK).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n ↦ (degreewiseSplitting K hK n).shortExact)

/-- Its actual extension by zero, used by bounded-below derived global sections. -/
def extendedShortComplex : ShortComplex (CochainComplex C ℤ) :=
  (shortComplex K hK).map ((ComplexShape.embeddingUpIntGE 0).extendFunctor C)

theorem extendedShortComplex_shortExact : (extendedShortComplex K hK).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n ↦
    ((ComplexShape.embeddingUpIntGE 0).splittingExtend (degreewiseSplitting K hK) n).shortExact)

variable [HasDerivedCategory C]

def inclusionPlus :
    BoundedBelowDerived.nonnegativePlus (degreeOne K) ⟶
      BoundedBelowDerived.nonnegativePlus K :=
  ObjectProperty.homMk
    (HomologicalComplex.extendMap (inclusion K hK) (ComplexShape.embeddingUpIntGE 0))

def projectionPlus :
    BoundedBelowDerived.nonnegativePlus K ⟶
      BoundedBelowDerived.nonnegativePlus (degreeZero K) :=
  ObjectProperty.homMk
    (HomologicalComplex.extendMap (projection K) (ComplexShape.embeddingUpIntGE 0))

/-- The actual distinguished two-term triangle, retained in the bounded-below category. -/
def triangle : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk
    (DerivedCategory.Plus.Q.map (inclusionPlus K hK))
    (DerivedCategory.Plus.Q.map (projectionPlus K))
    ((DerivedCategory.Plus.ι (C := C)).preimage
      (DerivedCategory.triangleOfSESδ (extendedShortComplex_shortExact K hK) ≫
        ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
          (DerivedCategory.Plus.Q.obj
            (BoundedBelowDerived.nonnegativePlus (degreeOne K)))))

set_option backward.isDefEq.respectTransparency false in
theorem triangle_distinguished : triangle K hK ∈ distTriang (DerivedCategory.Plus C) := by
  change (DerivedCategory.Plus.ι (C := C)).mapTriangle.obj (triangle K hK) ∈
    distTriang (DerivedCategory C)
  apply isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (extendedShortComplex_shortExact K hK)) _
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  all_goals simp [triangle, DerivedCategory.triangleOfSES, extendedShortComplex,
    DerivedCategory.Plus.Q, inclusionPlus, projectionPlus, Functor.mapTriangle, shortComplex]
  change (DerivedCategory.Plus.ι (C := C)).map
    ((DerivedCategory.Plus.ι (C := C)).preimage _) ≫ _ = _
  rw [Functor.map_preimage]
  simp
  change DerivedCategory.triangleOfSESδ (extendedShortComplex_shortExact K hK) ≫ 𝟙 _ = _
  exact Category.comp_id _

end

end HodgeConjecture.TwoTermComplex

namespace HodgeConjecture.BoundedBelowDerived

noncomputable section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/-- Extend a nonnegative complex starting in the specified integer degree. -/
def nonnegativePlusAt (p : ℤ) (K : CochainComplex C ℕ) : CochainComplex.Plus C :=
  ⟨K.extend (ComplexShape.embeddingUpIntGE p), ⟨p, inferInstance⟩⟩

/-- The same actual injective resolution computes a sheaf placed in any integer degree. -/
def injectiveResolutionDerivedIsoAt (M : C) (I : InjectiveResolution M) (p : ℤ) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
        (nonnegativePlusAt p ((CochainComplex.single₀ C).obj M))) ≅
      DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj (nonnegativePlusAt p I.cocomplex)) := by
  let i : nonnegativePlusAt p ((CochainComplex.single₀ C).obj M) ⟶
      nonnegativePlusAt p I.cocomplex :=
    ObjectProperty.homMk (HomologicalComplex.extendMap I.ι (ComplexShape.embeddingUpIntGE p))
  have hi : CochainComplex.Plus.quasiIso C i := by
    change QuasiIso (HomologicalComplex.extendMap I.ι (ComplexShape.embeddingUpIntGE p))
    infer_instance
  haveI : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) i hi
  haveI (n : ℤ) : Injective ((nonnegativePlusAt p I.cocomplex).obj.X n) := by
    change Injective ((I.cocomplex.extend (ComplexShape.embeddingUpIntGE p)).X n)
    infer_instance
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app (nonnegativePlusAt p I.cocomplex)) :=
    isIso_unit_of_injectiveTerms F (nonnegativePlusAt p I.cocomplex)
  exact F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map i)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (nonnegativePlusAt p I.cocomplex))).symm

/-- Ordinary right derived cohomology of a single object in its actual integer degree. -/
def singleAtHypercohomologyIsoRightDerived (M : C) (I : InjectiveResolution M)
    (p : ℤ) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D (p + n)).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (nonnegativePlusAt p ((CochainComplex.single₀ C).obj M)))) ≅
      (F.rightDerived n).obj M :=
  (DerivedCategory.Plus.homologyFunctor D (p + n)).mapIso
      (injectiveResolutionDerivedIsoAt F M I p) ≪≫
    (DerivedCategory.homologyFunctorFactors D (p + n)).app
      (F.mapCochainComplexPlus.obj (nonnegativePlusAt p I.cocomplex)).obj ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) (p + n)).mapIso
      (mapExtendIso F I.cocomplex (ComplexShape.embeddingUpIntGE p)) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      (ComplexShape.embeddingUpIntGE p) (by simp) ≪≫
    (I.isoRightDerivedObj F n).symm

/-- The actual singleton in nonnegative degree one agrees with extension starting at one. -/
def nonnegativeDegreeOneIso (M : C) :
    nonnegativePlus ((HomologicalComplex.single C (.up ℕ) 1).obj M) ≅
      nonnegativePlusAt 1 ((CochainComplex.single₀ C).obj M) :=
  ObjectProperty.isoMk _
    (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0) M 1 1 (by simp) ≪≫
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 1) M 0 1 (by simp)).symm)

/-- The actual degree-two derived cohomology of the singleton in degree one is `R¹ F`. -/
def degreeOneHypercohomologyIsoRightDerived (M : C) :
    (DerivedCategory.Plus.homologyFunctor D 2).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj
          (nonnegativePlus ((HomologicalComplex.single C (.up ℕ) 1).obj M)))) ≅
      (F.rightDerived 1).obj M :=
  (DerivedCategory.Plus.homologyFunctor D 2).mapIso
      (F.rightDerivedFunctorPlus.mapIso
        (DerivedCategory.Plus.Q.mapIso (nonnegativeDegreeOneIso M))) ≪≫
    singleAtHypercohomologyIsoRightDerived F M (injectiveResolution M) 1 1

/-- The actual degree-one inclusion induces an isomorphism in hypercohomology
when the adjacent derived cohomology of the degree-zero term vanishes. -/
theorem twoTermInclusion_isIso
    (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))
    (h₁ : IsZero ((F.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((F.rightDerived 2).obj (K.X 0))) :
    IsIso (((F.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.homologyFunctor D 2).map
      (DerivedCategory.Plus.Q.map (TwoTermComplex.inclusionPlus K hK))) := by
  let T := TwoTermComplex.triangle K hK
  have hT := TwoTermComplex.triangle_distinguished K hK
  let H := F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D 0
  have hz₁ : IsZero ((H.shift (1 : ℤ)).obj T.obj₃) :=
    h₁.of_iso (singleHypercohomologyIsoRightDerived F (K.X 0)
      (injectiveResolution (K.X 0)) 1)
  have hz₂ : IsZero ((H.shift (2 : ℤ)).obj T.obj₃) :=
    h₂.of_iso (singleHypercohomologyIsoRightDerived F (K.X 0)
      (injectiveResolution (K.X 0)) 2)
  have : Mono ((H.shift (2 : ℤ)).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T hT 1 2 rfl).mpr (hz₁.eq_of_src _ _)
  have : Epi ((H.shift (2 : ℤ)).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T hT 2).mpr (hz₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift (2 : ℤ)).map T.mor₁)

/-- The actual two-term comparison is the inverse of the derived inclusion,
followed by the ordinary injective-resolution identification. -/
def twoTermHypercohomologyIsoRightDerived
    (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))
    (h₁ : IsZero ((F.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((F.rightDerived 2).obj (K.X 0))) :
    (DerivedCategory.Plus.homologyFunctor D 2).obj
        (F.rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (nonnegativePlus K))) ≅
      (F.rightDerived 1).obj (K.X 1) := by
  haveI := twoTermInclusion_isIso F K hK h₁ h₂
  exact (asIso (((F.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.homologyFunctor D 2).map
      (DerivedCategory.Plus.Q.map (TwoTermComplex.inclusionPlus K hK)))).symm ≪≫
    degreeOneHypercohomologyIsoRightDerived F (K.X 1)

/-- The comparison is fixed by the original inclusion of the degree-one term. -/
@[reassoc]
theorem twoTermHypercohomologyIsoRightDerived_inclusion
    (K : CochainComplex C ℕ) (hK : ∀ n : ℕ, 2 ≤ n → IsZero (K.X n))
    (h₁ : IsZero ((F.rightDerived 1).obj (K.X 0)))
    (h₂ : IsZero ((F.rightDerived 2).obj (K.X 0))) :
    (((F.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.homologyFunctor D 2).map
        (DerivedCategory.Plus.Q.map (TwoTermComplex.inclusionPlus K hK))) ≫
        (twoTermHypercohomologyIsoRightDerived F K hK h₁ h₂).hom =
      (degreeOneHypercohomologyIsoRightDerived F (K.X 1)).hom := by
  have := twoTermInclusion_isIso F K hK h₁ h₂
  simp [twoTermHypercohomologyIsoRightDerived]

end

end HodgeConjecture.BoundedBelowDerived
