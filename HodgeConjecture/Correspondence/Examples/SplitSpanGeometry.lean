module

public import HodgeConjecture.Correspondence.Examples.SplitPointMaps
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

@[expose] public section

/-!
# Scheme realization of finite set spans

Functions of finite indexing sets induce morphisms of finite split schemes.
Consequently a finite set span has an actual finite étale scheme span, not
merely a formal matrix interpretation.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]
variable {S I J T U : Type u}

/-- Pullback of coefficient functions along a function of indexing sets. -/
def precompose (f : S → I) : (I → K) →ₐ[K] (S → K) where
  toFun a := a ∘ f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem precompose_apply (f : S → I) (a : I → K) (s : S) :
    precompose K f a s = a (f s) := rfl

/-- The morphism of split schemes induced by a function of indexing sets. -/
def mapOfFunction (f : S → I) : scheme K S ⟶ scheme K I :=
  Spec.map (CommRingCat.ofHom (precompose K f).toRingHom)

@[simp]
theorem mapOfFunction_id :
    mapOfFunction K (id : I → I) = 𝟙 (scheme K I) := by
  change Spec.map _ = _
  convert Spec.map_id (CommRingCat.of (I → K)) using 1 <;> first | rfl | congr 1; ext a i; rfl

@[simp, reassoc]
theorem mapOfFunction_comp (f : S → I) (g : I → J) :
    mapOfFunction K f ≫ mapOfFunction K g = mapOfFunction K (g ∘ f) := by
  unfold mapOfFunction
  rw [← Spec.map_comp]
  rfl

@[simp, reassoc]
theorem mapOfFunction_toBase (f : S → I) :
    mapOfFunction K f ≫ toBase K I = toBase K S := by
  unfold mapOfFunction toBase
  rw [← Spec.map_comp]
  rfl

@[simp, reassoc]
theorem pointInclusion_comp_mapOfFunction (f : S → I) (s : S) :
    pointInclusion K S s ≫ mapOfFunction K f = pointInclusion K I (f s) := by
  unfold pointInclusion mapOfFunction
  rw [← Spec.map_comp]
  rfl

@[reassoc]
theorem sigmaSpec_comp_mapOfFunction (f : S → I) :
    sigmaSpec (fun _ : S ↦ CommRingCat.of K) ≫ mapOfFunction K f =
      Sigma.desc (fun s : S ↦ pointInclusion K I (f s)) := by
  apply Sigma.hom_ext
  intro s
  simp only [ι_sigmaSpec_assoc, Sigma.ι_desc]
  exact pointInclusion_comp_mapOfFunction K f s

instance [Finite S] (f : S → I) : IsFinite (mapOfFunction K f) := by
  apply (IsFinite.SpecMap_iff _).2
  change (precompose K f).toRingHom.Finite
  letI : Algebra (I → K) (S → K) := (precompose K f).toRingHom.toAlgebra
  letI : IsScalarTower K (I → K) (S → K) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact Module.Finite.of_restrictScalars_finite K (I → K) (S → K)

instance [Finite S] (f : S → I) : Etale (mapOfFunction K f) := by
  apply (MorphismProperty.cancel_left_of_respectsIso @Etale
    (sigmaSpec (fun _ : S ↦ CommRingCat.of K)) (mapOfFunction K f)).mp
  rw [sigmaSpec_comp_mapOfFunction]
  exact IsZariskiLocalAtSource.sigmaDesc (fun s ↦
    inferInstanceAs (Etale (pointInclusion K I (f s))))

/-- The actual scheme span associated with its two indexing functions. -/
def span (left : S → I) (right : S → J) :
    SchemeCorrespondence (toBase K I) (toBase K J) where
  carrier := scheme K S
  left := mapOfFunction K left
  right := mapOfFunction K right
  over_base := by simp

theorem span_hasFiniteEtaleLegs [Finite S] (left : S → I) (right : S → J) :
    SchemeCorrespondence.HasFiniteEtaleLegs (span K left right) := by
  constructor
  · constructor
    · exact inferInstanceAs (Etale (mapOfFunction K left))
    · exact inferInstanceAs (Etale (mapOfFunction K right))
  · exact inferInstanceAs (IsFinite (mapOfFunction K left))
  · exact inferInstanceAs (IsFinite (mapOfFunction K right))

/-- Relabelling a split finite scheme gives a scheme isomorphism. -/
def isoOfEquiv (e : S ≃ I) : scheme K S ≅ scheme K I where
  hom := mapOfFunction K e
  inv := mapOfFunction K e.symm
  hom_inv_id := by
    rw [mapOfFunction_comp]
    convert mapOfFunction_id K using 2
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    rw [mapOfFunction_comp]
    convert mapOfFunction_id K using 2
    ext x
    exact e.apply_symm_apply x

/-- An equivalence of indexing spans gives an actual isomorphism of scheme spans. -/
def spanIsoOfEquiv (leftS : S → I) (rightS : S → J)
    (leftT : T → I) (rightT : T → J) (e : S ≃ T)
    (hleft : leftT ∘ e = leftS) (hright : rightT ∘ e = rightS) :
    SchemeCorrespondence.Isom (span K leftS rightS) (span K leftT rightT) where
  carrierIso := isoOfEquiv K e
  hom_left := by
    change mapOfFunction K e ≫ mapOfFunction K leftT = mapOfFunction K leftS
    rw [mapOfFunction_comp, hleft]
  hom_right := by
    change mapOfFunction K e ≫ mapOfFunction K rightT = mapOfFunction K rightS
    rw [mapOfFunction_comp, hright]

/-- The identity indexing span gives the identity scheme correspondence. -/
def span_identity_iso (I : Type u) :
    SchemeCorrespondence.Isom (span K (id : I → I) id)
      (SchemeCorrespondence.identity (toBase K I)) where
  carrierIso := Iso.refl _
  hom_left := by simp [span]
  hom_right := by simp [span]

/-- The one-point split scheme is canonically the base scheme. -/
def singletonIso : scheme K PUnit ≅ Spec (.of K) where
  hom := toBase K PUnit
  inv := pointInclusion K PUnit PUnit.unit
  hom_inv_id := by
    unfold toBase pointInclusion
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of (PUnit → K)) using 1
    · congr 1 <;> first | rfl | (ext a i; cases i; rfl)
    · rfl
  inv_hom_id := by
    unfold toBase pointInclusion
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of K) using 1
    congr 1 <;> first | rfl | (ext a; rfl)

/-- A singleton diagonal indexing span is the existing geometric point span. -/
def span_point_iso (I : Type u) (i : I) :
    SchemeCorrespondence.Isom
      (span K (fun _ : PUnit ↦ i) (fun _ : PUnit ↦ i)) (pointSpan K I i) where
  carrierIso := singletonIso K
  hom_left := by
    change toBase K PUnit ≫ pointInclusion K I i = mapOfFunction K (fun _ : PUnit ↦ i)
    unfold toBase pointInclusion mapOfFunction
    rw [← Spec.map_comp]
    rfl
  hom_right := by
    change toBase K PUnit ≫ pointInclusion K I i = mapOfFunction K (fun _ : PUnit ↦ i)
    unfold toBase pointInclusion mapOfFunction
    rw [← Spec.map_comp]
    rfl

/-- The indexing set of the set-theoretic fiber product. -/
def Fiber (f : S → I) (g : T → I) := {p : S × T // f p.1 = g p.2}

instance [Finite S] [Finite T] (f : S → I) (g : T → I) : Finite (Fiber f g) :=
  inferInstanceAs (Finite {p : S × T // f p.1 = g p.2})

@[simp]
theorem mapOfFunction_label [Finite S] [Finite I] (f : S → I) (s : S) :
    (mapOfFunction K f).base (labelEquivScheme K S s) =
      labelEquivScheme K I (f s) := rfl

/-- The comparison from the split scheme on the matching pairs to the scheme pullback. -/
def fiberComparison (f : S → I) (g : T → I) :
    scheme K (Fiber f g) ⟶ pullback (mapOfFunction K f) (mapOfFunction K g) :=
  pullback.lift (mapOfFunction K (fun p : Fiber f g ↦ p.val.1))
    (mapOfFunction K (fun p : Fiber f g ↦ p.val.2)) (by
      rw [mapOfFunction_comp, mapOfFunction_comp]
      congr 1
      funext p
      exact p.property)

@[simp, reassoc]
theorem fiberComparison_fst (f : S → I) (g : T → I) :
    fiberComparison K f g ≫ pullback.fst _ _ =
      mapOfFunction K (fun p : Fiber f g ↦ p.val.1) := by
  simp [fiberComparison]

@[simp, reassoc]
theorem fiberComparison_snd (f : S → I) (g : T → I) :
    fiberComparison K f g ≫ pullback.snd _ _ =
      mapOfFunction K (fun p : Fiber f g ↦ p.val.2) := by
  simp [fiberComparison]

private def fiberComponentMap (f : S → I) (g : T → I) (p : Fiber f g) :
    pullback (pointInclusion K I (f p.val.1)) (pointInclusion K I (f p.val.1)) ⟶
      pullback (mapOfFunction K f) (mapOfFunction K g) :=
  pullback.map _ _ _ _ (pointInclusion K S p.val.1) (pointInclusion K T p.val.2)
    (𝟙 _) (by simp) (by simp [p.property])

private instance (f : S → I) (g : T → I) (p : Fiber f g) :
    IsOpenImmersion (fiberComponentMap K f g p) := by
  apply MorphismProperty.pullbackMap (P := @IsOpenImmersion)
  · infer_instance
  · infer_instance
  · simp
  · simp [p.property]

private def fiberComponent (f : S → I) (g : T → I) (p : Fiber f g) :
    Spec (.of K) ⟶ pullback (mapOfFunction K f) (mapOfFunction K g) :=
  inv (pullback.fst (pointInclusion K I (f p.val.1)) (pointInclusion K I (f p.val.1))) ≫
    fiberComponentMap K f g p

private instance (f : S → I) (g : T → I) (p : Fiber f g) :
    IsOpenImmersion (fiberComponent K f g p) := by
  unfold fiberComponent
  infer_instance

@[simp, reassoc]
private theorem fiberComponent_fst (f : S → I) (g : T → I) (p : Fiber f g) :
    fiberComponent K f g p ≫ pullback.fst _ _ = pointInclusion K S p.val.1 := by
  simp [fiberComponent, fiberComponentMap]

@[simp, reassoc]
private theorem fiberComponent_snd (f : S → I) (g : T → I) (p : Fiber f g) :
    fiberComponent K f g p ≫ pullback.snd _ _ = pointInclusion K T p.val.2 := by
  simp [fiberComponent, fiberComponentMap, ← fst_eq_snd_of_mono_eq]

private theorem pointInclusion_fiberComparison (f : S → I) (g : T → I) (p : Fiber f g) :
    pointInclusion K (Fiber f g) p ≫ fiberComparison K f g = fiberComponent K f g p := by
  apply pullback.hom_ext <;> simp

private theorem sigmaSpec_fiberComparison (f : S → I) (g : T → I) :
    sigmaSpec (fun _ : Fiber f g ↦ CommRingCat.of K) ≫ fiberComparison K f g =
      Sigma.desc (fiberComponent K f g) := by
  apply Sigma.hom_ext
  intro p
  simp only [ι_sigmaSpec_assoc, Sigma.ι_desc]
  exact pointInclusion_fiberComparison K f g p

private theorem fiberComponent_range (f : S → I) (g : T → I) (p : Fiber f g) :
    Set.range (fiberComponent K f g p).base =
      (pullback.fst (mapOfFunction K f) (mapOfFunction K g)).base ⁻¹'
        Set.range (pointInclusion K S p.val.1).base ∩
      (pullback.snd (mapOfFunction K f) (mapOfFunction K g)).base ⁻¹'
        Set.range (pointInclusion K T p.val.2).base := by
  rw [fiberComponent, Scheme.Hom.comp_base]
  change Set.range ((fiberComponentMap K f g p).base ∘
    (inv (pullback.fst (pointInclusion K I (f p.val.1))
      (pointInclusion K I (f p.val.1)))).base) = _
  rw [Function.Surjective.range_comp
    (ConcreteCategory.bijective_of_isIso
      (inv (pullback.fst (pointInclusion K I (f p.val.1))
        (pointInclusion K I (f p.val.1)))).base).2]
  exact Scheme.Pullback.range_map
    (pointInclusion K I (f p.val.1)) (pointInclusion K I (f p.val.1))
    (mapOfFunction K f) (mapOfFunction K g)
    (pointInclusion K S p.val.1) (pointInclusion K T p.val.2) (𝟙 _)
    (by simp) (by simp [p.property])

private theorem pointInclusion_base [Finite I] (i : I) (x : Spec (.of K)) :
    (pointInclusion K I i).base x = labelEquivScheme K I i := by
  rw [labelEquivScheme_apply]
  congr 1
  exact Subsingleton.elim _ _

private theorem fiberComponent_disjoint [Finite S] [Finite T] (f : S → I) (g : T → I) :
    Pairwise (fun p q : Fiber f g ↦
      Disjoint (Set.range (fiberComponent K f g p).base)
        (Set.range (fiberComponent K f g q).base)) := by
  intro p q hpq
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  apply hpq
  apply Subtype.ext
  apply Prod.ext
  · apply (labelEquivScheme K S).injective
    have h' := congrArg (pullback.fst (mapOfFunction K f) (mapOfFunction K g)).base h
    simpa only [← Scheme.Hom.comp_apply, fiberComponent_fst, pointInclusion_base] using h'
  · apply (labelEquivScheme K T).injective
    have h' := congrArg (pullback.snd (mapOfFunction K f) (mapOfFunction K g)).base h
    simpa only [← Scheme.Hom.comp_apply, fiberComponent_snd, pointInclusion_base] using h'

private theorem fiberComponent_covers [Finite S] [Finite T] [Finite I]
    (f : S → I) (g : T → I)
    (z : (pullback (mapOfFunction K f) (mapOfFunction K g) : Scheme)) :
    ∃ p : Fiber f g, z ∈ Set.range (fiberComponent K f g p).base := by
  let s := (labelEquivScheme K S).symm
    ((pullback.fst (mapOfFunction K f) (mapOfFunction K g)).base z)
  let t := (labelEquivScheme K T).symm
    ((pullback.snd (mapOfFunction K f) (mapOfFunction K g)).base z)
  have hst : f s = g t := by
    apply (labelEquivScheme K I).injective
    rw [← mapOfFunction_label K f, ← mapOfFunction_label K g]
    simp only [s, t, Equiv.apply_symm_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  refine ⟨⟨(s, t), hst⟩, ?_⟩
  rw [fiberComponent_range]
  constructor
  · refine ⟨default, ?_⟩
    change (pointInclusion K S s) _ = _
    rw [show (default : Spec (.of K)) = (default : PrimeSpectrum K) from Subsingleton.elim _ _]
    change labelEquivScheme K S s = _
    exact (labelEquivScheme K S).apply_symm_apply _
  · refine ⟨default, ?_⟩
    change (pointInclusion K T t) _ = _
    rw [show (default : Spec (.of K)) = (default : PrimeSpectrum K) from Subsingleton.elim _ _]
    change labelEquivScheme K T t = _
    exact (labelEquivScheme K T).apply_symm_apply _

private instance [Finite S] [Finite T] (f : S → I) (g : T → I) :
    IsOpenImmersion (Sigma.desc (fiberComponent K f g)) :=
  isOpenImmersion_sigmaDesc _ _ (fiberComponent_disjoint K f g)

private instance [Finite S] [Finite T] [Finite I] (f : S → I) (g : T → I) :
    IsIso (Sigma.desc (fiberComponent K f g)) := by
  apply (isIso_iff_isOpenImmersion_and_epi_base _).2
  constructor
  · infer_instance
  · apply (TopCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨p, x, hx⟩ := fiberComponent_covers K f g z
    refine ⟨(Sigma.ι (fun _ : Fiber f g ↦ Spec (.of K)) p).base x, ?_⟩
    simpa only [← Scheme.Hom.comp_apply, Sigma.ι_desc] using hx

/-- The set-theoretic matching-pair construction computes the actual scheme pullback. -/
instance [Finite S] [Finite T] [Finite I] (f : S → I) (g : T → I) :
    IsIso (fiberComparison K f g) := by
  have h : IsIso (sigmaSpec (fun _ : Fiber f g ↦ CommRingCat.of K) ≫
      fiberComparison K f g) := by
    rw [sigmaSpec_fiberComparison]
    infer_instance
  exact IsIso.of_isIso_comp_left (sigmaSpec (fun _ : Fiber f g ↦ CommRingCat.of K)) _

/-- The canonical isomorphism between the split matching-pair scheme and the pullback. -/
def fiberIso [Finite S] [Finite T] [Finite I] (f : S → I) (g : T → I) :
    scheme K (Fiber f g) ≅ pullback (mapOfFunction K f) (mapOfFunction K g) :=
  asIso (fiberComparison K f g)

/-- Composition of actual split scheme spans is their finite matching-pair span. -/
def span_comp_iso [Finite S] [Finite T] [Finite J]
    (leftS : S → I) (rightS : S → J) (leftT : T → J) (rightT : T → U) :
    SchemeCorrespondence.Isom
      ((span K leftT rightT).comp (span K leftS rightS))
      (span K (fun p : Fiber rightS leftT ↦ leftS p.val.1)
        (fun p : Fiber rightS leftT ↦ rightT p.val.2)) where
  carrierIso := (fiberIso K rightS leftT).symm
  hom_left := by
    apply (cancel_epi (fiberComparison K rightS leftT)).1
    simp [span, fiberIso, fiberComparison_fst_assoc, Function.comp_def]
  hom_right := by
    apply (cancel_epi (fiberComparison K rightS leftT)).1
    simp [span, fiberIso, fiberComparison_snd_assoc, Function.comp_def]

end SplitPointGeometry

end

end HodgeConjecture
