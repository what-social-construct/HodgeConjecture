module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section

/-!
# Cochains on a union of actual simplicial subcomplexes

Rational functions on a simplicial set form its actual alternating coface
complex. For two subcomplexes, restriction and restriction difference give
a short exact sequence of cochain complexes on their union, the two pieces
and their intersection. Its connecting morphism and long exact sequence
are therefore constructed without an excision hypothesis.

For singular simplices this union is the small singular complex. Its
comparison with full singular cochains of a topological open cover is
provided separately by actual subdivision and exact rational dualization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SubcomplexCochains

open CategoryTheory Simplicial Opposite

universe u

/-- Rational functions on the actual simplices in degree `n`. -/
abbrev Cochain (S : SSet.{u}) (n : ℕ) := S.obj (op ⦋n⦌) → ℚ

/-- Actual rational cochains on an arbitrary simplicial set. -/
def cosimplicial (S : SSet.{u}) : CosimplicialObject (ModuleCat.{u} ℚ) :=
  S.rightOp ⋙ SingularCochains.functionModule

/-- The alternating coface complex of actual rational functions. -/
def complex (S : SSet.{u}) : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cosimplicial S)

/-- The alternating differential as an actual linear map on functions. -/
def differential (S : SSet.{u}) (n : ℕ) : Cochain S n →ₗ[ℚ] Cochain S (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimplicial S) n).hom

@[simp]
theorem complex_d (S : SSet.{u}) (n : ℕ) :
    (complex S).d n (n + 1) = ModuleCat.ofHom (differential S n) := by
  simp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rfl

theorem differential_squared (S : SSet.{u}) (n : ℕ) (φ : Cochain S n) :
    differential S (n + 1) (differential S n φ) = 0 :=
  congrArg (fun f ↦ f.hom φ)
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cosimplicial S) n)

/-- Precomposition along an actual simplicial map. -/
def pullback {S T : SSet.{u}} (f : S ⟶ T) : complex T ⟶ complex S :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).map
    (Functor.whiskerRight f.rightOp SingularCochains.functionModule)

@[simp]
theorem pullback_apply {S T : SSet.{u}} (f : S ⟶ T) (n : ℕ)
    (φ : Cochain T n) (σ : S.obj (op ⦋n⦌)) :
    (pullback f).f n φ σ = φ (f.app (op ⦋n⦌) σ) := rfl

@[simp]
theorem pullback_comp {S T U : SSet.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    pullback (f ≫ g) = pullback g ≫ pullback f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

/-- This construction specializes to the existing full singular cochain complex. -/
def singularComplexIso (X : TopCat.{u}) :
    complex (TopCat.toSSet.obj X) ≅ SingularCochains.complex X := Iso.refl _

/-- Simplicial pullback specializes to the original continuous singular pullback. -/
theorem singular_pullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    pullback (TopCat.toSSet.map f) = SingularCochains.pullback f := rfl

variable {S : SSet.{u}}

/-- Restriction to an actual simplicial subcomplex. -/
def restriction {A B : S.Subcomplex} (h : A ≤ B) : complex (B : SSet) ⟶ complex (A : SSet) :=
  pullback (SSet.Subcomplex.homOfLE h)

@[simp]
theorem restriction_apply {A B : S.Subcomplex} (h : A ≤ B) (n : ℕ)
    (φ : Cochain (B : SSet) n) (σ : A.obj (op ⦋n⦌)) :
    (restriction h).f n φ σ = φ ⟨σ.val, h _ σ.property⟩ := rfl

/-- The two actual chart cochains in one degree. -/
abbrev PairCochain (A B : S.Subcomplex) (n : ℕ) :=
  Cochain (A : SSet) n × Cochain (B : SSet) n

/-- Componentwise alternating differential on the two pieces. -/
def pairDifferential (A B : S.Subcomplex) (n : ℕ) :
    PairCochain A B n →ₗ[ℚ] PairCochain A B (n + 1) :=
  (differential (A : SSet) n).prodMap (differential (B : SSet) n)

theorem pairDifferential_squared (A B : S.Subcomplex) (n : ℕ) :
    pairDifferential A B (n + 1) ∘ₗ pairDifferential A B n = 0 := by
  apply LinearMap.ext
  intro φ
  exact Prod.ext (differential_squared (A : SSet) n φ.1)
    (differential_squared (B : SSet) n φ.2)

/-- The actual componentwise cochain complex of the two pieces. -/
def pairComplex (A B : S.Subcomplex) : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℚ (PairCochain A B n))
    (fun n ↦ ModuleCat.ofHom (pairDifferential A B n))
    (fun n ↦ ModuleCat.hom_ext (pairDifferential_squared A B n))

@[simp]
theorem pairComplex_d (A B : S.Subcomplex) (n : ℕ) :
    (pairComplex A B).d n (n + 1) = ModuleCat.ofHom (pairDifferential A B n) :=
  CochainComplex.of_d (fun n ↦ ModuleCat.of ℚ (PairCochain A B n))
    (fun n ↦ ModuleCat.ofHom (pairDifferential A B n)) n

/-- Restrict a cochain on the actual union to both pieces. -/
def coverRestrictionLinear (A B : S.Subcomplex) (n : ℕ) :
    Cochain ((A ⊔ B : S.Subcomplex) : SSet) n →ₗ[ℚ] PairCochain A B n where
  toFun φ :=
    (fun σ ↦ φ ⟨σ.val, Or.inl σ.property⟩, fun σ ↦ φ ⟨σ.val, Or.inr σ.property⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction difference on the actual intersection, with the order first minus second. -/
def coverDifferenceLinear (A B : S.Subcomplex) (n : ℕ) :
    PairCochain A B n →ₗ[ℚ] Cochain ((A ⊓ B : S.Subcomplex) : SSet) n where
  toFun φ σ := φ.1 ⟨σ.val, σ.property.1⟩ - φ.2 ⟨σ.val, σ.property.2⟩
  map_add' φ ψ := by funext σ; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; abel
  map_smul' a φ := by funext σ; simp [mul_sub]

@[simp]
theorem coverRestrictionLinear_apply (A B : S.Subcomplex) (n : ℕ)
    (φ : Cochain ((A ⊔ B : S.Subcomplex) : SSet) n) :
    coverRestrictionLinear A B n φ =
      (fun σ ↦ φ ⟨σ.val, Or.inl σ.property⟩, fun σ ↦ φ ⟨σ.val, Or.inr σ.property⟩) := rfl

@[simp]
theorem coverDifferenceLinear_apply (A B : S.Subcomplex) (n : ℕ)
    (φ : PairCochain A B n) (σ : (A ⊓ B).obj (op ⦋n⦌)) :
    coverDifferenceLinear A B n φ σ =
      φ.1 ⟨σ.val, σ.property.1⟩ - φ.2 ⟨σ.val, σ.property.2⟩ := rfl

/-- Both actual restrictions commute with the alternating differential. -/
def coverRestriction (A B : S.Subcomplex) :
    complex ((A ⊔ B : S.Subcomplex) : SSet) ⟶ pairComplex A B where
  f n := ModuleCat.ofHom (coverRestrictionLinear A B n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have ha := (restriction (show A ≤ A ⊔ B from le_sup_left)).comm i (i + 1)
    have hb := (restriction (show B ≤ A ⊔ B from le_sup_right)).comm i (i + 1)
    rw [complex_d, complex_d] at ha hb
    rw [complex_d, pairComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    exact Prod.ext (congrArg (fun f ↦ f.hom φ) ha) (congrArg (fun f ↦ f.hom φ) hb)

/-- The actual intersection difference is a cochain map. -/
def coverDifference (A B : S.Subcomplex) :
    pairComplex A B ⟶ complex ((A ⊓ B : S.Subcomplex) : SSet) where
  f n := ModuleCat.ofHom (coverDifferenceLinear A B n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have ha := (restriction (show A ⊓ B ≤ A from inf_le_left)).comm i (i + 1)
    have hb := (restriction (show A ⊓ B ≤ B from inf_le_right)).comm i (i + 1)
    rw [complex_d, complex_d] at ha hb
    rw [pairComplex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    funext σ
    change differential ((A ⊓ B : S.Subcomplex) : SSet) i
        ((restriction (show A ⊓ B ≤ A from inf_le_left)).f i φ.1 -
          (restriction (show A ⊓ B ≤ B from inf_le_right)).f i φ.2) σ = _
    rw [map_sub]
    exact congrFun (congrArg₂ (· - ·)
      (congrArg (fun f ↦ f.hom φ.1) ha) (congrArg (fun f ↦ f.hom φ.2) hb)) σ

theorem coverRestriction_comp_coverDifference (A B : S.Subcomplex) :
    coverRestriction A B ≫ coverDifference A B = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  exact sub_self _

/-- The actual cochain restriction/difference short complex on a simplicial union. -/
def coverShortComplex (A B : S.Subcomplex) :
    ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℕ) :=
  ShortComplex.mk (coverRestriction A B) (coverDifference A B)
    (coverRestriction_comp_coverDifference A B)

/-- A cochain on the actual union is determined by its two restrictions. -/
theorem coverRestrictionLinear_injective (A B : S.Subcomplex) (n : ℕ) :
    Function.Injective (coverRestrictionLinear A B n) := by
  intro φ ψ h
  funext σ
  rcases σ.property with ha | hb
  · exact congrFun (congrArg Prod.fst h) ⟨σ.val, ha⟩
  · exact congrFun (congrArg Prod.snd h) ⟨σ.val, hb⟩

/-- Extension by zero on the first piece gives every intersection cochain as a difference. -/
theorem coverDifferenceLinear_surjective (A B : S.Subcomplex) (n : ℕ) :
    Function.Surjective (coverDifferenceLinear A B n) := by
  classical
  intro φ
  refine ⟨(fun σ ↦ if h : σ.val ∈ B.obj (op ⦋n⦌) then
    φ ⟨σ.val, ⟨σ.property, h⟩⟩ else 0, 0), ?_⟩
  funext σ
  simp only [coverDifferenceLinear_apply, dite_eq_left σ.property.2, Pi.zero_apply, sub_zero]
  exact congrArg φ (Subtype.ext rfl)

/-- Choose the first value on the first subcomplex and the second value elsewhere.
For compatible cochains the following theorem proves this is their actual gluing. -/
def glueFunction (A B : S.Subcomplex) (n : ℕ) (φ : PairCochain A B n) :
    Cochain ((A ⊔ B : S.Subcomplex) : SSet) n := by
  classical
  exact fun σ ↦ if h : σ.val ∈ A.obj (op ⦋n⦌) then φ.1 ⟨σ.val, h⟩
    else φ.2 ⟨σ.val, σ.property.resolve_left h⟩

/-- Zero restriction difference is precisely the compatibility required for gluing. -/
theorem coverRestrictionLinear_glueFunction (A B : S.Subcomplex) (n : ℕ)
    (φ : PairCochain A B n) (hφ : coverDifferenceLinear A B n φ = 0) :
    coverRestrictionLinear A B n (glueFunction A B n φ) = φ := by
  classical
  apply Prod.ext
  · funext σ
    simp only [coverRestrictionLinear_apply, glueFunction, dite_eq_left σ.property]
    exact congrArg φ.1 (Subtype.ext rfl)
  · funext σ
    by_cases ha : σ.val ∈ A.obj (op ⦋n⦌)
    · have h := congrFun hφ ⟨σ.val, ⟨ha, σ.property⟩⟩
      simp only [coverDifferenceLinear_apply, Pi.zero_apply] at h
      simp only [coverRestrictionLinear_apply, glueFunction, dite_eq_left ha]
      exact (sub_eq_zero.mp h).trans (congrArg φ.2 (Subtype.ext rfl))
    · simp only [coverRestrictionLinear_apply, glueFunction, dite_eq_right ha]
      exact congrArg φ.2 (Subtype.ext rfl)

/-- Degreewise exactness uses actual compatible-function gluing. -/
theorem coverShortComplex_degreewise_shortExact (A B : S.Subcomplex) (n : ℕ) :
    ((coverShortComplex A B).map (HomologicalComplex.eval _ _ n)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro φ
    constructor
    · intro hφ
      exact ⟨glueFunction A B n φ, coverRestrictionLinear_glueFunction A B n φ hφ⟩
    · rintro ⟨ψ, rfl⟩
      funext σ
      exact sub_self _
  · exact coverRestrictionLinear_injective A B n
  · exact coverDifferenceLinear_surjective A B n

/-- The restriction/difference sequence is short exact as actual cochain complexes. -/
theorem coverShortComplex_shortExact (A B : S.Subcomplex) :
    (coverShortComplex A B).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (coverShortComplex_degreewise_shortExact A B)

/-- The connecting map from intersection degree `n` to union degree `n+1`, constructed
from this actual short exact sequence. -/
def connecting (A B : S.Subcomplex) (n : ℕ) :
    (complex ((A ⊓ B : S.Subcomplex) : SSet)).homology n ⟶
      (complex ((A ⊔ B : S.Subcomplex) : SSet)).homology (n + 1) :=
  (coverShortComplex_shortExact A B).δ n (n + 1) (by simp)

/-- Exactness at the union group after the connecting map. -/
theorem homology_exact_union (A B : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk (connecting A B n)
      (HomologicalComplex.homologyMap (coverRestriction A B) (n + 1))
        ((coverShortComplex_shortExact A B).δ_comp n (n + 1) (by simp))).Exact :=
  (coverShortComplex_shortExact A B).homology_exact₁ n (n + 1) (by simp)

/-- Exactness at the pair of pieces. -/
theorem homology_exact_pair (A B : S.Subcomplex) (n : ℕ) :
    ((coverShortComplex A B).map (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (coverShortComplex_shortExact A B).homology_exact₂ n

/-- Exactness at the intersection group before the connecting map. -/
theorem homology_exact_intersection (A B : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (coverDifference A B) n)
      (connecting A B n) ((coverShortComplex_shortExact A B).comp_δ n (n + 1) (by simp))).Exact :=
  (coverShortComplex_shortExact A B).homology_exact₃ n (n + 1) (by simp)

end HodgeConjecture.SubcomplexCochains
