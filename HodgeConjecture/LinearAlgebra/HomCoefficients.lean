module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public noncomputable section

/-!
# Exact linear functionals with coefficient change

Linear functionals into a coefficient algebra form an exact contravariant
functor on vector spaces. Scalar extension of the ordinary dual identifies
these functionals when the source vector space is finite dimensional.
No finite-dimensional hypothesis is imposed on a chain module here.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite
open scoped TensorProduct

namespace HodgeConjecture.HomCoefficients

variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

/-- Unrestricted linear functionals, with their native coefficient-algebra action. -/
@[implicit_reducible]
def functor : (ModuleCat.{0} k)ᵒᵖ ⥤ ModuleCat.{0} A where
  obj V := ModuleCat.of A (V.unop →ₗ[k] A)
  map f := ModuleCat.ofHom
    { toFun := fun φ ↦ φ.comp f.unop.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := by ext φ x; rfl
  map_comp _ _ := by ext φ x; rfl

instance : (functor k A).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    exact φ.map_add _ _

/-- A functional vanishing on the kernel factors through the original linear map. -/
theorem exists_factor {V W : ModuleCat.{0} k} (f : V ⟶ W) (φ : V →ₗ[k] A)
    (h : LinearMap.ker f.hom ≤ LinearMap.ker φ) :
    ∃ ψ : W →ₗ[k] A, ψ.comp f.hom = φ := by
  let q := (LinearMap.ker f.hom).liftQ φ h
  let r := q.comp f.hom.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := r.exists_extend
  refine ⟨ψ, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hψ (f.hom.rangeRestrict v)
  change ψ (f v) = φ v
  rw [show φ v = q ((LinearMap.ker f.hom).mkQ v) from rfl]
  rw [show (LinearMap.ker f.hom).mkQ v =
    f.hom.quotKerEquivRange.symm (f.hom.rangeRestrict v) from
      (f.hom.quotKerEquivRange.symm_apply_apply _).symm]
  exact hv

/-- Exactness uses extension from subspaces, without any dimension bound. -/
theorem map_exact (S : ShortComplex (ModuleCat.{0} k)ᵒᵖ) (hS : S.Exact) :
    (S.map (functor k A)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    change (φ.comp S.f.unop.hom).comp S.g.unop.hom = 0
    rw [LinearMap.comp_assoc]
    have hz : S.f.unop.hom.comp S.g.unop.hom = 0 := by
      exact congrArg ModuleCat.Hom.hom S.unop.zero
    rw [hz, LinearMap.comp_zero]
  · intro φ hφ
    have hex := hS.unop.moduleCat_range_eq_ker
    change LinearMap.range S.g.unop.hom = LinearMap.ker S.f.unop.hom at hex
    have hz : φ.comp S.g.unop.hom = 0 := hφ
    obtain ⟨ψ, hψ⟩ := exists_factor k A S.f.unop φ (by
      rw [← hex]
      rintro _ ⟨v, rfl⟩
      exact LinearMap.congr_fun hz v)
    exact ⟨ψ, hψ⟩

instance : (functor k A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (map_exact k A)

/-- Coefficient inclusion on unrestricted functionals. -/
def inclusion (V : ModuleCat.{0} k) :
    (V →ₗ[k] k) →ₗ[k] (V →ₗ[k] A) :=
  (Algebra.linearMap k A).compRight k

/-- Tensor extension is evaluation on the same original vector space. -/
def comparison (V : ModuleCat.{0} k) :
    A ⊗[k] (V →ₗ[k] k) →ₗ[A] (V →ₗ[k] A) :=
  (inclusion k A V).liftBaseChange A

@[simp]
theorem comparison_tmul (V : ModuleCat.{0} k) (a : A) (φ : V →ₗ[k] k) (v : V) :
    comparison k A V (a ⊗ₜ[k] φ) v = a * algebraMap k A (φ v) := rfl

/-- Finiteness is needed only for the vector space whose dual is compared. -/
theorem comparison_bijective (V : ModuleCat.{0} k) [FiniteDimensional k V] :
    Function.Bijective (comparison k A V) := by
  have heq : comparison k A V =
      IsBaseChange.linearMapRightBaseChangeHom A V (Algebra.linearMap k A) := by
    ext a φ
    rfl
  rw [heq]
  exact (IsBaseChange.linearMapRightBaseChangeEquiv V (IsBaseChange.linearMap k A)).bijective

/-- The finite-dimensional coefficient isomorphism has the original evaluation map as its hom. -/
def comparisonEquiv (V : ModuleCat.{0} k) [FiniteDimensional k V] :
    A ⊗[k] (V →ₗ[k] k) ≃ₗ[A] (V →ₗ[k] A) :=
  LinearEquiv.ofBijective (comparison k A V) (comparison_bijective k A V)

/-- Scalar extension with the existing algebra action on the coefficient ring. -/
@[implicit_reducible]
def tensorFunctor : ModuleCat.{0} k ⥤ ModuleCat.{0} A where
  obj V := ModuleCat.of A (A ⊗[k] V)
  map f := ModuleCat.ofHom (f.hom.baseChange A)
  map_id V := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : V →ₗ[k] V).baseChange A = LinearMap.id
    ext a
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change (g.hom.comp f.hom).baseChange A = (g.hom.baseChange A).comp (f.hom.baseChange A)
    ext a
    rfl

instance : (tensorFunctor k A).Additive where
  map_add := by
    intro V W f g
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).baseChange A = f.hom.baseChange A + g.hom.baseChange A
    ext a
    exact TensorProduct.tmul_add _ _ _

/-- Flatness over the source field proves exactness on the original tensor maps. -/
theorem tensorFunctor_map_exact (S : ShortComplex (ModuleCat.{0} k)) (hS : S.Exact) :
    (S.map (tensorFunctor k A)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact A hS

instance : (tensorFunctor k A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (tensorFunctor_map_exact k A)

/-- Evaluation is natural in the original vector space, including infinite-dimensional ones. -/
def coefficientTransform : functor k k ⋙ tensorFunctor k A ⟶ functor k A where
  app V := ModuleCat.ofHom (comparison k A V.unop)
  naturality V W f := by
    apply ModuleCat.hom_ext
    change (comparison k A W.unop).comp (((functor k k).map f).hom.baseChange A) =
      ((functor k A).map f).hom.comp (comparison k A V.unop)
    ext a φ
    rfl

/-- Functionals on the original chain complex, with coefficients in the algebra. -/
abbrev dualComplex (K : ChainComplex (ModuleCat.{0} k) ℕ) :
    CochainComplex (ModuleCat.{0} A) ℕ :=
  ((functor k A).mapHomologicalComplex (.up ℕ)).obj K.op

/-- Exact functionals identify dual cohomology with functionals on the original homology. -/
def dualHomologyIso (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    (dualComplex k A K).homology n ≅ ModuleCat.of A (K.homology n →ₗ[k] A) :=
  (K.op.sc n).mapHomologyIso (functor k A) ≪≫ (functor k A).mapIso (K.homologyOp n)

/-- The actual cochain coefficient map; its terms need not be isomorphisms. -/
def complexComparison (K : ChainComplex (ModuleCat.{0} k) ℕ) :
    ((tensorFunctor k A).mapHomologicalComplex (.up ℕ)).obj (dualComplex k k K) ⟶
      dualComplex k A K :=
  ((coefficientTransform k A).mapHomologicalComplex (.up ℕ)).app K.op

@[simp]
theorem complexComparison_apply (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    (a : A) (φ : K.X n →ₗ[k] k) (v : K.X n) :
    (show K.X n →ₗ[k] A from (complexComparison k A K).f n (a ⊗ₜ[k] φ)) v =
      a * algebraMap k A (φ v) := rfl

/-- Exact scalar extension identifies homology of the tensor complex with the original tensor target. -/
def tensorHomologyIso (K : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    (((tensorFunctor k A).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      ModuleCat.of A (A ⊗[k] K.homology n) :=
  (K.sc n).mapHomologyIso (tensorFunctor k A)

@[reassoc]
theorem tensorHomologyIso_naturality {K L : CochainComplex (ModuleCat.{0} k) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (((tensorFunctor k A).mapHomologicalComplex (.up ℕ)).map f) n ≫
        (tensorHomologyIso k A L n).hom =
      (tensorHomologyIso k A K n).hom ≫
        (tensorFunctor k A).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map f) (tensorFunctor k A)

/-- Coefficient change on cohomology, with the original tensor complexification as source. -/
def cohomologyComparison (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    ModuleCat.of A (A ⊗[k] (dualComplex k k K).homology n) ⟶
      (dualComplex k A K).homology n :=
  (tensorHomologyIso k A (dualComplex k k K) n).inv ≫
    HomologicalComplex.homologyMap (complexComparison k A K) n

/-- The comparison is induced by the actual cochain coefficient map, not an unrelated equivalence. -/
@[reassoc]
theorem tensorHomologyIso_cohomologyComparison (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    (tensorHomologyIso k A (dualComplex k k K) n).hom ≫ cohomologyComparison k A K n =
      HomologicalComplex.homologyMap (complexComparison k A K) n := by
  simp only [cohomologyComparison, Iso.hom_inv_id_assoc]

/-- Only the homology in this degree must be finite dimensional; chain modules may be infinite. -/
theorem complexComparison_quasiIsoAt (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    [FiniteDimensional k (K.homology n)] :
    QuasiIsoAt (complexComparison k A K) n := by
  have : FiniteDimensional k ((K.op.homology n).unop : ModuleCat.{0} k) :=
    Module.Finite.equiv (K.homologyOp n).unop.toLinearEquiv
  have : IsIso ((coefficientTransform k A).app (K.op.homology n)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact comparison_bijective k A (K.op.homology n).unop
  have : (functor k k ⋙ tensorFunctor k A).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ (fun S hS ↦
      tensorFunctor_map_exact k A (S.map (functor k k)) (map_exact k k S hS))
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (ShortComplex.homologyMap ((K.op.sc n).mapNatTrans (coefficientTransform k A)))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso ((coefficientTransform k A).app (K.op.sc n).homology) :=
    inferInstanceAs (IsIso ((coefficientTransform k A).app (K.op.homology n)))
  infer_instance

theorem cohomologyComparison_isIso (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    [FiniteDimensional k (K.homology n)] : IsIso (cohomologyComparison k A K n) := by
  have := complexComparison_quasiIsoAt k A K n
  unfold cohomologyComparison
  infer_instance

/-- The isomorphism retains the original cochain coefficient map. -/
def cohomologyIso (K : ChainComplex (ModuleCat.{0} k) ℕ) (n : ℕ)
    [FiniteDimensional k (K.homology n)] :
    ModuleCat.of A (A ⊗[k] (dualComplex k k K).homology n) ≅
      (dualComplex k A K).homology n := by
  have := cohomologyComparison_isIso k A K n
  exact asIso (cohomologyComparison k A K n)

end HodgeConjecture.HomCoefficients
