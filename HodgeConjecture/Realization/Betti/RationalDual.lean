module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import HodgeConjecture.LinearAlgebra.HomCoefficients

@[expose] public section

/-!
# Exact rational linear duals and dual cochain complexes

The unrestricted rational linear dual is an additive exact contravariant
functor on rational vector spaces. The shared coefficient-functional
construction proves exactness by extension from subspaces, with no
finite-dimensional hypothesis. Reversing a chain complex and applying this functor gives its
dual cochain complex, preserving quasi-isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RationalDual

open CategoryTheory Opposite HomologicalComplex

/-- The actual unrestricted rational linear dual, contravariant in rational modules. -/
@[implicit_reducible]
def functor : (ModuleCat.{0} ℚ)ᵒᵖ ⥤ ModuleCat.{0} ℚ :=
  HomCoefficients.functor ℚ ℚ

@[simp]
theorem functor_map_apply {M N : (ModuleCat.{0} ℚ)ᵒᵖ} (f : M ⟶ N)
    (φ : Module.Dual ℚ M.unop) (x : N.unop) :
    (show Module.Dual ℚ N.unop from functor.map f φ).toFun x = φ (f.unop x) := rfl

instance : functor.Additive := inferInstanceAs (HomCoefficients.functor ℚ ℚ).Additive

/-- Exactness of rational dualization, through the shared extension-of-functionals proof. -/
theorem map_exact (S : ShortComplex (ModuleCat.{0} ℚ)ᵒᵖ) (hS : S.Exact) :
    (S.map functor).Exact := HomCoefficients.map_exact ℚ ℚ S hS

instance : functor.PreservesHomology :=
  inferInstanceAs (HomCoefficients.functor ℚ ℚ).PreservesHomology

/-- Opposite chain complexes followed by actual rational linear dualization. -/
@[implicit_reducible]
def chainFunctor : (ChainComplex (ModuleCat.{0} ℚ) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  HomologicalComplex.opFunctor _ (ComplexShape.down ℕ) ⋙
    functor.mapHomologicalComplex (ComplexShape.up ℕ)

/-- The unrestricted rational dual cochain complex of an actual chain complex. -/
abbrev dualComplex (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) :
    CochainComplex (ModuleCat.{0} ℚ) ℕ := chainFunctor.obj (op K)

/-- Actual precomposition dualizes a chain map and reverses its direction. -/
def dualMap {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) :
    dualComplex L ⟶ dualComplex K := chainFunctor.map f.op

@[simp]
theorem dualComplex_X (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (dualComplex K).X n = ModuleCat.of ℚ (Module.Dual ℚ (K.X n)) := rfl

@[simp]
theorem dualComplex_d (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (i j : ℕ) :
    (dualComplex K).d i j = ModuleCat.ofHom (K.d j i).hom.dualMap := rfl

@[simp]
theorem dualComplex_d_apply (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (i j : ℕ)
    (φ : Module.Dual ℚ (K.X i)) (x : K.X j) :
    (show Module.Dual ℚ (K.X j) from (dualComplex K).d i j φ).toFun x = φ (K.d j i x) := rfl

@[simp]
theorem dualMap_f_apply {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (φ : Module.Dual ℚ (L.X n)) (x : K.X n) :
    (show Module.Dual ℚ (K.X n) from (dualMap f).f n φ).toFun x = φ (f.f n x) := rfl

/-- Exact rational dualization sends every actual chain quasi-isomorphism to a cochain
quasi-isomorphism, without boundedness or finite-dimensionality assumptions. -/
theorem dualMap_quasiIso {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (dualMap f) := by
  change QuasiIso ((functor.mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((HomologicalComplex.opFunctor _ (ComplexShape.down ℕ)).map f.op))
  infer_instance

instance {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (dualMap f) := dualMap_quasiIso f

end HodgeConjecture.RationalDual
