/-
Adapted from:
  GaloisObstructionTheory/Jacobian/General/Galois/TensorInvariants.lean
in the sibling galois-obstruction-theory repository.
Source SHA-256:
  ce099a1f1cb419ec4a7ddce7ee0aa30559cdbc6b9ba8d6f112bdeeaec35778b8

The original algebra theorem is generalized here to arbitrary vector spaces.
The following notice is preserved from Jacobian/LICENSE in the source repository.

MIT License

Copyright (c) 2026 Chloe van der Vlugt and contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

/-!
# Galois descent for scalar-extended vector spaces

For a finite Galois extension `N / K` and any `K`-vector space `V`, a tensor in
`N ⊗[K] V` is fixed under all automorphisms acting on its first factor exactly
when it is `1 ⊗ₜ v` for a unique `v : V`. In an extended basis, the proof
descends each of the tensor's finitely many nonzero coefficients.

No multiplication or algebra structure on `V` is required. In particular, this
result concerns scalar extension of a given vector space; an application to a
Chow module does not assert geometric base change or descent of Chow groups.
-/

set_option autoImplicit false

namespace HodgeConjecture.GaloisDescent

open scoped TensorProduct

variable {K N V : Type*}
  [Field K] [Field N] [Algebra K N] [AddCommGroup V] [Module K V]

/-- The canonical linear inclusion into scalar extension, `v ↦ 1 ⊗ₜ v`. -/
def tensorInclude : V →ₗ[K] N ⊗[K] V :=
  TensorProduct.mk K N V 1

@[simp]
theorem tensorInclude_apply (v : V) :
    tensorInclude (N := N) v = (1 : N) ⊗ₜ[K] v :=
  rfl

/-- An automorphism of the scalar field acts on the first tensor factor.
This action is `K`-linear, so it is available for arbitrary `K`-vector spaces. -/
def scalarAction (g : N ≃ₐ[K] N) : N ⊗[K] V →ₗ[K] N ⊗[K] V :=
  TensorProduct.map g.toAlgHom.toLinearMap LinearMap.id

@[simp]
theorem scalarAction_tmul (g : N ≃ₐ[K] N) (n : N) (v : V) :
    scalarAction g (n ⊗ₜ[K] v) = g n ⊗ₜ[K] v :=
  rfl

@[simp]
theorem scalarAction_tensorInclude (g : N ≃ₐ[K] N) (v : V) :
    scalarAction g (tensorInclude (N := N) v) = tensorInclude (N := N) v := by
  simp

/-- Scalar extension over a field preserves the original vector space
injectively. This assertion does not require a finite or Galois extension. -/
theorem tensorInclude_injective :
    Function.Injective (tensorInclude (K := K) (N := N) (V := V)) := by
  classical
  let b := Module.Free.chooseBasis K V
  intro v w h
  apply b.repr.injective
  ext i
  apply RingHom.injective (algebraMap K N)
  have hc := congrArg (fun z : N ⊗[K] V => (b.baseChange N).repr z i) h
  simpa [Algebra.smul_def] using hc

private theorem baseChange_repr_scalarAction
    {ι : Type*} (b : Module.Basis ι K V) (g : N ≃ₐ[K] N)
    (z : N ⊗[K] V) (i : ι) :
    (b.baseChange N).repr (scalarAction g z) i =
      g ((b.baseChange N).repr z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul n v => simp [Algebra.smul_def]
  | add z w hz hw => simp [hz, hw]

/-- The tensors fixed under every automorphism on the first factor are
exactly those included from the original vector space. -/
theorem mem_range_tensorInclude_iff_fixed
    [FiniteDimensional K N] [IsGalois K N] (z : N ⊗[K] V) :
    z ∈ Set.range (tensorInclude (K := K) (N := N) (V := V)) ↔
      ∀ g : N ≃ₐ[K] N, scalarAction g z = z := by
  constructor
  · rintro ⟨v, rfl⟩ g
    simp
  · intro hz
    classical
    let b := Module.Free.chooseBasis K V
    let coefficient := (b.baseChange N).repr z
    have coefficient_in_range (i : Module.Free.ChooseBasisIndex K V) :
        coefficient i ∈ Set.range (algebraMap K N) := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed (coefficient i)).2
      intro g
      have map_coefficient := baseChange_repr_scalarAction b g z i
      rw [hz g] at map_coefficient
      exact map_coefficient.symm
    let liftCoefficient := Function.invFun (algebraMap K N)
    have lift_zero : liftCoefficient 0 = 0 := by
      simpa [liftCoefficient] using
        Function.leftInverse_invFun (RingHom.injective (algebraMap K N)) (0 : K)
    let lifted := Finsupp.mapRange liftCoefficient lift_zero coefficient
    refine ⟨b.repr.symm lifted, (b.baseChange N).repr.injective ?_⟩
    ext i
    simp only [tensorInclude_apply, Module.Basis.baseChange_repr_tmul,
      LinearEquiv.apply_symm_apply, Algebra.smul_def, mul_one]
    exact Function.invFun_eq (coefficient_in_range i)

/-- Choose the unique original vector represented by a fixed tensor. -/
noncomputable def descendFixed
    [FiniteDimensional K N] [IsGalois K N]
    (z : N ⊗[K] V) (hz : ∀ g : N ≃ₐ[K] N, scalarAction g z = z) : V :=
  Classical.choose ((mem_range_tensorInclude_iff_fixed z).2 hz)

/-- Including a descended fixed tensor recovers the tensor itself. -/
@[simp]
theorem include_descendFixed
    [FiniteDimensional K N] [IsGalois K N]
    (z : N ⊗[K] V) (hz : ∀ g : N ≃ₐ[K] N, scalarAction g z = z) :
    tensorInclude (N := N) (descendFixed z hz) = z :=
  Classical.choose_spec ((mem_range_tensorInclude_iff_fixed z).2 hz)

/-- The descended vector is unique. -/
theorem descendFixed_unique
    [FiniteDimensional K N] [IsGalois K N]
    (z : N ⊗[K] V) (hz : ∀ g : N ≃ₐ[K] N, scalarAction g z = z)
    (v : V) (hv : tensorInclude (N := N) v = z) :
    v = descendFixed z hz :=
  tensorInclude_injective (hv.trans (include_descendFixed z hz).symm)

/-- Descending an included vector recovers the original vector. -/
@[simp]
theorem descendFixed_tensorInclude
    [FiniteDimensional K N] [IsGalois K N] (v : V)
    (hv : ∀ g : N ≃ₐ[K] N,
      scalarAction g (tensorInclude (N := N) v) = tensorInclude (N := N) v) :
    descendFixed (tensorInclude (N := N) v) hv = v := by
  exact (descendFixed_unique _ hv v rfl).symm

/-- The original algebra formulation, as a specialization of vector-space
descent. The proof still uses only the vector-space structure of `A`. -/
theorem mem_range_includeRight_iff_fixed
    {A : Type*} [CommRing A] [Algebra K A]
    [FiniteDimensional K N] [IsGalois K N] (z : N ⊗[K] A) :
    z ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[K] N ⊗[K] A) ↔
      ∀ g : N ≃ₐ[K] N,
        Algebra.TensorProduct.map g.toAlgHom (AlgHom.id K A) z = z := by
  have action_eq (g : N ≃ₐ[K] N) (w : N ⊗[K] A) :
      scalarAction g w =
        Algebra.TensorProduct.map g.toAlgHom (AlgHom.id K A) w := by
    induction w using TensorProduct.inductionOn with
    | tmul n a => simp
    | add w v hw hv => simp [hw, hv]
  simpa only [Set.mem_range, tensorInclude_apply,
    Algebra.TensorProduct.includeRight_apply, action_eq] using
      (mem_range_tensorInclude_iff_fixed (K := K) (N := N) (V := A) z)

end HodgeConjecture.GaloisDescent
