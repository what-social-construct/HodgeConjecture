module

public import Mathlib.LinearAlgebra.Pi

@[expose] public section

set_option autoImplicit false

namespace HodgeConjecture

open Classical
open scoped BigOperators

noncomputable section

universe u v w

/-- Linear summation over the actual fibers of a map with finite domain. -/
def finiteFiberSum (R : Type w) [CommSemiring R]
    {S : Type u} {I : Type v} [Fintype S] (f : S → I) : (S → R) →ₗ[R] (I → R) where
  toFun a i := ∑ s, if f s = i then a s else 0
  map_add' a b := by
    ext i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  map_smul' r a := by
    ext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp

@[simp]
theorem finiteFiberSum_apply (R : Type w) [CommSemiring R]
    {S : Type u} {I : Type v} [Fintype S] (f : S → I) (a : S → R) (i : I) :
    finiteFiberSum R f a i = ∑ s, if f s = i then a s else 0 := rfl

end

end HodgeConjecture
