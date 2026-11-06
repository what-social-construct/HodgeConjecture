module

public import HodgeConjecture.CommutativeAlgebra.DeRham.Differential
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

@[expose] public section

/-!
# The affine de Rham cochain complex

Adapted from AxiomMath/Stacks at
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/RingTheory/DeRham/Complex.lean`, Apache-2.0.
This is the actual complex of exterior powers of Kähler differentials;
the differential and its square-zero theorem are constructed, not supplied.
-/

set_option autoImplicit false

open CategoryTheory

namespace KaehlerDifferential

universe u

section Complex

/-! From here the two ring universes are tied together, `A B : Type u`.  That is forced by
`ModuleCat.{u}` being the target category of the complex, not chosen. -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The de Rham complex `Ω^0_{B/A} → Ω^1_{B/A} → Ω^2_{B/A} → ⋯` of `B` over `A`: the exterior
powers of `Ω[B⁄A]`, as `A`-modules, with the de Rham differentials as its arrows.  The
construction has no hypothesis — the arrows are `deRhamDifferential` and the square-zero
condition is `deRhamDifferential_comp_deRhamDifferential`. -/
public noncomputable def deRhamComplex (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun p ↦ ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])))
    (fun p ↦ ModuleCat.ofHom (deRhamDifferential (A := A) p))
    (fun p ↦ ModuleCat.hom_ext (deRhamDifferential_comp_deRhamDifferential p))

/-- The degree-`p` term of the de Rham complex is `Ω^p_{B/A} = ⋀[B]^p Ω[B⁄A]`. -/
@[simp] public theorem deRhamComplex_X (p : ℕ) :
    (deRhamComplex A B).X p = ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])) := rfl

/-- The arrow of the de Rham complex out of degree `p` is `deRhamDifferential p`. -/
@[simp] public theorem deRhamComplex_d (p : ℕ) :
    (deRhamComplex A B).d p (p + 1) =
      ModuleCat.ofHom (deRhamDifferential (A := A) (B := B) p) := by
  apply CochainComplex.of_d

/-- The defining rule of the de Rham complex, read on its arrows:
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.  For `p = 0` this is the statement that
the degree-zero arrow is the universal derivation. -/
public theorem deRhamComplex_d_smul_ιMulti_D (p : ℕ) (b : Fin (p + 1) → B) :
    ((deRhamComplex A B).d p (p + 1)).hom
        (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
      exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i) := by
  rw [deRhamComplex_d]
  exact deRhamDifferential_smul_ιMulti_D p b

/-- The defining rule determines the de Rham complex: a family of `A`-linear maps on the
exterior powers of `Ω[B⁄A]` obeying `d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ ⋯ ∧ d b_p` assembles
into `deRhamComplex A B`, whatever proof of the square-zero property it is supplied with. -/
public theorem deRhamComplex_unique
    (d' : ∀ p : ℕ, ⋀[B]^p (Ω[B⁄A]) →ₗ[A] ⋀[B]^(p + 1) (Ω[B⁄A]))
    (hd' : ∀ (p : ℕ) (b : Fin (p + 1) → B),
      d' p (b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) =
        exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i))
    (hsq : ∀ p : ℕ, ModuleCat.ofHom (d' p) ≫ ModuleCat.ofHom (d' (p + 1)) = 0) :
    CochainComplex.of (fun p ↦ ModuleCat.of A ↥(⋀[B]^p (Ω[B⁄A])))
        (fun p ↦ ModuleCat.ofHom (d' p)) hsq = deRhamComplex A B := by
  have hdd : d' = fun p ↦ deRhamDifferential (A := A) (B := B) p :=
    funext fun p ↦ deRhamDifferential_unique p (d' p) (hd' p)
  subst hdd
  rfl

end Complex

end KaehlerDifferential
