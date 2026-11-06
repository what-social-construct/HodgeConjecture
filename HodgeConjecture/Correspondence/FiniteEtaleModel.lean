module

public import HodgeConjecture.Correspondence.EtaleClasses
public import HodgeConjecture.Correspondence.FiniteCoproduct

@[expose] public section

/-!
# Realization models for finite étale correspondences

The unrestricted span interface in `Correspondence.Algebra` is useful for
recording formal laws, but it is too broad to model ordinary cycle theories:
arbitrary scheme correspondences include infinite coproducts.  Additivity on
all such spans can therefore force an Eilenberg-swindle collapse.

This file gives the admissible interface used by the finite-cover branch.
Its source is the convolution algebra on finite étale correspondence classes,
and its additivity requirement is only for finite indexed coproducts which
remain finite étale.  A concrete Chow or bivariant theory is still an
external input, exactly as intended; the input is now stated on a category
where a nontrivial realization can reasonably exist.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u v

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)
variable (Gamma : Type v)

/--
A rational algebra realization of finite étale endocorrespondences which is
additive on finite disjoint unions.

The algebra homomorphism supplies the identity and convolution laws.  The
last field is the separate geometric input identifying a finite coproduct of
spans with the sum of their realized classes.
-/
structure FiniteEtaleAlgebraModel
    [Ring Gamma] [Algebra ℚ Gamma] where
  realization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ] Gamma
  realization_coprod :
    ∀ (P Q : SchemeCorrespondence pX pX)
      (hP : HasFiniteEtaleLegs P)
      (hQ : HasFiniteEtaleLegs Q)
      (hCoprod : HasFiniteEtaleLegs (coprod P Q)),
      realization (finiteEtaleOfScheme (coprod P Q) hCoprod) =
        realization (finiteEtaleOfScheme P hP) +
          realization (finiteEtaleOfScheme Q hQ)
  realization_indexedCoprod :
    ∀ {iota : Type u} [Fintype iota]
      (P : iota → SchemeCorrespondence pX pX)
      (hP : ∀ i, HasFiniteEtaleLegs (P i))
      (hCoprod : HasFiniteEtaleLegs (indexedCoprod P)),
      realization
          (finiteEtaleOfScheme (indexedCoprod P) hCoprod) =
        ∑ i, realization (finiteEtaleOfScheme (P i) (hP i))

namespace FiniteEtaleAlgebraModel

variable {pX : X ⟶ S}
variable {Gamma : Type v} [Ring Gamma] [Algebra ℚ Gamma]

/-- The realized class of a finite étale scheme correspondence. -/
def classOf
    (chi : FiniteEtaleAlgebraModel pX Gamma)
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    Gamma :=
  chi.realization (finiteEtaleOfScheme P hP)

/-- Isomorphic finite étale spans have the same realized class. -/
theorem classOf_isom
    (chi : FiniteEtaleAlgebraModel pX Gamma)
    {P Q : SchemeCorrespondence pX pX}
    (hP : HasFiniteEtaleLegs P)
    (hQ : HasFiniteEtaleLegs Q)
    (e : Isom P Q) :
    chi.classOf P hP = chi.classOf Q hQ := by
  apply congrArg chi.realization
  unfold finiteEtaleOfScheme
  congr 1
  apply Subtype.ext
  exact classOf_eq_of_isom e

/-- The diagonal realizes to the multiplicative unit. -/
@[simp]
theorem classOf_identity
    (chi : FiniteEtaleAlgebraModel pX Gamma) :
    chi.classOf (identity pX) (HasFiniteEtaleLegs.identity pX) = 1 := by
  change chi.realization
      (finiteEtaleOfScheme
        (identity pX) (HasFiniteEtaleLegs.identity pX)) = 1
  rw [← map_one chi.realization]
  congr 1

/-- Pullback composition realizes to multiplication. -/
theorem classOf_comp
    (chi : FiniteEtaleAlgebraModel pX Gamma)
    (Q P : SchemeCorrespondence pX pX)
    (hQ : HasFiniteEtaleLegs Q)
    (hP : HasFiniteEtaleLegs P) :
    chi.classOf (Q.comp P) (hQ.comp hP) =
      chi.classOf Q hQ * chi.classOf P hP := by
  change chi.realization
      (finiteEtaleOfScheme (Q.comp P) (hQ.comp hP)) =
    chi.realization (finiteEtaleOfScheme Q hQ) *
      chi.realization (finiteEtaleOfScheme P hP)
  rw [← map_mul]
  unfold finiteEtaleOfScheme
  rw [MonoidAlgebra.single_mul_single]
  simp only [one_mul]
  congr 1

/-- A finite-étale binary coproduct realizes to a sum. -/
theorem classOf_coprod
    (chi : FiniteEtaleAlgebraModel pX Gamma)
    (P Q : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P)
    (hQ : HasFiniteEtaleLegs Q)
    (hCoprod : HasFiniteEtaleLegs (coprod P Q)) :
    chi.classOf (coprod P Q) hCoprod =
      chi.classOf P hP + chi.classOf Q hQ :=
  chi.realization_coprod P Q hP hQ hCoprod

/-- Finite sheet decompositions realize to finite sums. -/
theorem classOf_indexedCoprod
    (chi : FiniteEtaleAlgebraModel pX Gamma)
    {iota : Type u} [Fintype iota]
    (P : iota → SchemeCorrespondence pX pX)
    (hP : ∀ i, HasFiniteEtaleLegs (P i))
    (hCoprod : HasFiniteEtaleLegs (indexedCoprod P)) :
    chi.classOf (indexedCoprod P) hCoprod =
      ∑ i, chi.classOf (P i) (hP i) :=
  chi.realization_indexedCoprod P hP hCoprod

end FiniteEtaleAlgebraModel

end SchemeCorrespondence

end

end HodgeConjecture
