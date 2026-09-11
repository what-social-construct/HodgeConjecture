import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.Unramified.Locus

/-!
# Visible formally unramified loci

These are the two presentation-independent visible-unramifiedness lemmas.

The first passes formal unramifiedness to the map between local rings at a
prime.  The second says that if an affine open sheet is formally unramified
over a base, then every point of the ambient affine model visible on that
sheet is unramified over the base.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/--
Formal unramifiedness survives passage from a ring map to the induced map
between local rings at a prime.
-/
lemma ringHom_formallyUnramified_localRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FormallyUnramified)
    (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyUnramified := by
  algebraize [f, Localization.localRingHom (J.comap f) J f rfl]
  haveI : Algebra.FormallyUnramified R S := hf
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime J) :=
    inferInstance
  haveI : IsScalarTower R
      (Localization.AtPrime (J.comap (algebraMap R S)))
      (Localization.AtPrime J) :=
    .of_algebraMap_eq fun x ↦
      (Localization.localRingHom_to_map _ _ _ rfl x).symm
  change Algebra.FormallyUnramified
    (Localization.AtPrime (J.comap f)) (Localization.AtPrime J)
  exact Algebra.FormallyUnramified.of_comp R
    (Localization.AtPrime (J.comap (algebraMap R S)))
    (Localization.AtPrime J)

/--
Let `j : U ⟶ X` be an open immersion into an affine scheme.  If the
composite `U ⟶ X ⟶ Spec R` is formally unramified, then `X` is unramified
over `R` at every point represented by `U`.  The visible open `U` need not
itself be affine.
-/
lemma isUnramifiedAt_of_openImmersion_comp_formallyUnramified
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    {U : Scheme.{u}}
    (j : U ⟶ Spec (.of C)) [IsOpenImmersion j]
    [AlgebraicGeometry.FormallyUnramified
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)))]
    (x : U) :
    Algebra.IsUnramifiedAt R (j.base x).asIdeal := by
  let q := j.base x
  let p := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hcomp :
      RingHom.FormallyUnramified ((j ≫ p).stalkMap x).hom :=
    HasRingHomProperty.stalkMap
      (P := @AlgebraicGeometry.FormallyUnramified)
      ringHom_formallyUnramified_localRingHom
      (inferInstance :
        AlgebraicGeometry.FormallyUnramified (j ≫ p)) x
  have hpstalk :
      RingHom.FormallyUnramified (p.stalkMap q).hom := by
    rw [Scheme.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at hcomp
    exact hcomp
  have hlocal :
      RingHom.FormallyUnramified
        (Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl) :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (algebraMap R C)) q)).mp hpstalk
  have hbase :
      RingHom.FormallyUnramified
        (algebraMap R
          (Localization.AtPrime
            (q.asIdeal.comap (algebraMap R C)))) := by
    rw [RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_isLocalization
      (q.asIdeal.comap (algebraMap R C)).primeCompl
  have htotal :
      RingHom.FormallyUnramified
        ((Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl).comp
            (algebraMap R
              (Localization.AtPrime
                (q.asIdeal.comap (algebraMap R C))))) :=
    RingHom.FormallyUnramified.stableUnderComposition
      (algebraMap R
        (Localization.AtPrime
          (q.asIdeal.comap (algebraMap R C))))
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl)
      hbase hlocal
  rw [show
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl).comp
          (algebraMap R
            (Localization.AtPrime
              (q.asIdeal.comap (algebraMap R C)))) =
        algebraMap R (Localization.AtPrime q.asIdeal) by
      ext y
      exact Localization.localRingHom_to_map _ _ _ rfl y] at htotal
  change Algebra.FormallyUnramified R
    (Localization.AtPrime q.asIdeal)
  exact RingHom.formallyUnramified_algebraMap.mp htotal

end

end HodgeConjecture.CollisionFoundations
