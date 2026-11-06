module

public import HodgeConjecture.Correspondence.Examples.SplitPoints
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-!
# Intrinsic points of finite split schemes

The labels of `Spec (I → K)` are canonically its scheme-theoretic points.
Consequently an actual scheme isomorphism between two finite split
presentations induces a bijection of their labels. No chosen presentation
isomorphism or field-linear description of that isomorphism is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]

/-- The canonical equivalence from split labels to prime ideals. -/
def labelEquivSpectrum (I : Type u) [Finite I] : I ≃ PrimeSpectrum (I → K) :=
  (Equiv.sigmaUnique I (fun _ ↦ PrimeSpectrum K)).symm.trans
    (Equiv.ofBijective (PrimeSpectrum.sigmaToPi (fun _ : I ↦ K))
      (PrimeSpectrum.sigmaToPi_bijective _))

@[simp]
theorem labelEquivSpectrum_apply (I : Type u) [Finite I] (i : I) :
    labelEquivSpectrum K I i =
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : I ↦ K) i) (default : PrimeSpectrum K) := rfl

/-- The same equivalence, with the scheme's underlying point type as target. -/
def labelEquivScheme (I : Type u) [Finite I] : I ≃ scheme K I :=
  labelEquivSpectrum K I

@[simp]
theorem labelEquivScheme_apply (I : Type u) [Finite I] (i : I) :
    labelEquivScheme K I i =
      (pointInclusion K I i).base (default : PrimeSpectrum K) := rfl

/-- Naturality of the label equivalence under a function's pullback on coordinates. -/
theorem labelEquivSpectrum_natural {S I : Type u} [Finite S] [Finite I]
    (f : S → I) (s : S) :
    PrimeSpectrum.comap (Pi.ringHom (fun s ↦ Pi.evalRingHom (fun _ : I ↦ K) (f s)))
        (labelEquivSpectrum K S s) = labelEquivSpectrum K I (f s) := by
  rfl

/-- Scheme-level naturality, in the form used for the legs of split spans. -/
theorem labelEquivScheme_natural {S I : Type u} [Finite S] [Finite I]
    (f : S → I) (s : S) :
    (Spec.map (CommRingCat.ofHom
      (Pi.ringHom (fun s ↦ Pi.evalRingHom (fun _ : I ↦ K) (f s))))).base
        (labelEquivScheme K S s) = labelEquivScheme K I (f s) := rfl

/-- Relabelling induced by an actual scheme isomorphism. -/
def labelEquivOfIso {S T : Type u} [Finite S] [Finite T]
    (e : scheme K S ≅ scheme K T) : S ≃ T :=
  (labelEquivScheme K S).trans
    ((Scheme.homeoOfIso e).toEquiv.trans (labelEquivScheme K T).symm)

@[simp]
theorem labelEquivOfIso_apply {S T : Type u} [Finite S] [Finite T]
    (e : scheme K S ≅ scheme K T) (s : S) :
    labelEquivScheme K T (labelEquivOfIso K e s) =
      e.hom.base (labelEquivScheme K S s) := by
  simp [labelEquivOfIso]

/-- Equality of actual scheme maps can be evaluated on component points. -/
theorem labelEquivOfIso_respects_map {S T I : Type u}
    [Finite S] [Finite T] [Finite I]
    (e : scheme K S ≅ scheme K T)
    (p : scheme K S ⟶ scheme K I) (q : scheme K T ⟶ scheme K I)
    (f : S → I) (g : T → I)
    (hp : ∀ s, p.base (labelEquivScheme K S s) = labelEquivScheme K I (f s))
    (hq : ∀ t, q.base (labelEquivScheme K T t) = labelEquivScheme K I (g t))
    (h : e.hom ≫ q = p) (s : S) :
    g (labelEquivOfIso K e s) = f s := by
  apply (labelEquivScheme K I).injective
  rw [← hq, labelEquivOfIso_apply]
  change (e.hom ≫ q).base (labelEquivScheme K S s) = _
  rw [h, hp]

end SplitPointGeometry

end

end HodgeConjecture
