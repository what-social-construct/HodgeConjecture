/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Source: StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/IntersectionInvertibleSheaf.lean
Only the component/minimal-prime and ideal-stalk comparisons are retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.Cycles.IdealStalk
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The canonical morphism `Spec 𝒪_{X, x} ⟶ X` is an isomorphism on stalks at every prime: it
factors as the spectrum of a localization map followed by an open immersion. -/
theorem isIso_stalkMap_fromSpecStalk {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap p) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  let R := Γ(X, U)
  let A := X.presheaf.stalk x
  let q : PrimeSpectrum R := hU.primeIdealOf ⟨x, hxU⟩
  let g := X.presheaf.germ U x hxU
  let : Algebra R A := g.hom.toAlgebra
  let : IsLocalization.AtPrime A q.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime q.asIdeal ≃ₐ[R] A :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) A
  let eIso := e.toRingEquiv.toCommRingCatIso
  have hSpecIso : IsIso (Spec.map eIso.hom) := (Scheme.Spec.mapIso eIso.op).isIso_hom
  let pS : Spec A := p
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.AtPrime q.asIdeal)))).stalkMap
      (PrimeSpectrum.comap e.toRingHom p)) :=
    AlgebraicGeometry.isIso_specMap_stalkMap_localization (CommRingCat.of R)
      q.asIdeal.primeCompl (PrimeSpectrum.comap e.toRingHom p)
  have he : IsIso ((Spec.map eIso.hom).stalkMap pS) :=
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap (Spec.map eIso.hom)).mp hSpecIso).2 pS
  have hfac : CommRingCat.ofHom (algebraMap R A) =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal)) ≫
        CommRingCat.ofHom e.toRingHom := by
    ext r
    simp [e]
  have hEq : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map eIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal))) := by
    rw [← Spec.map_comp, hfac]
    rfl
  have hfirst : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R A))).stalkMap pS) := by
    rw [hEq, Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso' hloc he
  have hgerm : g = CommRingCat.ofHom (algebraMap R A) := by
    ext r
    rfl
  have hfirst' : IsIso ((Spec.map g).stalkMap pS) := by rwa [hgerm]
  have hfromSpecIso : ∀ z : Spec R, IsIso (hU.fromSpec.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap).mp hU.isOpenImmersion_fromSpec |>.2
  show IsIso ((X.fromSpecStalk x).stalkMap pS)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  exact IsIso.comp_isIso' (hfromSpecIso _) hfirst'

/-- The stalk at `x` of the vanishing ideal of an irreducible component through `x` is a minimal
prime of the local ring at `x`: on an affine chart it is the localization of the prime of the
component, which is a minimal prime of the ring of sections. -/
theorem stalk_vanishingIdeal_mem_minimalPrimes {Y : Scheme.{u}} (x : Y)
    (W : irreducibleComponents Y) (hxW : x ∈ (W : Set Y)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨(W : Set Y), isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x ∈
      minimalPrimes (Y.presheaf.stalk x) := by
  classical
  let U : Y.affineOpens :=
    ⟨(Y.affineCover.f (Y.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
  have hxU : x ∈ (U : Set Y) := Y.affineCover.covers x
  have hU := U.2
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  let : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let W' : irreducibleComponents (PrimeSpectrum Γ(Y, U)) :=
    ⟨hU.fromSpec ⁻¹' (W : Set Y),
      preimage_mem_irreducibleComponents W.2 hU.fromSpec.isOpenEmbedding
        ⟨hU.fromSpec p, by rw [hp]; exact hxW, p, rfl⟩⟩
  let q : Ideal Γ(Y, U) := PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum Γ(Y, U)))
  have hq : q.IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp W'.2.1
  have hqp : q ≤ p.asIdeal := fun r hr =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr p
      (by change hU.fromSpec p ∈ (W : Set Y); rw [hp]; exact hxW)
  let A := Y.presheaf.stalk x
  let g := Y.presheaf.germ U x hxU
  let : Algebra Γ(Y, U) A := g.hom.toAlgebra
  let : IsLocalization.AtPrime A p.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have hdisj : Disjoint (p.asIdeal.primeCompl : Set Γ(Y, U)) (q : Set Γ(Y, U)) :=
    Set.disjoint_left.mpr fun r hrp hrq => hrp (hqp hrq)
  have hqmin : q ∈ (⊥ : Ideal Γ(Y, U)).minimalPrimes := by
    rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
    have hclosed : IsClosed (W' : Set (PrimeSpectrum Γ(Y, U))) :=
      isClosed_of_mem_irreducibleComponents W'.1 W'.2
    simpa only [hclosed.closure_eq] using W'.2
  have hmapmin : Ideal.map g.hom q ∈ (⊥ : Ideal A).minimalPrimes := by
    have hbot : Ideal.map g.hom (⊥ : Ideal Γ(Y, U)) = ⊥ := by simp
    rw [← hbot]
    show Ideal.map (algebraMap Γ(Y, U) A) q ∈
      (Ideal.map (algebraMap Γ(Y, U) A) (⊥ : Ideal Γ(Y, U))).minimalPrimes
    rw [IsLocalization.minimalPrimes_map p.asIdeal.primeCompl A (⊥ : Ideal Γ(Y, U))]
    show Ideal.under Γ(Y, U) (Ideal.map (algebraMap Γ(Y, U) A) q) ∈
      (⊥ : Ideal Γ(Y, U)).minimalPrimes
    rw [IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl A hq hdisj]
    exact hqmin
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hxU]
  exact hmapmin

/-- Every irreducible component through `x` is the closure of the image of a minimal prime of the
local ring at `x` under `Spec 𝒪_{X, x} ⟶ X`. -/
theorem exists_mem_minimalPrimes_fromSpecStalk_eq {X : Scheme.{u}} (x : X)
    (W : irreducibleComponents X) (hxW : x ∈ (W : Set X)) :
    ∃ p : PrimeSpectrum (X.presheaf.stalk x),
      p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x) ∧
        X.fromSpecStalk x p = (genericPoints.ofComponent W : X) := by
  have hη := genericPoints.isGenericPoint_ofComponent W
  have hrange : (genericPoints.ofComponent W : X) ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hη.specializes hxW
  obtain ⟨p, hp⟩ := hrange
  refine ⟨p, PrimeSpectrum.isMin_iff.mp ?_, hp⟩
  intro q hqp
  have hspec : X.fromSpecStalk x q ⤳ (genericPoints.ofComponent W : X) := by
    rw [← hp]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map (X.fromSpecStalk x).continuous
  have hsub : (W : Set X) ⊆ closure ({X.fromSpecStalk x q} : Set X) := by
    rw [← hη]
    exact hspec.closure_subset
  have heq : X.fromSpecStalk x q = (genericPoints.ofComponent W : X) := by
    have hcl : closure ({X.fromSpecStalk x q} : Set X) = W :=
      subset_antisymm (W.2.2 isIrreducible_singleton.closure hsub) hsub
    exact (show IsGenericPoint (X.fromSpecStalk x q) (W : Set X) from hcl).eq hη
  have hqp' : q = p := (X.fromSpecStalk x).isEmbedding.injective (heq.trans hp.symm)
  exact le_of_eq hqp'.symm

/-- Every minimal prime of the local ring at `x` maps to the generic point of an irreducible
component through `x`. -/
theorem exists_irreducibleComponents_fromSpecStalk_eq {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)) :
    ∃ W : irreducibleComponents X, x ∈ (W : Set X) ∧
      X.fromSpecStalk x p = (genericPoints.ofComponent W : X) := by
  have hpx : X.fromSpecStalk x p ⤳ x := by
    have h : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({X.fromSpecStalk x p} : Set X)) isIrreducible_singleton.closure
  let W' : irreducibleComponents X := ⟨W, hW⟩
  have hxW : x ∈ (W' : Set X) := hsub hpx.mem_closure
  obtain ⟨q, hq, heq⟩ := exists_mem_minimalPrimes_fromSpecStalk_eq x W' hxW
  have hqp : q ≤ p := by
    refine (PrimeSpectrum.le_iff_specializes q p).mpr ?_
    refine (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp ?_
    rw [heq]
    exact (genericPoints.isGenericPoint_ofComponent W').specializes (hsub (subset_closure rfl))
  have hEq : p = q := le_antisymm ((PrimeSpectrum.isMin_iff.mpr hp) hqp) hqp
  exact ⟨W', hxW, hEq ▸ heq⟩

/-- **The irreducible components of a scheme through a point correspond to the minimal primes of
its local ring there.** A component is sent to the minimal prime whose image under
`Spec 𝒪_{X, x} ⟶ X` is its generic point. -/
def irreducibleComponentsEquivMinimalPrimes {X : Scheme.{u}} (x : X) :
    {W : irreducibleComponents X // x ∈ (W : Set X)} ≃
      {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} := by
  classical
  let g : {W : irreducibleComponents X // x ∈ (W : Set X)} →
      {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} := fun W =>
    ⟨(exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose,
      (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.1⟩
  have hg (W) : X.fromSpecStalk x (g W).1 = (genericPoints.ofComponent W.1 : X) :=
    (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.2
  refine Equiv.ofBijective g ⟨?_, ?_⟩
  · intro W V h
    have hη : (genericPoints.ofComponent W.1 : X) = (genericPoints.ofComponent V.1 : X) :=
      (hg W).symm.trans ((congrArg (fun p : {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} =>
          X.fromSpecStalk x p.1) h).trans (hg V))
    refine Subtype.ext (Subtype.ext ?_)
    exact (genericPoints.isGenericPoint_ofComponent W.1).symm.trans
      ((congrArg (fun z : X => closure ({z} : Set X)) hη).trans
        (genericPoints.isGenericPoint_ofComponent V.1))
  · intro p
    obtain ⟨W, hxW, hpW⟩ := exists_irreducibleComponents_fromSpecStalk_eq x p.1 p.2
    exact ⟨⟨W, hxW⟩, Subtype.ext
      ((X.fromSpecStalk x).isEmbedding.injective ((hg ⟨W, hxW⟩).trans hpW.symm))⟩

/-- The minimal prime attached to an irreducible component by
`AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes` maps to its generic point. -/
theorem fromSpecStalk_irreducibleComponentsEquivMinimalPrimes {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    X.fromSpecStalk x (irreducibleComponentsEquivMinimalPrimes x W).1 =
      (genericPoints.ofComponent W.1 : X) :=
  (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.2

/-- A minimal prime of the local ring at `x` whose image is a point of the component `W` is the
stalk at `x` of the vanishing ideal of `W`. -/
theorem stalk_vanishingIdeal_eq_of_mem_minimalPrimes {X : Scheme.{u}} (x : X)
    (W : irreducibleComponents X) (hxW : x ∈ (W : Set X))
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x))
    (hpW : X.fromSpecStalk x p ∈ (W : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x = p.asIdeal := by
  have hmin := stalk_vanishingIdeal_mem_minimalPrimes x W hxW
  apply le_antisymm ?_ (hp.2 ⟨hmin.1.1, bot_le⟩ ?_)
  all_goals
    let U : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
    have hxU : x ∈ U.1 := X.affineCover.covers x
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hxU]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha
      (PrimeSpectrum.comap (X.presheaf.germ U.1 x hxU).hom p) ?_
    show U.2.fromSpecStalk hxU p ∈ (W : Set X)
    rw [U.2.fromSpecStalk_eq_fromSpecStalk hxU]
    exact hpW


end

end AlgebraicGeometry
