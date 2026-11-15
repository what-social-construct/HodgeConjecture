module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Localization.Defs

@[expose] public section

/-!
# Fixed rings and localization at fixed base denominators

For an injective localization map equivariant under a group action, taking
fixed points commutes with localization at denominators in the fixed base.
The injectivity hypothesis is satisfied by the normalization inclusions
inside a common field.  The result is stated at the `IsLocalization` level so
the selected-prime local-ring comparison can use the ordinary localization
API.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

variable {A S T G : Type*}
variable [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
variable [Group G] [MulSemiringAction G S] [MulSemiringAction G T]
variable [SMulCommClass G A S] [SMulCommClass G A T]

/-- The map of fixed rings induced by an equivariant algebra map. -/
def fixedSubalgebraLocalizationMap (H : Subgroup G)
    (hequiv : ∀ (g : G) (x : S),
      g • algebraMap S T x = algebraMap S T (g • x)) :
    FixedPoints.subalgebra A S H →ₐ[A] FixedPoints.subalgebra A T H where
  toFun x := ⟨algebraMap S T x, fun g ↦ by
    change (g : G) • algebraMap S T (x : S) = algebraMap S T (x : S)
    rw [hequiv (g : G) (x : S)]
    exact congrArg (algebraMap S T) (x.property g)⟩
  map_one' := Subtype.ext (map_one (algebraMap S T))
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (algebraMap S T) (x : S) (y : S)
  map_zero' := Subtype.ext (map_zero (algebraMap S T))
  map_add' x y := by
    apply Subtype.ext
    exact map_add (algebraMap S T) (x : S) (y : S)
  commutes' a := by
    apply Subtype.ext
    change algebraMap S T (algebraMap A S a) = algebraMap A T a
    exact (IsScalarTower.algebraMap_apply A S T a).symm

/-- Equivariant localization at fixed base denominators localizes the fixed
subalgebra. In the normalization application, `S → T` is the inclusion into
the integral closure over a localized base. -/
theorem fixedSubalgebra_isLocalization_of_injective
    [IsDomain T] (H : Subgroup G) (M : Submonoid A)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) T]
    (hequiv : ∀ (g : G) (x : S),
      g • algebraMap S T x = algebraMap S T (g • x))
    (hinjective : Function.Injective (algebraMap S T)) :
    let F := FixedPoints.subalgebra A S H
    let F' := FixedPoints.subalgebra A T H
    letI : Algebra F F' := (fixedSubalgebraLocalizationMap H hequiv).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid F M) F' := by
  dsimp only
  let F := FixedPoints.subalgebra A S H
  let F' := FixedPoints.subalgebra A T H
  let f : F →ₐ[A] F' := fixedSubalgebraLocalizationMap H hequiv
  letI : Algebra F F' := f.toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    let d : Algebra.algebraMapSubmonoid S M :=
      ⟨algebraMap A S m, ⟨m, hm, rfl⟩⟩
    have hdT : algebraMap S T (d : S) = algebraMap A T m := by
      change algebraMap S T (algebraMap A S m) = algebraMap A T m
      exact (IsScalarTower.algebraMap_apply A S T m).symm
    have hu : IsUnit (algebraMap A T m) :=
      hdT ▸ IsLocalization.map_units T d
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨z, ?_⟩, ?_⟩
    · intro g
      apply hu.mul_left_inj.mp
      have hg : (g : G) • algebraMap A T m = algebraMap A T m :=
        smul_algebraMap (g : G) m
      have hgz : ((g : G) • z) * algebraMap A T m = 1 := by
        calc
          ((g : G) • z) * algebraMap A T m =
              ((g : G) • z) * ((g : G) • algebraMap A T m) := by rw [hg]
          _ = (g : G) • (z * algebraMap A T m) := (smul_mul' _ _ _).symm
          _ = 1 := by rw [mul_comm z, hz, smul_one]
      exact hgz.trans (by simpa only [mul_comm z] using hz.symm)
    · apply Subtype.ext
      have hmap : (algebraMap F F' : F →+* F') = f.toRingHom :=
        RingHom.algebraMap_toAlgebra f.toRingHom
      rw [hmap]
      change (f (algebraMap A F m) : T) * z = 1
      rw [f.commutes]
      change algebraMap A T m * z = 1
      exact hz
  · intro y
    obtain ⟨⟨x, d⟩, hy⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid S M) (y : T)
    obtain ⟨m, hm, hdm⟩ := d.property
    have hdenS : ∀ g : G, g • (d : S) = d := by
      intro g
      rw [← hdm]
      exact smul_algebraMap g m
    have hdenT : ∀ g : G,
        g • algebraMap S T (d : S) = algebraMap S T (d : S) := by
      intro g
      rw [hequiv g (d : S), hdenS g]
    have hx : ∀ g : H, (g : G) • x = x := by
      intro g
      apply hinjective
      calc
        algebraMap S T ((g : G) • x) =
            (g : G) • algebraMap S T x := (hequiv g x).symm
        _ = (g : G) • ((y : T) * algebraMap S T (d : S)) := by rw [hy]
        _ = (y : T) * algebraMap S T (d : S) := by
          have hyfixed : (g : G) • (y : T) = y := by
            simpa only [Subgroup.smul_def] using y.property g
          rw [smul_mul', hyfixed, hdenT (g : G)]
        _ = algebraMap S T x := hy
    let xF : F := ⟨x, hx⟩
    let dF : Algebra.algebraMapSubmonoid F M :=
      ⟨algebraMap A F m, ⟨m, hm, rfl⟩⟩
    refine ⟨⟨xF, dF⟩, ?_⟩
    apply Subtype.ext
    change (y : T) * algebraMap S T (algebraMap A S m) = algebraMap S T x
    rw [hdm]
    exact hy
  · intro x y h
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    apply Subtype.ext
    apply hinjective
    exact congrArg (fun z : F' ↦ (z : T)) h



end

end HodgeConjecture.NormalizationInertia
