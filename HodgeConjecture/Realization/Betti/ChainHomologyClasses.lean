module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

/-!
# Actual module homology classes represented by cycles

These elementwise helpers use the native cycles object, native homology
projection and native homology map. They expose representatives and
boundaries without replacing the original categorical homology object.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ChainHomologyClasses

open CategoryTheory

variable (S T : ShortComplex (ModuleCat.{0} ℚ))

/-- The original homology projection of an actual cycle representative. -/
def classOf (x : S.X₂) (hx : S.g x = 0) : S.homology := S.homologyπ (S.cyclesMk x hx)

@[simp]
theorem cyclesMk_i (x : S.X₂) (hx : S.g x = 0) : S.iCycles (S.cyclesMk x hx) = x :=
  S.i_cyclesMk x hx

theorem classOf_ι (x : S.X₂) (hx : S.g x = 0) :
    S.homologyι (classOf S x hx) = S.pOpcycles x := by
  have h := congrArg (fun f : S.cycles ⟶ S.opcycles ↦ f (S.cyclesMk x hx)) S.homology_π_ι
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, cyclesMk_i, classOf] using h

/-- Every element of the original native homology has an actual cycle representative. -/
theorem classOf_surjective (z : S.homology) : ∃ x : S.X₂, ∃ hx : S.g x = 0, classOf S x hx = z := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance z
  have hx : S.g (S.iCycles c) = 0 := by
    have h := congrArg (fun f : S.cycles ⟶ S.X₃ ↦ f c) S.iCycles_g
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  refine ⟨S.iCycles c, hx, ?_⟩
  have he : S.cyclesMk (S.iCycles c) hx = c := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    exact cyclesMk_i S (S.iCycles c) hx
  rw [classOf, he, hc]

/-- A native class vanishes exactly when its actual cycle is an incoming boundary. -/
theorem classOf_eq_zero_iff (x : S.X₂) (hx : S.g x = 0) :
    classOf S x hx = 0 ↔ ∃ a : S.X₁, S.f a = x := by
  change classOf S x hx = 0 ↔ x ∈ LinearMap.range S.f.hom
  rw [← S.moduleCat_pOpcycles_eq_zero_iff]
  constructor
  · intro h
    rw [← classOf_ι S x hx, h, map_zero]
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [classOf_ι, h, map_zero]

theorem classOf_map (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0)
    (hy : T.g (φ.τ₂ x) = 0) :
    ShortComplex.homologyMap φ (classOf S x hx) = classOf T (φ.τ₂ x) hy := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [classOf_ι T]
  have h := congrArg (fun f : S.cycles ⟶ T.opcycles ↦ f (S.cyclesMk x hx))
    (ShortComplex.π_homologyMap_ι φ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, cyclesMk_i, classOf] using h

theorem map_cycle (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) : T.g (φ.τ₂ x) = 0 := by
  have h := congrArg (fun f : S.X₂ ⟶ T.X₃ ↦ f x) φ.comm₂₃
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] using h

theorem classOf_congr {x y : S.X₂} (h : x = y) (hx : S.g x = 0) (hy : S.g y = 0) :
    classOf S x hx = classOf S y hy := by cases h; rfl

section Complex

open HomologicalComplex

variable {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}

/-- An actual injective chain map is a quasi-isomorphism if compatible families of endomorphisms
inducing the identity on homology eventually send each individual chain into its image. -/
theorem quasiIso_of_eventual_image (f : K ⟶ L)
    (hf : ∀ n, Function.Injective (f.f n))
    (pK : ℕ → (K ⟶ K)) (pL : ℕ → (L ⟶ L))
    (hK : ∀ k n, homologyMap (pK k) n = 𝟙 _)
    (hL : ∀ k n, homologyMap (pL k) n = 𝟙 _)
    (hcomm : ∀ k, f ≫ pL k = pK k ≫ f)
    (hevent : ∀ n (c : L.X n), ∃ k, ∃ a : K.X n, f.f n a = (pL k).f n c) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let φ : K.sc n ⟶ L.sc n := (shortComplexFunctor _ _ n).map f
  let α (k : ℕ) : K.sc n ⟶ K.sc n := (shortComplexFunctor _ _ n).map (pK k)
  let β (k : ℕ) : L.sc n ⟶ L.sc n := (shortComplexFunctor _ _ n).map (pL k)
  have hsurj : Function.Surjective (homologyMap f n) := by
    intro z
    obtain ⟨x, hx, rfl⟩ := classOf_surjective (L.sc n) z
    obtain ⟨k, a, ha⟩ := hevent n x
    have ha' : φ.τ₂ a = (β k).τ₂ x := ha
    have hpx := map_cycle _ _ (β k) x hx
    have hacycle : (K.sc n).g a = 0 := by
      apply hf ((ComplexShape.down ℕ).next n)
      have h := congrArg (fun g : (K.sc n).X₂ ⟶ (L.sc n).X₃ ↦ g a) φ.comm₂₃
      change (L.sc n).g (φ.τ₂ a) = φ.τ₃ ((K.sc n).g a) at h
      change φ.τ₃ ((K.sc n).g a) = φ.τ₃ 0
      rw [← h, ha', hpx, map_zero]
    refine ⟨classOf (K.sc n) a hacycle, ?_⟩
    calc
      homologyMap f n (classOf (K.sc n) a hacycle) = classOf (L.sc n) (φ.τ₂ a)
          (map_cycle _ _ φ a hacycle) := classOf_map _ _ φ a hacycle _
      _ = classOf (L.sc n) ((β k).τ₂ x) hpx := classOf_congr _ ha' _ _
      _ = ShortComplex.homologyMap (β k) (classOf (L.sc n) x hx) :=
        (classOf_map _ _ (β k) x hx hpx).symm
      _ = classOf (L.sc n) x hx := by
        change homologyMap (pL k) n _ = _
        rw [hL]
        rfl
  have hzero : ∀ z, homologyMap f n z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := classOf_surjective (K.sc n) z
    have hfx := map_cycle _ _ φ x hx
    have hz' : classOf (L.sc n) (φ.τ₂ x) hfx = 0 := by
      rw [← classOf_map _ _ φ x hx hfx]
      exact hz
    obtain ⟨b, hb⟩ := (classOf_eq_zero_iff (L.sc n) (φ.τ₂ x) hfx).mp hz'
    obtain ⟨k, a, ha⟩ := hevent ((ComplexShape.down ℕ).prev n) b
    have ha' : φ.τ₁ a = (β k).τ₁ b := ha
    have hprim : (K.sc n).f a = (α k).τ₂ x := by
      apply hf n
      have h₁ := congrArg (fun g : (K.sc n).X₁ ⟶ (L.sc n).X₂ ↦ g a) φ.comm₁₂
      have h₂ := congrArg (fun g : (L.sc n).X₁ ⟶ (L.sc n).X₂ ↦ g b) (β k).comm₁₂
      have h₃ := congrArg (fun g : K ⟶ L ↦ g.f n x) (hcomm k)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
      calc
        f.f n ((K.sc n).f a) = (L.sc n).f (φ.τ₁ a) := h₁.symm
        _ = (L.sc n).f ((β k).τ₁ b) := congrArg (L.sc n).f ha'
        _ = (β k).τ₂ ((L.sc n).f b) := h₂
        _ = (β k).τ₂ (φ.τ₂ x) := congrArg (β k).τ₂ hb
        _ = f.f n ((α k).τ₂ x) := h₃
    have hpzero : classOf (K.sc n) ((α k).τ₂ x) (map_cycle _ _ (α k) x hx) = 0 :=
      (classOf_eq_zero_iff _ _ _).mpr ⟨a, hprim⟩
    rw [← classOf_map _ _ (α k) x hx _] at hpzero
    change homologyMap (pK k) n (classOf (K.sc n) x hx) = 0 at hpzero
    rw [hK] at hpzero
    exact hpzero
  have hinj : Function.Injective (homologyMap f n) := by
    intro x y hxy
    have h := hzero (x - y) (by simp only [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  exact (ConcreteCategory.isIso_iff_bijective (homologyMap f n)).mpr ⟨hinj, hsurj⟩

end Complex

end HodgeConjecture.ChainHomologyClasses
