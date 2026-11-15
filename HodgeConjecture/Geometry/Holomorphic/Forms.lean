module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Holomorphic differential forms on coordinate opens

The coefficients are native continuous complex alternating maps. Sections
are Mathlib's bundled complex C∞ maps on an open subset of a normed space.
The differential is the native exterior derivative of a local extension;
locality makes it independent of that extension and compatible with
restriction. No analytic atlas on a general scheme is assumed here.

The auxiliary local-extension argument adapts the extension-by-zero
helper in Axiom Weil, revision `27cdb2049be62ee2911429b47f54774078450e32`,
`Weil/Geometry/Manifold/Sheaf/HolomorphicCohomology.lean` (Apache-2.0),
generalized to the native coefficient spaces. See `third_party/axiom-weil/LICENSE`.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open CategoryTheory TopologicalSpace Filter
open scoped Manifold ContDiff Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Native coefficient space of complex differential forms. -/
abbrev Coeff (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) :=
  E [⋀^Fin n]→L[ℂ] ℂ

/-- Holomorphic forms in the given coordinates, using the original bundled maps. -/
abbrev Sections (U : Opens E) (n : ℕ) := C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, Coeff E n), Coeff E n⟯

section Extension

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- An auxiliary extension for computing local derivatives; not asserted holomorphic off U. -/
def extend {U : Opens E} (f : U → V) (x : E) : V := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else 0

omit [NormedSpace ℂ E] [NormedSpace ℂ V] in
@[simp]
theorem extend_of_mem {U : Opens E} (f : U → V) (x : U) : extend f x = f x := by
  simp [extend]

omit [NormedSpace ℂ E] [NormedSpace ℂ V] in
theorem extend_eventuallyEq {U : Opens E} (f : U → V) {x : E} (hx : x ∈ U)
    (g : E → V) (h : ∀ y : U, f y = g y) : extend f =ᶠ[𝓝 x] g := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (extend_of_mem f ⟨y, hy⟩).trans (h ⟨y, hy⟩)

theorem contDiffAt_extend {U : Opens E}
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, V), V⟯) (x : U) :
    ContDiffAt ℂ ∞ (extend f) x := by
  apply ContMDiffAt.contDiffAt
  apply (contMDiffAt_subtype_iff (x := x)).mp
  simpa only [extend_of_mem] using f.contMDiff x

theorem contMDiff_restrict {U : Opens E} {g : E → V}
    (h : ∀ x ∈ U, ContDiffAt ℂ ∞ g x) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, V) ∞ (fun x : U ↦ g x) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr (h x x.2).contMDiffAt

end Extension

/-- Restriction is the existing restriction of bundled complex smooth maps. -/
def restrict {U V : Opens E} (h : U ≤ V) (n : ℕ) : Sections V n →ₗ[ℂ] Sections U n where
  toFun f := ⟨fun x ↦ f (Set.inclusion h x), f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrict_apply {U V : Opens E} (h : U ≤ V) (n : ℕ) (f : Sections V n) (x : U) :
    restrict h n f x = f (Set.inclusion h x) := rfl

/-- The native exterior derivative is holomorphic near every point of the coordinate open. -/
theorem contDiffAt_extDeriv {U : Opens E} {n : ℕ} (f : Sections U n) (x : U) :
    ContDiffAt ℂ ∞ (extDeriv (extend f)) x := by
  have hd : ContDiffAt ℂ ∞ (fderiv ℂ (extend f)) (x : E) :=
    (contDiffAt_extend f x).fderiv_right (by simp)
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).contDiff.contDiffAt.comp (x : E) hd

/-- Exterior differentiation on actual holomorphic sections. -/
def differential (U : Opens E) (n : ℕ) : Sections U n →ₗ[ℂ] Sections U (n + 1) where
  toFun f := ⟨fun x ↦ extDeriv (extend f) x,
    contMDiff_restrict (fun x hx ↦ contDiffAt_extDeriv f ⟨x, hx⟩)⟩
  map_add' f g := by
    apply ContMDiffMap.ext
    intro x
    have he : extend (f + g) = extend f + extend g := by
      funext y
      by_cases hy : y ∈ U <;> simp [extend, hy]
    change extDeriv (extend (f + g)) x = _
    rw [he, extDeriv_add (contDiffAt_extend f x |>.differentiableAt (by simp))
      (contDiffAt_extend g x |>.differentiableAt (by simp))]
    rfl
  map_smul' c f := by
    apply ContMDiffMap.ext
    intro x
    have he : extend (c • f) = c • extend f := by
      funext y
      by_cases hy : y ∈ U <;> simp [extend, hy]
    change extDeriv (extend (c • f)) x = _
    rw [he, extDeriv_smul]
    rfl

@[simp]
theorem differential_apply (U : Opens E) (n : ℕ) (f : Sections U n) (x : U) :
    differential U n f x = extDeriv (extend f) x := rfl

/-- Locality identifies the differential with every genuine local extension. -/
theorem differential_eq_of_extension {U : Opens E} {n : ℕ} (f : Sections U n)
    (g : E → Coeff E n) (h : ∀ x : U, f x = g x) (x : U) :
    differential U n f x = extDeriv g x :=
  (extend_eventuallyEq f x.2 g h).extDeriv_eq

/-- The actual differential commutes with restriction. -/
theorem restrict_differential {U V : Opens E} (h : U ≤ V) (n : ℕ) (f : Sections V n) :
    restrict h (n + 1) (differential V n f) = differential U n (restrict h n f) := by
  apply ContMDiffMap.ext
  intro x
  symm
  apply differential_eq_of_extension _ (extend f)
  intro y
  exact (extend_of_mem f (Set.inclusion h y)).symm

/-- d² = 0 is inherited from the native analytic exterior derivative. -/
theorem differential_comp (U : Opens E) (n : ℕ) :
    (differential U (n + 1)).comp (differential U n) = 0 := by
  apply LinearMap.ext
  intro f
  apply ContMDiffMap.ext
  intro x
  change differential U (n + 1) (differential U n f) x = 0
  rw [differential_eq_of_extension (differential U n f) (extDeriv (extend f)) (fun _ ↦ rfl)]
  exact extDeriv_extDeriv_apply (contDiffAt_extend f x) (by simp)

end HodgeConjecture.HolomorphicForms
