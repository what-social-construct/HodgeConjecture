module

public import HodgeConjecture.Boundary.Normalization.NormalizationLocalization
public import HodgeConjecture.Boundary.Normalization.InvariantIntermediate
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

/-!
# Inertia and localization at fixed denominators

If a group fixes the denominators in a localization, its inertia group at a
prime is unchanged after extending that prime. This is the group comparison
needed when the normalization of a field extension is localized at a prime of
the base.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- Localizing at denominators fixed by a group preserves the inertia group
of a prime disjoint from those denominators. -/
theorem inertia_map_of_isLocalization_fixed
    {S T G : Type*}
    [CommRing S] [CommRing T] [Algebra S T]
    [Group G] [MulSemiringAction G S] [MulSemiringAction G T]
    (M : Submonoid S) [IsLocalization M T]
    (hfixed : ∀ (g : G) (m : M), g • (m : S) = m)
    (hequiv : ∀ (g : G) (x : S),
      g • algebraMap S T x = algebraMap S T (g • x))
    (Q : Ideal S) [Q.IsPrime]
    (hdisjoint : Disjoint (M : Set S) (Q : Set S)) :
    (Q.map (algebraMap S T)).inertia G = Q.inertia G := by
  let f : S →+* T := algebraMap S T
  let P : Ideal T := Q.map f
  have hPunder : P.under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M T (inferInstance : Q.IsPrime) hdisjoint
  ext g
  constructor
  · intro hg x
    have hx : f (g • x - x) ∈ P := by
      rw [map_sub, ← hequiv g x]
      exact (Ideal.mem_inertia.mp hg) (f x)
    rw [← hPunder]
    exact hx
  · intro hg y
    obtain ⟨⟨x, m⟩, hy⟩ := IsLocalization.surj M y
    have hmfixed : g • f (m : S) = f (m : S) := by
      rw [hequiv, hfixed]
    have hgy : (g • y) * f (m : S) = f (g • x) := by
      calc
        (g • y) * f (m : S) = (g • y) * (g • f (m : S)) := by rw [hmfixed]
        _ = g • (y * f (m : S)) := (smul_mul' g y (f (m : S))).symm
        _ = g • f x := by rw [hy]
        _ = f (g • x) := hequiv g x
    have hmul : (g • y - y) * f (m : S) ∈ P := by
      have hx : f (g • x - x) ∈ P := Ideal.mem_map_of_mem f (Ideal.mem_inertia.mp hg x)
      rw [sub_mul, hgy, hy, ← map_sub]
      exact hx
    have hmUnit : IsUnit (f (m : S)) := IsLocalization.map_units T m
    exact (P.unit_mul_mem_iff_mem hmUnit).mp (by simpa only [mul_comm] using hmul)

/-- The prime inertia group of a normal-closure normalization is preserved by
localizing the affine base away from the prime below it. The upstairs prime is
the image under the same-element normalization base-change map. -/
theorem normalization_inertia_map_of_isLocalization
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    (M : Submonoid B) [IsLocalization M C]
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime]
    (hdisjoint : Disjoint (M : Set B) (Q.under B : Set B)) :
    (Q.map
      (CollisionFoundations.normalizationBaseChangeMap
        (B := B) (C := C) (E := N)).toRingHom).inertia (N ≃ₐ[K] N) =
      Q.inertia (N ≃ₐ[K] N) := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let T := NormalClosureNormalizationRing (B := C) (N := N)
  let f := CollisionFoundations.normalizationBaseChangeMap
    (B := B) (C := C) (E := N)
  letI : Algebra S T := f.toAlgebra
  let MS := Algebra.algebraMapSubmonoid S M
  letI : IsLocalization MS T :=
    CollisionFoundations.normalizedCoordinateRing_isLocalization
      (B := B) (C := C) (E := N) M
  have hfixed : ∀ (σ : N ≃ₐ[K] N) (m : MS), σ • (m : S) = (m : S) := by
    intro σ m
    obtain ⟨b, hb, hbm⟩ := m.property
    rw [← hbm]
    change (normalClosureNormalizationRingEquiv (B := B) σ)
      (algebraMap B S b) = algebraMap B S b
    exact (normalClosureNormalizationRingEquiv (B := B) σ).commutes b
  have hequiv : ∀ (σ : N ≃ₐ[K] N) (x : S),
      σ • algebraMap S T x = algebraMap S T (σ • x) := by
    intro σ x
    apply Subtype.ext
    rfl
  have hMS : Disjoint (MS : Set S) (Q : Set S) := by
    rw [Set.disjoint_left]
    intro s hs hQ
    obtain ⟨b, hb, rfl⟩ := hs
    exact (Set.disjoint_left.mp hdisjoint) hb hQ
  exact inertia_map_of_isLocalization_fixed MS hfixed hequiv Q hMS

end

end HodgeConjecture.NormalizationInertia
