module

public import HodgeConjecture.SheafCohomology.AffineVanishing

@[expose] public section

/-!
# Affine acyclicity with an independently chosen coefficient category

The standard-cover proof of affine vanishing depends on the underlying
abelian presheaf of the coefficient object. This file transports that
calculation through an actual presheaf isomorphism and proves the result
for the right derived sections functor of the given coefficient category.
In particular it applies to the underlying abelian sheaf of an actual
quasi-coherent module, independently of its module-valued cohomology.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace HodgeConjecture.SheafCohomology

open Cohomology.Basis Cohomology.BasisCycles

noncomputable section

universe u v w

/-- Injective abelian sheaves have surjective restriction maps, hence their
positive-degree Čech cohomology vanishes. -/
theorem cechAcyclicInjectives_identity (X : Type u) [TopologicalSpace X] :
    CechAcyclicInjectives (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) := by
  intro A hA κ Y q
  let : Injective A := hA
  let A' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) := A
  have : A'.IsFlasque :=
    { epi := fun {U V} i => by
        rw [AddCommGrpCat.epi_iff_surjective]
        exact Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
          A' (leOfHom i.unop) }
  apply cechSurj_of_uliftFamily Y (abPresheaf (𝟭 _) A) q
  rw [cechSurj_iff_isZero_homology]
  exact Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque A'
    (⨆ i, (uliftFamily Y : ULift.{u} κ → Opens X) i)
    (uliftFamily Y : ULift.{u} κ → Opens X) rfl (q + 1) (Nat.succ_pos q)

variable (X : Scheme.{u})
  {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- A coefficient object whose actual underlying abelian presheaf is that
of a quasi-coherent module is acyclic for its own derived sections functor
on every affine open. -/
theorem isZero_coefficientCohomology_of_isAffineOpen
    (hacyc : CechAcyclicInjectives T) (A : 𝒜) (F : X.Modules) [F.IsQuasicoherent]
    (e : abPresheaf T A ≅ F.presheaf)
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : 0 < n) :
    IsZero (Hobj T U n A) := by
  refine isZero_Hobj_of_cech_isZero_on_basis T hacyc A X.affineOpens
    X.isBasis_affineOpens (Cohomology.Cech.standardCovers X)
    (Cohomology.Cech.affineOpens_of_mem_standardCovers)
    (fun _ hV W hWV => Cohomology.Cech.exists_mem_standardCovers_refines hV W hWV)
    (fun C hC q hq => ?_) U hU n hn
  let h := Cohomology.Cech.cechCohomologyIsZero_of_mem_standardCovers F C hC q hq
  exact h.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).mapIso
    ((cechComplexFunctor C.obj).mapIso e))

/-- Affine acyclicity of the underlying abelian sheaf of a quasi-coherent
module, computed using injective abelian sheaves. -/
theorem isZero_abelianCohomology_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : 0 < n) :
    IsZero (Hobj (𝟭 _) U n ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)) :=
  isZero_coefficientCohomology_of_isAffineOpen X (𝟭 _)
    (cechAcyclicInjectives_identity X) _ F (Iso.refl _) U hU n hn

end

end HodgeConjecture.SheafCohomology
