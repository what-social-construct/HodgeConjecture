/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Source: StacksFrontier/AlgebraicGeometry/Chow/RelativeCycles/ModuleSpecialization/StalkLengths.lean
Only stalk kernels of pullbacks and scheme fibers are retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.Cycles.PullbackStalk
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace HodgeConjecture.SchemeCycles

noncomputable section

private lemma injective_of_localization_of_isLocalHom {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] [IsLocalHom (algebraMap A B)] :
    Function.Injective (algebraMap A B) := by
  have hS : S ≤ IsUnit.submonoid A := fun s hs ↦
    isUnit_of_map_unit (algebraMap A B) s (IsLocalization.map_units B ⟨s, hs⟩)
  exact (IsLocalization.atUnits A S hS (S := B)).injective

private lemma ker_tensor_includeLeft {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hB : Function.Surjective (algebraMap R B)) :
    RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A) := by
  let I := RingHom.ker (algebraMap R B)
  let eB : (R ⧸ I) ≃ₐ[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B) hB
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB)
  have he (a : A) : e (Ideal.Quotient.mk _ a) = a ⊗ₜ[R] (1 : B) := by
    simp [e]
  ext a
  change (a ⊗ₜ[R] (1 : B)) = 0 ↔ _
  rw [← he a, ← map_zero e, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

private lemma ker_tensor_localization {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B]
    (hB : Function.Surjective (algebraMap R B))
    (φ : A ⊗[R] B →+* C)
    [IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom)]
    (S : Submonoid (A ⊗[R] B))
    (hφ : letI : Algebra (A ⊗[R] B) C := φ.toAlgebra; IsLocalization S C) :
    RingHom.ker (φ.comp Algebra.TensorProduct.includeLeftRingHom) =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A) := by
  let : Algebra (A ⊗[R] B) C := φ.toAlgebra
  let : IsLocalization S C := hφ
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) :=
    Algebra.TensorProduct.includeLeft_surjective A A hB
  have : IsLocalHom φ := ⟨by
    intro z hz
    obtain ⟨a, rfl⟩ := hsurj z
    exact (isUnit_of_map_unit (φ.comp Algebra.TensorProduct.includeLeftRingHom) a hz).map
      Algebra.TensorProduct.includeLeftRingHom⟩
  have hφinj : Function.Injective φ := injective_of_localization_of_isLocalHom S
  rw [RingHom.ker_comp_of_injective _ hφinj]
  exact ker_tensor_includeLeft hB

theorem pullback_fst_stalkMap_ker {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g]
    (x : (pullback f g).carrier) :
    let h : (pullback.fst f g ≫ f) x = (pullback.snd f g ≫ g) x :=
      congrArg (fun k : pullback f g ⟶ S ↦ k x) pullback.condition
    RingHom.ker ((pullback.fst f g).stalkMap x).hom =
      (RingHom.ker (eqToHom (congrArg S.presheaf.stalk h) ≫
        g.stalkMap (pullback.snd f g x)).hom).map
          (f.stalkMap (pullback.fst f g x)).hom := by
  dsimp only
  let h : (pullback.fst f g ≫ f) x = (pullback.snd f g ≫ g) x :=
    congrArg (fun k : pullback f g ⟶ S ↦ k x) pullback.condition
  let R := S.presheaf.stalk ((pullback.fst f g ≫ f) x)
  let A := X.presheaf.stalk (pullback.fst f g x)
  let B := Y.presheaf.stalk (pullback.snd f g x)
  let β : R ⟶ B := eqToHom (congrArg S.presheaf.stalk h) ≫
    g.stalkMap (pullback.snd f g x)
  let : Algebra R A := (f.stalkMap (pullback.fst f g x)).hom.toAlgebra
  let : Algebra R B := β.hom.toAlgebra
  have hβ : Function.Surjective β.hom :=
    (g.stalkMap_surjective _).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg S.presheaf.stalk h))).2
  obtain ⟨φ, hφl, hφr, T, hT⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g x
  change A ⊗[R] B →+* (pullback f g).presheaf.stalk x at φ
  change φ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
    ((pullback.fst f g).stalkMap x).hom at hφl
  have : IsLocalHom (φ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) := by
    rw [hφl]
    infer_instance
  have hk := ker_tensor_localization (R := R) (A := A) (B := B) hβ φ T hT
  rwa [hφl] at hk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

private lemma isField_stalk_spec_field (k : Type u) [Field k]
    (p : Spec (.of k)) : IsField ((Spec (.of k)).presheaf.stalk p) := by
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  exact (stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv.isField
    (Field.toIsField k)

lemma fiber_stalkMap_ker {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (x : f.fiber s) :
    RingHom.ker ((f.fiberι s).stalkMap x).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f (f.fiberι s x)))).map
        (f.stalkMap (f.fiberι s x)).hom := by
  let pY := f.fiberToSpecResidueField s
  let h : (f.fiberι s ≫ f) x = (pY ≫ S.fromSpecResidueField s) x :=
    congrArg (fun k : f.fiber s ⟶ S ↦ k x) pullback.condition
  let β : S.presheaf.stalk ((f.fiberι s ≫ f) x) ⟶ (Spec (S.residueField s)).presheaf.stalk (pY x) :=
    eqToHom (congrArg S.presheaf.stalk h) ≫ (S.fromSpecResidueField s).stalkMap (pY x)
  have hβ : Function.Surjective β.hom :=
    ((S.fromSpecResidueField s).stalkMap_surjective (pY x)).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg S.presheaf.stalk h))).2
  have hfield := isField_stalk_spec_field (S.residueField s) (pY x)
  let : Field ((Spec (S.residueField s)).presheaf.stalk (pY x)) := hfield.toField
  have : IsLocalHom (β.hom : _ →+* _) := IsLocalHom.of_surjective _ hβ
  have hβker : RingHom.ker β.hom = IsLocalRing.maximalIdeal _ := by
    ext a
    change β.hom a = 0 ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun ha hu ↦ not_isUnit_zero (ha ▸ hu.map β.hom), fun ha ↦ Classical.byContradiction
      fun hn ↦ ha (isUnit_of_map_unit β.hom a (isUnit_iff_ne_zero.mpr hn))⟩
  exact (pullback_fst_stalkMap_ker f (S.fromSpecResidueField s) x).trans
    (congrArg (Ideal.map _) hβker)


end

end HodgeConjecture.SchemeCycles
