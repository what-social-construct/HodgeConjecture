module

public import HodgeConjecture.SheafCohomology.LinearSheaves
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

/-!
# The shared constant-sheaf lift

These are aliases for native constant (pre)sheaves and their actual
sheafification lift. Injectivity on nonempty opens proves that the lift
is a monomorphism. Coordinate and intrinsic augmentations share this proof.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SheafCohomology.ConstantLift

open CategoryTheory TopologicalSpace Opposite

universe u

variable (k : Type u) [CommRing k] (X : TopCat.{u})

abbrev presheaf : TopCat.Presheaf (ModuleCat.{u} k) X :=
  (Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of k k)

abbrev sheaf : TopCat.Sheaf (ModuleCat.{u} k) X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).obj
    (ModuleCat.of k k)

variable {k X} (F : TopCat.Sheaf (ModuleCat.{u} k) X) (f : presheaf k X ⟶ F.obj)

def lift : sheaf k X ⟶ F :=
  ObjectProperty.homMk (sheafifyLift _ f F.property)

theorem toSheafify_lift : toSheafify _ _ ≫ (lift F f).hom = f :=
  toSheafify_sheafifyLift _ _ _

theorem locallyInjective {P : TopCat.Presheaf (ModuleCat.{u} k) X}
    (g : presheaf k X ⟶ P)
    (hinj : ∀ U : Opens X, (U : Set X).Nonempty → Function.Injective (g.app (op U))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) g := by
  refine ⟨fun {U} a b hab ↦ ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  refine ⟨U.unop, 𝟙 _, ?_, hx⟩
  simp only [Presheaf.equalizerSieve_apply, op_id]
  exact hinj U.unop ⟨x, hx⟩ hab

/-- The same nonempty-open criterion for a sheafified presheaf augmentation. -/
theorem map_mono {P : TopCat.Presheaf (ModuleCat.{u} k) X}
    (g : presheaf k X ⟶ P)
    (hinj : ∀ U : Opens X, (U : Set X).Nonempty → Function.Injective (g.app (op U))) :
    Mono ((sheafification k X).map g) := by
  have : Sheaf.IsLocallyInjective ((sheafification k X).map g) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ g).mpr (locallyInjective g hinj)
  exact Sheaf.mono_of_isLocallyInjective _

theorem mono (hinj : ∀ U : Opens X, (U : Set X).Nonempty → Function.Injective (f.app (op U))) :
    Mono (lift F f) := by
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f :=
    locallyInjective f hinj
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (lift F f).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _
      (f₁ := toSheafify _ _) f (toSheafify_lift F f)
  exact Sheaf.mono_of_isLocallyInjective _

end HodgeConjecture.SheafCohomology.ConstantLift
