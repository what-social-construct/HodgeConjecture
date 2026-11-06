module

public import HodgeConjecture.Correspondence.GroupAlgebraProjector
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RingTheory.Idempotents

@[expose] public section

/-!
# Subgroup Hecke corners and double-coset correspondences

Let a group `G` act on `X/S` by deck transformations and let `H ≤ G` be
finite.  This file places the normalized subgroup average

`e_H = |H|⁻¹ ∑ h : H, [h]`

inside the ambient rational group algebra `ℚ[G]` and forms the honest
unital corner ring `e_H ℚ[G] e_H`.  Its unit is `e_H`, as provided by
Mathlib's `IsIdempotentElem.Corner`; it is not the ambient unit of `ℚ[G]`.

The element `e_H [g] e_H` depends only on the double coset `H g H`, so it
descends to a function from `H \ G / H`.  The graph-correspondence algebra
map then restricts to a unital ring homomorphism between corners.  Its target
unit is the previously defined `subgroupAveragingProjector`.

The normalization matters: `heckeElement H g` is `e_H [g] e_H`, not the raw
characteristic sum of the finite set `H g H`.  The two differ by the usual
stabilizer-dependent nonzero rational factor.  We do not claim here that the
double-coset operators form a basis, compute their structure constants, or
make the corner commutative.  No normality assumption on `H` is used, and
`G` itself need not be finite.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w

namespace SchemeCorrespondence

section CornerAlgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable {e : A} (he : IsIdempotentElem e)

/-- The ambient scalar-stable additive subspace underlying an idempotent corner. -/
def cornerSubmodule (e : A) : Submodule R A where
  carrier := Set.range (e * · * e)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp only [mul_add, add_mul]⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, by
      change e * (r • a) * e = r • (e * a * e)
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]⟩

/-- The corner inherits the ambient module structure. -/
noncomputable instance cornerModule : Module R he.Corner :=
  inferInstanceAs (Module R (cornerSubmodule (R := R) (A := A) e))

/--
An idempotent corner in an `R`-algebra is itself an `R`-algebra.  Its scalar
map sends `r` to `r • e`, because the corner unit is `e`.
-/
noncomputable instance cornerAlgebra : Algebra R he.Corner :=
  Algebra.ofModule
    (fun r x y ↦ by
      apply Subtype.ext
      change (r • x.1) * y.1 = r • (x.1 * y.1)
      exact Algebra.smul_mul_assoc r x.1 y.1)
    (fun r x y ↦ by
      apply Subtype.ext
      change x.1 * (r • y.1) = r • (x.1 * y.1)
      exact Algebra.mul_smul_comm r x.1 y.1)

@[simp]
theorem corner_algebraMap_coe (r : R) :
    ((algebraMap R he.Corner r).1 : A) = r • e := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

end CornerAlgebra

section CornerMap

variable {A : Type v} {B : Type w} [Ring A] [Ring B]
variable {e : A} (he : IsIdempotentElem e)

/--
A unital ring homomorphism carries the corner of an idempotent to the corner
of its image.  Passing to the target corner is essential: the composite from
the source corner to the full target ring generally sends `1 = e` to `f e`,
not to the ambient target unit.
-/
def cornerRingHom (f : A →+* B) :
    he.Corner →+* (he.map f).Corner where
  toFun x :=
    ⟨f x.1, by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨f a, by simpa only [map_mul] using congrArg f ha⟩⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    exact f.map_mul x.1 y.1
  map_zero' := by
    apply Subtype.ext
    exact f.map_zero
  map_add' x y := by
    apply Subtype.ext
    exact f.map_add x.1 y.1

@[simp]
theorem cornerRingHom_apply_coe (f : A →+* B) (x : he.Corner) :
    (cornerRingHom he f x).1 = f x.1 :=
  rfl

end CornerMap

section HeckeCorner

variable {G : Type v} [Group G]
variable (H : Subgroup G)

/-- Inclusion of the subgroup algebra into the ambient group algebra. -/
noncomputable def subgroupAlgebraMap :
    MonoidAlgebra ℚ H →ₐ[ℚ] MonoidAlgebra ℚ G :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ H.subtype

@[simp]
theorem subgroupAlgebraMap_single (h : H) :
    subgroupAlgebraMap H (MonoidAlgebra.single h 1) =
      MonoidAlgebra.single (h : G) 1 := by
  simp [subgroupAlgebraMap]

variable [Fintype H]

/-- The normalized subgroup average `e_H`, viewed in `ℚ[G]`. -/
noncomputable def subgroupAverage : MonoidAlgebra ℚ G :=
  subgroupAlgebraMap H (finiteGroupAverage H)

/-- The ambient subgroup average is idempotent. -/
theorem subgroupAverage_isIdempotent :
    IsIdempotentElem (subgroupAverage H) :=
  (finiteGroupAverage_isIdempotent H).map (subgroupAlgebraMap H)

/-- A subgroup basis element fixes `e_H` on the left. -/
@[simp]
theorem single_mul_subgroupAverage (h : H) :
    MonoidAlgebra.single (h : G) 1 * subgroupAverage H =
      subgroupAverage H := by
  rw [← subgroupAlgebraMap_single H h, subgroupAverage,
    ← map_mul, single_mul_finiteGroupAverage]

/-- A subgroup basis element fixes `e_H` on the right. -/
@[simp]
theorem subgroupAverage_mul_single (h : H) :
    subgroupAverage H * MonoidAlgebra.single (h : G) 1 =
      subgroupAverage H := by
  rw [← subgroupAlgebraMap_single H h, subgroupAverage,
    ← map_mul, finiteGroupAverage_mul_single]

/-- The subgroup Hecke corner `e_H ℚ[G] e_H`, with unit `e_H`. -/
abbrev SubgroupHeckeAlgebra :=
  (subgroupAverage_isIdempotent H).Corner

/-- The normalized Hecke operator represented by `g`, namely `e_H [g] e_H`. -/
noncomputable def heckeElement (g : G) : SubgroupHeckeAlgebra H :=
  ⟨subgroupAverage H * MonoidAlgebra.single g 1 * subgroupAverage H,
    ⟨MonoidAlgebra.single g 1, rfl⟩⟩

/-- `e_H [g] e_H` depends only on the double coset `H g H`. -/
theorem heckeElement_eq_of_rel {a b : G}
    (hab : DoubleCoset.setoid (H : Set G) H a b) :
    heckeElement H a = heckeElement H b := by
  obtain ⟨h, hh, k, hk, hb⟩ := DoubleCoset.rel_iff.mp hab
  subst b
  apply Subtype.ext
  change
    subgroupAverage H * MonoidAlgebra.single a 1 * subgroupAverage H =
      subgroupAverage H * MonoidAlgebra.single (h * a * k) 1 * subgroupAverage H
  have hsingle :
      (MonoidAlgebra.single (h * a * k) (1 : ℚ) : MonoidAlgebra ℚ G) =
        MonoidAlgebra.single h 1 * MonoidAlgebra.single a 1 *
          MonoidAlgebra.single k 1 := by simp
  calc
    subgroupAverage H * MonoidAlgebra.single a 1 * subgroupAverage H =
        (subgroupAverage H * MonoidAlgebra.single h 1) *
          MonoidAlgebra.single a 1 *
          (MonoidAlgebra.single k 1 * subgroupAverage H) := by
            rw [subgroupAverage_mul_single H ⟨h, hh⟩,
              single_mul_subgroupAverage H ⟨k, hk⟩]
    _ = subgroupAverage H *
          (MonoidAlgebra.single h 1 * MonoidAlgebra.single a 1 *
            MonoidAlgebra.single k 1) * subgroupAverage H := by
            simp only [mul_assoc]
    _ = subgroupAverage H * MonoidAlgebra.single (h * a * k) 1 *
          subgroupAverage H :=
      congrArg (fun x : MonoidAlgebra ℚ G ↦
        subgroupAverage H * x * subgroupAverage H) hsingle.symm

/-- A double coset determines a normalized Hecke operator in the corner. -/
noncomputable def doubleCosetOperator :
    DoubleCoset.Quotient (H : Set G) H → SubgroupHeckeAlgebra H :=
  Quotient.lift (heckeElement H) fun _ _ hab ↦
    heckeElement_eq_of_rel H hab

@[simp]
theorem doubleCosetOperator_mk (g : G) :
    doubleCosetOperator H (DoubleCoset.mk H H g) = heckeElement H g :=
  rfl

end HeckeCorner

section CorrespondenceHeckeCorner

variable {S X : Scheme.{u}} (pX : X ⟶ S)
variable {G : Type v} [Group G]
variable (H : Subgroup G) [Fintype H]
variable (α : FiniteDeckAction pX G)

/-- The corner cut out by the correspondence image of `e_H`. -/
abbrev CorrespondenceHeckeAlgebra :=
  ((subgroupAverage_isIdempotent H).map
    (α.toFiniteEtaleAlgebra pX)).Corner

/--
The graph algebra map restricted from the group-algebra Hecke corner to the
corner cut out by the subgroup averaging correspondence.
-/
noncomputable def heckeToCorrespondenceCorner :
    SubgroupHeckeAlgebra H →+* CorrespondenceHeckeAlgebra pX H α :=
  cornerRingHom (subgroupAverage_isIdempotent H)
    (α.toFiniteEtaleAlgebra pX).toRingHom

@[simp]
theorem heckeToCorrespondenceCorner_apply_coe
    (x : SubgroupHeckeAlgebra H) :
    (heckeToCorrespondenceCorner pX H α x).1 =
      α.toFiniteEtaleAlgebra pX x.1 :=
  rfl

/-- The ambient image of `e_H` is the existing subgroup averaging projector. -/
theorem subgroupAverage_toFiniteEtaleAlgebra :
    α.toFiniteEtaleAlgebra pX (subgroupAverage H) =
      subgroupAveragingProjector pX H α := by
  change
    ((α.toFiniteEtaleAlgebra pX).comp (subgroupAlgebraMap H))
        (finiteGroupAverage H) =
      (α.restrict pX H).toFiniteEtaleAlgebra pX
        (finiteGroupAverage H)
  congr 1
  ext h
  simp

/--
Under graph-correspondence transport, `e_H [g] e_H` is the expected
projector--graph--projector sandwich.
-/
theorem heckeElement_toCorrespondenceCorner_coe (g : G) :
    (heckeToCorrespondenceCorner pX H α (heckeElement H g)).1 =
      subgroupAveragingProjector pX H α *
        finiteEtaleOfScheme
          (graph pX (α g))
          (graph_hasFiniteEtaleLegs pX (α g)) *
        subgroupAveragingProjector pX H α := by
  change
    α.toFiniteEtaleAlgebra pX
        (subgroupAverage H * MonoidAlgebra.single g 1 * subgroupAverage H) = _
  rw [map_mul, map_mul, α.toFiniteEtaleAlgebra_single,
    subgroupAverage_toFiniteEtaleAlgebra]

/-!
## Idempotents in the Hecke corner

An idempotent of the corner is, after forgetting the subtype, an idempotent
of the ambient group algebra.  It therefore transports through the graph
algebra map to a correspondence idempotent.  The constructors below expose
both the operator induced by that correspondence and a separately prescribed
operator target.
-/

/-- Forgetting the corner subtype preserves the idempotence equation. -/
theorem heckeIdempotent_coe_isIdempotent
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q) :
    IsIdempotentElem (q.1 : MonoidAlgebra ℚ G) := by
  change q.1 * q.1 = q.1
  exact congrArg Subtype.val hq

/-- An arbitrary element of the Hecke corner transported to correspondences. -/
noncomputable def heckeCorrespondence
    (q : SubgroupHeckeAlgebra H) :
    FiniteEtaleFreeAlgebra pX :=
  groupAlgebraCorrespondence pX α q.1

/-- The ambient correspondence agrees with the value of the corner map. -/
@[simp]
theorem heckeCorrespondence_eq_cornerImage_coe
    (q : SubgroupHeckeAlgebra H) :
    heckeCorrespondence pX H α q =
      (heckeToCorrespondenceCorner pX H α q).1 :=
  rfl

/-- An idempotent remains idempotent inside the correspondence target corner. -/
theorem heckeCornerImage_isIdempotent
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q) :
    IsIdempotentElem (heckeToCorrespondenceCorner pX H α q) :=
  hq.map (heckeToCorrespondenceCorner pX H α)

/-- An idempotent of the Hecke corner gives an ambient correspondence idempotent. -/
theorem heckeCorrespondence_isIdempotent
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q) :
    IsIdempotentElem (heckeCorrespondence pX H α q) :=
  groupAlgebraCorrespondence_isIdempotent
    pX α q.1 (heckeIdempotent_coe_isIdempotent H q hq)

section Realization

variable {V : Type w} [AddCommGroup V] [Module ℚ V]

/--
Canonical algebraic lift of the operator induced by an idempotent in the
Hecke corner.
-/
noncomputable def heckeProjectorLift
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) V) :
    AlgebraicProjectorLift ρ
      (ρ.action (heckeCorrespondence pX H α q)) :=
  groupAlgebraProjectorLift pX α q.1
    (heckeIdempotent_coe_isIdempotent H q hq) ρ

/--
Lift a separately prescribed operator using an idempotent in the Hecke
corner.  The equality `hrealizes` is explicit, so the target is not defined
circularly from the correspondence.
-/
noncomputable def prescribedHeckeProjectorLift
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) V)
    (P : Module.End ℚ V)
    (hrealizes :
      ρ.action (heckeCorrespondence pX H α q) = P) :
    AlgebraicProjectorLift ρ P :=
  prescribedGroupAlgebraProjectorLift pX α q.1
    (heckeIdempotent_coe_isIdempotent H q hq) ρ P hrealizes

@[simp]
theorem prescribedHeckeProjectorLift_projector
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) V)
    (P : Module.End ℚ V)
    (hrealizes :
      ρ.action (heckeCorrespondence pX H α q) = P) :
    (prescribedHeckeProjectorLift
      pX H α q hq ρ P hrealizes).projector =
        heckeCorrespondence pX H α q :=
  rfl

/-- The prescribed Hecke lift realizes exactly the supplied target operator. -/
theorem prescribedHeckeProjectorLift_realizes
    (q : SubgroupHeckeAlgebra H)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) V)
    (P : Module.End ℚ V)
    (hrealizes :
      ρ.action (heckeCorrespondence pX H α q) = P) :
    ρ.action
        ((prescribedHeckeProjectorLift
          pX H α q hq ρ P hrealizes).projector) = P :=
  hrealizes

end Realization

end CorrespondenceHeckeCorner

end SchemeCorrespondence

end

end HodgeConjecture
