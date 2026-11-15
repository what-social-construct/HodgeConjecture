module

public import HodgeConjecture.Cycles.ProjectiveLineProductChowClasses
public import HodgeConjecture.Geometry.ProjectiveLineProductAffineDimension
public import HodgeConjecture.Cycles.AffinePrimeDimension
public import Mathlib.Data.ENat.Monoid

/-!
# Codimension of the zero-coordinate fibers in P¹ × P¹

The generic point of each integral coordinate fiber lifts to the affine
product chart. In that chart the finite-type prime dimension formula
computes its codimension from the fiber's proved dimension one and the
affine product's proved dimension two.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductFiberCodimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeCycles TensorProduct
open HodgeConjecture.ProjectiveLineProductChow

universe u

variable (k : Type u) [Field k]

/-- Evaluation at zero as an actual affine-scheme point. -/
def affineZeroPoint : Spec (.of k) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))

@[simp] theorem affineZeroPoint_over :
    affineZeroPoint k ≫ projectiveLineAffineStructureMorphism k = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of k) using 1
  congr 1
  ext c
  exact Polynomial.eval_C

/-- The zero-first-coordinate map, restricted to the affine chart of its
free second coordinate, lands in the affine product chart. -/
def zeroFirstAffineLift :
    Spec (.of (Polynomial k)) ⟶ projectiveLineAffineProduct k :=
  pullback.lift
    (projectiveLineAffineStructureMorphism k ≫ affineZeroPoint k)
    (𝟙 (Spec (.of (Polynomial k)))) (by
      rw [Category.assoc, affineZeroPoint_over, Category.comp_id, Category.id_comp])

/-- The restricted affine fiber map agrees with the actual global
zero-first-coordinate section. -/
theorem zeroFirstAffineLift_map :
    zeroFirstAffineLift k ≫ projectiveLineAffineProductMap k =
      projectiveLineXChart k ≫ projectiveLineProductZeroFirst k := by
  apply projectiveLineProduct_hom_ext k
  · rw [Category.assoc, projectiveLineAffineProductMap_fst,
      ← Category.assoc, zeroFirstAffineLift, pullback.lift_fst]
    conv_rhs => rw [Category.assoc, projectiveLineProductZeroFirst_fst,
      ← Category.assoc, projectiveLineXChart_comp_structureMorphism]
    rfl
  · rw [Category.assoc, projectiveLineAffineProductMap_snd,
      ← Category.assoc, zeroFirstAffineLift, pullback.lift_snd]
    conv_rhs => rw [Category.assoc, projectiveLineProductZeroFirst_snd]
    simp

/-- The same factorization expressed in tensor-product affine coordinates. -/
theorem zeroFirstAffineChart_map :
    zeroFirstAffineLift k ≫ (projectiveLineAffineProductIso k).hom ≫
      projectiveLineProductAffineChart k =
        projectiveLineXChart k ≫ projectiveLineProductZeroFirst k := by
  simpa [projectiveLineProductAffineChart, Category.assoc] using
    zeroFirstAffineLift_map k

/-- An explicit affine-chart preimage of the first fiber's generic point. -/
def firstAffineGenericPoint : Spec (.of (Polynomial k ⊗[k] Polynomial k)) :=
  (zeroFirstAffineLift k ≫ (projectiveLineAffineProductIso k).hom).base
    (genericPoint (Spec (.of (Polynomial k))))

theorem firstAffineGenericPoint_map :
    (projectiveLineProductAffineChart k).base (firstAffineGenericPoint k) =
      ambientGenericPoint (projectiveLineProductZeroFirstCarrier k) := by
  change ((zeroFirstAffineLift k ≫ (projectiveLineAffineProductIso k).hom) ≫
    projectiveLineProductAffineChart k).base
      (genericPoint (Spec (.of (Polynomial k)))) = _
  rw [Category.assoc, zeroFirstAffineChart_map]
  change (projectiveLineProductZeroFirst k).base
    ((projectiveLineXChart k).base (genericPoint (Spec (.of (Polynomial k))))) = _
  rw [projectiveLineXChart_genericPoint_eq,
    projectiveLineProductZeroFirstCarrier_eq_candidate]
  simp [HodgeConjecture.ProjectiveLineProductIntegralCandidates.firstZeroCarrier]

/-- The affine product coordinate algebra is a domain. -/
instance affineProduct_isDomain :
    IsDomain (Polynomial k ⊗[k] Polynomial k) :=
  (projectiveLineAffineProductRingEquiv k).toRingEquiv.toMulEquiv.isDomain _

/-- The same coordinate algebra is finite type over the ground field. -/
instance affineProduct_finiteType :
    Algebra.FiniteType k (Polynomial k ⊗[k] Polynomial k) :=
  Algebra.FiniteType.equiv inferInstance (projectiveLineAffineProductRingEquiv k).symm

/-- The explicit affine preimage of the first zero-fiber generic point is
height one, derived from the prime dimension formula. -/
theorem firstAffineGenericPoint_height_one :
    (firstAffineGenericPoint k).asIdeal.height = 1 := by
  let B := Polynomial k ⊗[k] Polynomial k
  let q : Spec (.of B) := firstAffineGenericPoint k
  have hdegree : dimensionFunction k
      (ambientGenericPoint (projectiveLineProductZeroFirstCarrier k)) = 1 := by
    simpa only [supportDegree] using firstCarrier_supportDegree_one k
  have hheight : Order.height (α := (Spec (.of B) : Scheme)) q = (1 : ℕ∞) := by
    rw [point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType k
      (projectiveLineProductStructureMorphism k)
      (projectiveLineProductAffineChart k) q,
      firstAffineGenericPoint_map,
      point_height_eq_ofLocallyOfFiniteType k (projectiveLineProduct k)
        (projectiveLineProductStructureMorphism k)]
    change ((dimensionFunction k
      (ambientGenericPoint (projectiveLineProductZeroFirstCarrier k))).toNat : ℕ∞) = 1
    rw [hdegree]
    norm_num
  have hquot : ringKrullDim (B ⧸ q.asIdeal) = (1 : WithBot ℕ∞) := by
    rw [← prime_coheight_eq_quotientDim B q,
      ← spec_point_height_eq_prime_coheight B q]
    exact_mod_cast hheight
  letI : q.asIdeal.IsPrime := q.isPrime
  have hsum := height_add_quotient_dimension_eq k B q.asIdeal
  rw [hquot, projectiveLineAffineProduct_ringKrullDim k] at hsum
  have hcast : (q.asIdeal.height : WithBot ℕ∞) = 1 := by
    apply (ENat.WithBot.add_one_cancel).mp
    calc
      (q.asIdeal.height : WithBot ℕ∞) + 1 = 2 := hsum
      _ = (1 : WithBot ℕ∞) + 1 := by norm_num
  exact_mod_cast hcast

/-- The first actual zero-coordinate fiber has topological codimension one. -/
theorem firstZeroCarrier_codimension_one :
    supportCodimension (projectiveLineProductZeroFirstCarrier k) = 1 := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight,
    ← firstAffineGenericPoint_map,
    ← point_coheight_eq_of_isOpenImmersion
      (projectiveLineProductAffineChart k) (firstAffineGenericPoint k),
    ← idealHeight_eq_coheight]
  exact firstAffineGenericPoint_height_one k

/-- The zero-second-coordinate map, restricted to the affine chart of its
free first coordinate, lands in the affine product chart. -/
def zeroSecondAffineLift :
    Spec (.of (Polynomial k)) ⟶ projectiveLineAffineProduct k :=
  pullback.lift
    (𝟙 (Spec (.of (Polynomial k))))
    (projectiveLineAffineStructureMorphism k ≫ affineZeroPoint k) (by
      rw [Category.id_comp, Category.assoc, affineZeroPoint_over, Category.comp_id])

theorem zeroSecondAffineLift_map :
    zeroSecondAffineLift k ≫ projectiveLineAffineProductMap k =
      projectiveLineXChart k ≫ projectiveLineProductZeroSecond k := by
  apply projectiveLineProduct_hom_ext k
  · rw [Category.assoc, projectiveLineAffineProductMap_fst,
      ← Category.assoc, zeroSecondAffineLift, pullback.lift_fst]
    conv_rhs => rw [Category.assoc, projectiveLineProductZeroSecond_fst]
    simp
  · rw [Category.assoc, projectiveLineAffineProductMap_snd,
      ← Category.assoc, zeroSecondAffineLift, pullback.lift_snd]
    conv_rhs => rw [Category.assoc, projectiveLineProductZeroSecond_snd,
      ← Category.assoc, projectiveLineXChart_comp_structureMorphism]
    rfl

theorem zeroSecondAffineChart_map :
    zeroSecondAffineLift k ≫ (projectiveLineAffineProductIso k).hom ≫
      projectiveLineProductAffineChart k =
        projectiveLineXChart k ≫ projectiveLineProductZeroSecond k := by
  simpa [projectiveLineProductAffineChart, Category.assoc] using
    zeroSecondAffineLift_map k

/-- An explicit affine-chart preimage of the second fiber's generic point. -/
def secondAffineGenericPoint : Spec (.of (Polynomial k ⊗[k] Polynomial k)) :=
  (zeroSecondAffineLift k ≫ (projectiveLineAffineProductIso k).hom).base
    (genericPoint (Spec (.of (Polynomial k))))

theorem secondAffineGenericPoint_map :
    (projectiveLineProductAffineChart k).base (secondAffineGenericPoint k) =
      ambientGenericPoint (projectiveLineProductZeroSecondCarrier k) := by
  change ((zeroSecondAffineLift k ≫ (projectiveLineAffineProductIso k).hom) ≫
    projectiveLineProductAffineChart k).base
      (genericPoint (Spec (.of (Polynomial k)))) = _
  rw [Category.assoc, zeroSecondAffineChart_map]
  change (projectiveLineProductZeroSecond k).base
    ((projectiveLineXChart k).base (genericPoint (Spec (.of (Polynomial k))))) = _
  rw [projectiveLineXChart_genericPoint_eq,
    projectiveLineProductZeroSecondCarrier_eq_candidate]
  simp [HodgeConjecture.ProjectiveLineProductIntegralCandidates.secondZeroCarrier]

/-- The explicit affine preimage of the second zero-fiber generic point is
height one, by the same prime dimension formula. -/
theorem secondAffineGenericPoint_height_one :
    (secondAffineGenericPoint k).asIdeal.height = 1 := by
  let B := Polynomial k ⊗[k] Polynomial k
  let q : Spec (.of B) := secondAffineGenericPoint k
  have hdegree : dimensionFunction k
      (ambientGenericPoint (projectiveLineProductZeroSecondCarrier k)) = 1 := by
    simpa only [supportDegree] using secondCarrier_supportDegree_one k
  have hheight : Order.height (α := (Spec (.of B) : Scheme)) q = (1 : ℕ∞) := by
    rw [point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType k
      (projectiveLineProductStructureMorphism k)
      (projectiveLineProductAffineChart k) q,
      secondAffineGenericPoint_map,
      point_height_eq_ofLocallyOfFiniteType k (projectiveLineProduct k)
        (projectiveLineProductStructureMorphism k)]
    change ((dimensionFunction k
      (ambientGenericPoint (projectiveLineProductZeroSecondCarrier k))).toNat : ℕ∞) = 1
    rw [hdegree]
    norm_num
  have hquot : ringKrullDim (B ⧸ q.asIdeal) = (1 : WithBot ℕ∞) := by
    rw [← prime_coheight_eq_quotientDim B q,
      ← spec_point_height_eq_prime_coheight B q]
    exact_mod_cast hheight
  letI : q.asIdeal.IsPrime := q.isPrime
  have hsum := height_add_quotient_dimension_eq k B q.asIdeal
  rw [hquot, projectiveLineAffineProduct_ringKrullDim k] at hsum
  have hcast : (q.asIdeal.height : WithBot ℕ∞) = 1 := by
    apply (ENat.WithBot.add_one_cancel).mp
    calc
      (q.asIdeal.height : WithBot ℕ∞) + 1 = 2 := hsum
      _ = (1 : WithBot ℕ∞) + 1 := by norm_num
  exact_mod_cast hcast

/-- The second actual zero-coordinate fiber has topological codimension one. -/
theorem secondZeroCarrier_codimension_one :
    supportCodimension (projectiveLineProductZeroSecondCarrier k) = 1 := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight,
    ← secondAffineGenericPoint_map,
    ← point_coheight_eq_of_isOpenImmersion
      (projectiveLineProductAffineChart k) (secondAffineGenericPoint k),
    ← idealHeight_eq_coheight]
  exact secondAffineGenericPoint_height_one k

end HodgeConjecture.ProjectiveLineProductFiberCodimension

end
