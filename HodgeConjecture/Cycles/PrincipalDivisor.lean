import HodgeConjecture.Cycles.DivisorFiniteness

/-!
# Principal divisors in the existing finite-cycle module

For an integral locally Noetherian quasi-compact scheme, the proved
finiteness of nonzero local orders assembles the principal divisor as a
finite integral cycle. Its coefficient at an actual prime divisor is the
existing signed local order; all other integral generators have coefficient
zero. The construction embeds the prime-divisor subtype into the existing
integral closed-subscheme index, without introducing another cycle module.

Products of nonzero rational functions give sums of these cycles. This is
an ungraded principal-divisor construction; no dimension-function grading,
rational-equivalence relation, or Chow quotient is imposed here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry

noncomputable section

universe u

/-- The principal divisor of an actual nonzero rational function, assembled
in the existing cycle module using the proved finite coefficient support. -/
def principalDivisor (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) : Cycles X ℤ :=
  Finsupp.embDomain (Function.Embedding.subtype
    (fun Z : IntegralClosedSubscheme X ↦ supportCodimension Z = 1))
    (Finsupp.ofSupportFinite (fun Z : PrimeDivisor X ↦ primeDivisorOrder X Z f)
      (finite_primeDivisorOrder_support X f))

/-- The coefficient of an actual prime divisor is its existing local order. -/
@[simp]
theorem principalDivisor_apply_prime (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    principalDivisor X f Z.val = primeDivisorOrder X Z f := by
  exact Finsupp.embDomain_apply _ _ Z

/-- Integral generators outside codimension one have zero coefficient. -/
@[simp]
theorem principalDivisor_apply_of_not_prime (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) (Z : IntegralClosedSubscheme X)
    (h : supportCodimension Z ≠ 1) : principalDivisor X f Z = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨W, rfl⟩
  exact h W.property

/-- The complete coefficient formula on the original integral generators. -/
theorem principalDivisor_apply (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) (Z : IntegralClosedSubscheme X) :
    principalDivisor X f Z =
      if h : supportCodimension Z = 1 then primeDivisorOrder X ⟨Z, h⟩ f else 0 := by
  classical
  by_cases h : supportCodimension Z = 1
  · simpa only [dif_pos h] using principalDivisor_apply_prime X f ⟨Z, h⟩
  · simp only [dif_neg h, principalDivisor_apply_of_not_prime X f Z h]

/-- The cycle support is exactly the image of the nonzero prime-coefficient
set under the inclusion of actual prime divisors into integral subschemes. -/
theorem principalDivisor_support (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    ((principalDivisor X f).support : Set (IntegralClosedSubscheme X)) =
      Subtype.val '' {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} := by
  classical
  ext Z
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_image]
  constructor
  · intro hZ
    have h : supportCodimension Z = 1 := by
      by_contra hn
      exact hZ (principalDivisor_apply_of_not_prime X f Z hn)
    exact ⟨⟨Z, h⟩, by simpa only [principalDivisor_apply_prime X f ⟨Z, h⟩] using hZ, rfl⟩
  · rintro ⟨W, hW, rfl⟩
    simpa only [principalDivisor_apply_prime] using hW

/-- Vanishing of this cycle means all existing prime-divisor orders vanish;
it does not assert that the rational function is a global unit. -/
theorem principalDivisor_eq_zero_iff (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    principalDivisor X f = 0 ↔ ∀ Z : PrimeDivisor X, primeDivisorOrder X Z f = 0 := by
  constructor
  · intro h Z
    rw [← principalDivisor_apply_prime X f Z, h, Finsupp.zero_apply]
  · intro h
    ext Z
    rw [principalDivisor_apply]
    split_ifs <;> simp only [h, Finsupp.zero_apply]

@[simp]
theorem principalDivisor_one (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] :
    principalDivisor X (1 : X.functionFieldˣ) = 0 := by
  apply (principalDivisor_eq_zero_iff X 1).mpr
  intro Z
  exact divisorOrder_one X _

/-- Multiplication of rational functions gives addition in the existing
integral cycle module. -/
theorem principalDivisor_mul (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f g : X.functionFieldˣ) :
    principalDivisor X (f * g) = principalDivisor X f + principalDivisor X g := by
  classical
  ext Z
  by_cases h : supportCodimension Z = 1 <;>
    simp [principalDivisor_apply, h, primeDivisorOrder, divisorOrder_mul]

@[simp]
theorem principalDivisor_inv (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    principalDivisor X f⁻¹ = -principalDivisor X f := by
  classical
  ext Z
  by_cases h : supportCodimension Z = 1 <;>
    simp [principalDivisor_apply, h, primeDivisorOrder, divisorOrder_inv]

theorem principalDivisor_div (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f g : X.functionFieldˣ) :
    principalDivisor X (f / g) = principalDivisor X f - principalDivisor X g := by
  rw [div_eq_mul_inv, principalDivisor_mul, principalDivisor_inv, sub_eq_add_neg]

/-- The multiplicative-to-additive principal-divisor homomorphism, with
the multiplicative group of actual rational functions additively tagged. -/
def principalDivisorAddHom (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] :
    Additive X.functionFieldˣ →+ Cycles X ℤ where
  toFun f := principalDivisor X f.toMul
  map_zero' := principalDivisor_one X
  map_add' f g := principalDivisor_mul X f.toMul g.toMul

@[simp]
theorem principalDivisorAddHom_ofMul (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    principalDivisorAddHom X (Additive.ofMul f) = principalDivisor X f := rfl

end

end HodgeConjecture.SchemeCycles
