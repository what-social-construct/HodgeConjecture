module

public import HodgeConjecture.Cycles.MilnorSymbols
public import HodgeConjecture.Realization.DeRham.Logarithmic
public import HodgeConjecture.CommutativeAlgebra.DeRham.WedgeProduct

@[expose] public section

/-!
# A degree-two logarithmic regulator on actual Milnor symbols

The symbol `{u,v}` maps to the class of `d log u ∧ d log v` in degree-two
cohomology of the constructed Kähler de Rham complex. The original
differential proves closedness; the actual form formula proves both
multiplicativity relations and the Steinberg relation. Descent is through
the presented Milnor-symbol quotient and the actual closed/exact quotient.
No Bloch higher-Chow or singular/mixed-Hodge comparison is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open KaehlerDifferential

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The actual two-form underlying a logarithmic unit symbol. -/
def logarithmicSymbolForm (u v : Aˣ) : ⋀[A]^2 Ω[A⁄k] :=
  exteriorPower.wedgeMul 1 1 (logarithmicForm k A u) (logarithmicForm k A v)

theorem logarithmicSymbolForm_closed (u v : Aˣ) :
    deRhamDifferential (A := k) 2 (logarithmicSymbolForm k A u v) = 0 :=
  deRhamDifferential_wedgeMul_eq_zero_of_closed 1 1 _ _
    (logarithmicForm_closed k A u) (logarithmicForm_closed k A v)

/-- The original logarithmic two-form in the actual kernel. -/
def closedLogarithmicSymbol (u v : Aˣ) : closedForms k A 2 :=
  ⟨logarithmicSymbolForm k A u v, logarithmicSymbolForm_closed k A u v⟩

/-- Its actual degree-two cohomology class. -/
def logarithmicSymbolClass (u v : Aˣ) : Cohomology k A 2 :=
  cohomologyClass k A 2 (closedLogarithmicSymbol k A u v)

theorem logarithmicSymbolForm_mul_left (u v w : Aˣ) :
    logarithmicSymbolForm k A (u * v) w =
      logarithmicSymbolForm k A u w + logarithmicSymbolForm k A v w := by
  simp only [logarithmicSymbolForm, logarithmicForm_mul, map_add, LinearMap.add_apply]

theorem logarithmicSymbolForm_mul_right (u v w : Aˣ) :
    logarithmicSymbolForm k A u (v * w) =
      logarithmicSymbolForm k A u v + logarithmicSymbolForm k A u w := by
  simp only [logarithmicSymbolForm, logarithmicForm_mul, map_add]

theorem logarithmicSymbolClass_mul_left (u v w : Aˣ) :
    logarithmicSymbolClass k A (u * v) w =
      logarithmicSymbolClass k A u w + logarithmicSymbolClass k A v w := by
  have h : closedLogarithmicSymbol k A (u * v) w =
      closedLogarithmicSymbol k A u w + closedLogarithmicSymbol k A v w :=
    Subtype.ext (logarithmicSymbolForm_mul_left k A u v w)
  simp only [logarithmicSymbolClass, h, map_add]

theorem logarithmicSymbolClass_mul_right (u v w : Aˣ) :
    logarithmicSymbolClass k A u (v * w) =
      logarithmicSymbolClass k A u v + logarithmicSymbolClass k A u w := by
  have h : closedLogarithmicSymbol k A u (v * w) =
      closedLogarithmicSymbol k A u v + closedLogarithmicSymbol k A u w :=
    Subtype.ext (logarithmicSymbolForm_mul_right k A u v w)
  simp only [logarithmicSymbolClass, h, map_add]

/-- Steinberg vanishing holds on the actual exterior two-form, before quotienting. -/
theorem logarithmicSymbolForm_steinberg (u v : Aˣ) (huv : (u : A) + (v : A) = 1) :
    logarithmicSymbolForm k A u v = 0 := by
  have hd : D k A (v : A) = -D k A (u : A) := by
    have h := congrArg (D k A) huv
    rw [map_add, Derivation.map_one_eq_zero] at h
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  have hform : logarithmicForm k A v =
      -(((v⁻¹ : Aˣ) : A) * (u : A)) • logarithmicForm k A u := by
    have hc : -(((v⁻¹ : Aˣ) : A) * (u : A)) * ((u⁻¹ : Aˣ) : A) =
        -((v⁻¹ : Aˣ) : A) := by
      rw [neg_mul, mul_assoc]
      simp
    apply (exteriorPower.oneEquiv A Ω[A⁄k]).injective
    simp only [map_smul, oneEquiv_logarithmicForm, logarithmicDifferential,
      hd, smul_neg, smul_smul, hc, neg_smul]
  rw [logarithmicSymbolForm, hform, map_smul, exteriorPower.wedgeMul_one_self, smul_zero]

theorem logarithmicSymbolClass_steinberg (u v : Aˣ) (huv : (u : A) + (v : A) = 1) :
    logarithmicSymbolClass k A u v = 0 := by
  have h : closedLogarithmicSymbol k A u v = 0 :=
    Subtype.ext (logarithmicSymbolForm_steinberg k A u v huv)
  simp only [logarithmicSymbolClass, h, map_zero]

@[simp]
theorem logarithmicSymbolForm_self (u : Aˣ) : logarithmicSymbolForm k A u u = 0 :=
  exteriorPower.wedgeMul_one_self _

@[simp]
theorem logarithmicSymbolClass_self (u : Aˣ) : logarithmicSymbolClass k A u u = 0 := by
  have h : closedLogarithmicSymbol k A u u = 0 :=
    Subtype.ext (logarithmicSymbolForm_self k A u)
  simp only [logarithmicSymbolClass, h, map_zero]

theorem logarithmicSymbolForm_swap (u v : Aˣ) :
    logarithmicSymbolForm k A u v = -logarithmicSymbolForm k A v u := by
  apply Subtype.ext
  simpa only [logarithmicSymbolForm, Submodule.coe_neg,
    one_mul, pow_one, neg_one_mul] using
      exteriorPower.coe_wedgeMul_comm 1 1 (logarithmicForm k A u) (logarithmicForm k A v)

theorem logarithmicSymbolClass_swap (u v : Aˣ) :
    logarithmicSymbolClass k A u v = -logarithmicSymbolClass k A v u := by
  have h : closedLogarithmicSymbol k A u v = -closedLogarithmicSymbol k A v u :=
    Subtype.ext (logarithmicSymbolForm_swap k A u v)
  simp only [logarithmicSymbolClass, h, map_neg]

/-- Linear assembly of actual degree-two logarithmic classes on free unit symbols. -/
def freeLogarithmicSymbolMap : MilnorSymbols.FreeSymbols k A →ₗ[k] Cohomology k A 2 :=
  Finsupp.linearCombination k (fun uv ↦ logarithmicSymbolClass k A uv.1 uv.2)

@[simp]
theorem freeLogarithmicSymbolMap_single (u v : Aˣ) (a : k) :
    freeLogarithmicSymbolMap k A (Finsupp.single (u, v) a) =
      a • logarithmicSymbolClass k A u v := by
  simp [freeLogarithmicSymbolMap]

/-- Every defining relation is killed by the original logarithmic form calculation. -/
theorem milnorRelations_le_ker_freeLogarithmicSymbolMap :
    MilnorSymbols.relations k A ≤ LinearMap.ker (freeLogarithmicSymbolMap k A) := by
  apply Submodule.span_le.mpr
  intro r hr
  change freeLogarithmicSymbolMap k A r = 0
  cases hr with
  | mul_left u v w =>
      simp [logarithmicSymbolClass_mul_left]
  | mul_right u v w =>
      simp [logarithmicSymbolClass_mul_right]
  | steinberg u v h =>
      simp [logarithmicSymbolClass_steinberg k A u v h]

/-- The degree-two logarithmic de Rham regulator on the actual Milnor-symbol quotient. -/
def milnorRegulator : MilnorSymbols.K2 k A →ₗ[k] Cohomology k A 2 :=
  (MilnorSymbols.relations k A).liftQ (freeLogarithmicSymbolMap k A)
    (milnorRelations_le_ker_freeLogarithmicSymbolMap k A)

@[simp]
theorem milnorRegulator_symbol (u v : Aˣ) :
    milnorRegulator k A (MilnorSymbols.symbol k A u v) =
      logarithmicSymbolClass k A u v := by
  change freeLogarithmicSymbolMap k A (Finsupp.single (u, v) 1) = _
  simp

end

end HodgeConjecture.AffineDeRham
