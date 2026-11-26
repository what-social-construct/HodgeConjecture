module

public import HodgeConjecture.LinearAlgebra.Harmonic.HarmonicCohomology

@[expose] public section

/-!
# Cohomological transport of harmonic witnesses

The witness map below passes through the actual quotient by cellular boundaries.
For a symmetric same-complex endomorphism, naturality identifies that transport
with the endomorphism's restriction to harmonic cochains. Faithfulness of a
transported witness remains a separate hypothesis; symmetry does not imply it.

All cochains in this module are finite real cochains on the same oriented
complex. Restriction to rational scalars only changes the witness-map scalars.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.Harmonic.CellularSheaf.Morphism

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}
  {F : CellularSheaf X}

/-- Multiplication by a real scalar on every stalk gives a cellular endomorphism. -/
def scalar (F : CellularSheaf X) (t : ℝ) : Morphism F F where
  vertexMap _ := t • LinearMap.id
  edgeMap _ := t • LinearMap.id
  faceMap _ := t • LinearMap.id
  naturality01 _ _ _ := by ext x; simp
  naturality12 _ _ _ := by ext x; simp
  naturality02 _ _ _ _ _ := by ext x; simp

@[simp]
theorem scalar_mapC0 (F : CellularSheaf X) (t : ℝ) :
    (scalar F t).mapC0 = t • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro p
  rcases p with ⟨v, i⟩
  rfl

@[simp]
theorem scalar_mapC1 (F : CellularSheaf X) (t : ℝ) :
    (scalar F t).mapC1 = t • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro p
  rcases p with ⟨e, i⟩
  rfl

@[simp]
theorem scalar_mapC2 (F : CellularSheaf X) (t : ℝ) :
    (scalar F t).mapC2 = t • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro p
  rcases p with ⟨f, i⟩
  rfl

/-- Scalar cellular endomorphisms satisfy the symmetry premise of naturality. -/
theorem scalar_mapC1_isSymmetric (F : CellularSheaf X) (t : ℝ) :
    (scalar F t).mapC1.IsSymmetric := by
  rw [scalar_mapC1]
  exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Transport a rational witness through degree-one cellular cohomology.

The construction itself needs only a cellular endomorphism. Its identification
with a map on harmonic cochains uses the symmetry hypothesis in the next theorem.
-/
def transportHarmonicWitness (η : Morphism F F)
    (W : V →ₗ[ℚ] F.harmonicOneSubspace) : V →ₗ[ℚ] F.harmonicOneSubspace :=
  (F.cohomologyOneEquivHarmonic.toLinearMap.restrictScalars ℚ).comp
    ((η.mapCohomologyOne.restrictScalars ℚ).comp
      ((F.cohomologyOneEquivHarmonic.symm.toLinearMap.restrictScalars ℚ).comp W))

/-- Naturality computes the quotient-defined transport on each witness. -/
theorem transportHarmonicWitness_apply (η : Morphism F F)
    (hη : η.mapC1.IsSymmetric) (W : V →ₗ[ℚ] F.harmonicOneSubspace) (x : V) :
    η.transportHarmonicWitness W x = η.mapHarmonicOne hη (W x) := by
  change F.cohomologyOneEquivHarmonic
      (η.mapCohomologyOne (F.cohomologyOneEquivHarmonic.symm (W x))) = _
  rw [η.cohomologyOneEquivHarmonic_naturality hη, LinearEquiv.apply_symm_apply]

/-- Map-level form of the harmonic naturality computation. -/
theorem transportHarmonicWitness_eq_mapHarmonicOne (η : Morphism F F)
    (hη : η.mapC1.IsSymmetric) (W : V →ₗ[ℚ] F.harmonicOneSubspace) :
    η.transportHarmonicWitness W = ((η.mapHarmonicOne hη).restrictScalars ℚ).comp W := by
  apply LinearMap.ext
  exact η.transportHarmonicWitness_apply hη W

/-- Scalar transport agrees with scalar multiplication on harmonic witnesses. -/
@[simp]
theorem transportHarmonicWitness_scalar_apply (F : CellularSheaf X) (t : ℝ)
    (W : V →ₗ[ℚ] F.harmonicOneSubspace) (x : V) :
    (scalar F t).transportHarmonicWitness W x = t • W x := by
  rw [transportHarmonicWitness_apply _ (scalar_mapC1_isSymmetric F t)]
  apply Subtype.ext
  change (scalar F t).mapC1 (W x) = t • (W x : F.C1)
  rw [scalar_mapC1]
  rfl

/-- A nonzero scalar preserves an already faithful harmonic witness. -/
theorem transportHarmonicWitness_scalar_injective (F : CellularSheaf X)
    {t : ℝ} (ht : t ≠ 0) (W : V →ₗ[ℚ] F.harmonicOneSubspace)
    (hW : Function.Injective W) :
    Function.Injective ((scalar F t).transportHarmonicWitness W) := by
  intro x y hxy
  apply hW
  have hsmul : t • W x = t • W y := by
    simpa only [transportHarmonicWitness_scalar_apply] using hxy
  exact smul_right_injective _ ht hsmul

end HodgeConjecture.Harmonic.CellularSheaf.Morphism

end
