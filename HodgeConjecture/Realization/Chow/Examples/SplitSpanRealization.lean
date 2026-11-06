module

public import HodgeConjecture.Correspondence.Examples.SplitSpanGeometry
public import HodgeConjecture.Correspondence.Examples.SplitPointMaps
public import HodgeConjecture.Correspondence.Examples.SplitSpanCoproduct
public import HodgeConjecture.LinearAlgebra.FiniteSpanMatrix

@[expose] public section

/-!
# Intrinsic matrix realization of finite split scheme spans

Incidence matrices are invariant under actual scheme-span isomorphisms.
This is the descent step from split presentations to geometric classes;
the relabelling is extracted from the scheme isomorphism itself.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory Classical
open scoped BigOperators

noncomputable section

universe u

namespace SplitSpanRealization

open SplitPointGeometry

variable (K : Type u) [Field K]
variable {I J S T : Type u} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

/-- Incidence coefficients depend on the actual geometric span, not on its
chosen finite split presentation. -/
theorem matrix_eq_of_isom
    (leftS : S → I) (rightS : S → J) (leftT : T → I) (rightT : T → J)
    (e : SchemeCorrespondence.Isom (span K leftS rightS) (span K leftT rightT)) :
    FiniteSpanMatrix.matrix leftS rightS = FiniteSpanMatrix.matrix leftT rightT := by
  let b := labelEquivOfIso K e.carrierIso
  have hl : leftT ∘ b = leftS := by
    funext s
    exact labelEquivOfIso_respects_map K e.carrierIso
      (mapOfFunction K leftS) (mapOfFunction K leftT) leftS leftT
      (labelEquivScheme_natural K leftS) (labelEquivScheme_natural K leftT)
      e.hom_left s
  have hr : rightT ∘ b = rightS := by
    funext s
    exact labelEquivOfIso_respects_map K e.carrierIso
      (mapOfFunction K rightS) (mapOfFunction K rightT) rightS rightT
      (labelEquivScheme_natural K rightS) (labelEquivScheme_natural K rightT)
      e.hom_right s
  rw [← hl, ← hr]
  exact FiniteSpanMatrix.matrix_reindex b leftT rightT

/-- Equality in the existing geometric correspondence quotient is sufficient
for equality of the incidence matrices. -/
theorem matrix_eq_of_class_eq
    (leftS : S → I) (rightS : S → J) (leftT : T → I) (rightT : T → J)
    (h : SchemeCorrespondence.classOf (span K leftS rightS) =
      SchemeCorrespondence.classOf (span K leftT rightT)) :
    FiniteSpanMatrix.matrix leftS rightS = FiniteSpanMatrix.matrix leftT rightT := by
  obtain ⟨e⟩ := Quotient.exact h
  exact matrix_eq_of_isom K leftS rightS leftT rightT e

variable (I)

/-- A finite split presentation of an existing finite-étale scheme-span
class. The equality is in the actual carrier-isomorphism quotient. -/
structure Presentation
    (c : SchemeCorrespondence.FiniteEtaleClass (toBase K I)) where
  Carrier : Type u
  fintypeCarrier : Fintype Carrier
  left : Carrier → I
  right : Carrier → I
  presents : SchemeCorrespondence.classOf (span K left right) = c.val

attribute [instance] Presentation.fintypeCarrier

/-- The finite-étale class represented by a finite split span. -/
def spanClass (left right : S → I) :
    SchemeCorrespondence.FiniteEtaleClass (toBase K I) :=
  SchemeCorrespondence.finiteEtaleClassOf (span K left right)
    (span_hasFiniteEtaleLegs K left right)

/-- The tautological presentation of a finite split span. -/
def spanPresentation (left right : S → I) :
    Presentation K I (spanClass K I left right) where
  Carrier := S
  fintypeCarrier := inferInstance
  left := left
  right := right
  presents := rfl

/-- The point-cycle matrix computed from a finite split presentation. -/
def Presentation.matrix
    {c : SchemeCorrespondence.FiniteEtaleClass (toBase K I)}
    (P : Presentation K I c) : Matrix I I ℚ :=
  FiniteSpanMatrix.matrix P.left P.right

/-- Any two presentations of the same actual class give identical coefficients. -/
theorem Presentation.matrix_eq
    {c : SchemeCorrespondence.FiniteEtaleClass (toBase K I)}
    (P Q : Presentation K I c) : P.matrix = Q.matrix :=
  matrix_eq_of_class_eq K P.left P.right Q.left Q.right
    (P.presents.trans Q.presents.symm)

/-- The identity correspondence has the diagonal split presentation. -/
def identityPresentation : Presentation K I 1 where
    Carrier := I
    fintypeCarrier := inferInstance
    left := id
    right := id
    presents := SchemeCorrespondence.classOf_eq_of_isom (span_identity_iso K I)

/-- Composition uses the actual scheme pullback comparison, not merely a
definition of multiplication on finite labels. -/
def Presentation.comp
    {a b : SchemeCorrespondence.FiniteEtaleClass (toBase K I)}
    (Q : Presentation K I a) (P : Presentation K I b) :
    Presentation K I (a * b) := by
  classical
  exact {
    Carrier := {p : P.Carrier × Q.Carrier // P.right p.1 = Q.left p.2}
    fintypeCarrier := inferInstance
    left := fun p => P.left p.val.1
    right := fun p => Q.right p.val.2
    presents := by
      calc
        _ = SchemeCorrespondence.classOf ((span K Q.left Q.right).comp
            (span K P.left P.right)) :=
          (SchemeCorrespondence.classOf_eq_of_isom
            (span_comp_iso K P.left P.right Q.left Q.right)).symm
        _ = (a * b).val := by
          rw [SchemeCorrespondence.classOf_comp, Q.presents, P.presents]
          rfl
  }

/-- Finite split-presentable classes form a submonoid of the existing
finite-étale geometric correspondence classes. -/
def classSubmonoid :
    Submonoid (SchemeCorrespondence.FiniteEtaleClass (toBase K I)) where
  carrier := {c | Nonempty (Presentation K I c)}
  one_mem' := ⟨identityPresentation K I⟩
  mul_mem' := by
    rintro a b ⟨Q⟩ ⟨P⟩
    exact ⟨Presentation.comp K I Q P⟩

/-- Actual finite split scheme-span classes, with their geometric convolution. -/
abbrev SplitClass := classSubmonoid K I

/-- A presented span as an intrinsic geometric class. -/
def ofSpan (left right : S → I) : SplitClass K I :=
  ⟨spanClass K I left right, ⟨spanPresentation K I left right⟩⟩

/-- Choose a presentation only to compute coefficients; the preceding
invariance theorem removes all dependence on this choice. -/
def classMatrix (c : SplitClass K I) : Matrix I I ℚ :=
  (Classical.choice c.property).matrix

theorem classMatrix_eq (c : SplitClass K I) (P : Presentation K I c.val) :
    classMatrix K I c = P.matrix :=
  Presentation.matrix_eq K I (Classical.choice c.property) P

@[simp]
theorem classMatrix_ofSpan (left right : S → I) :
    classMatrix K I (ofSpan K I left right) = FiniteSpanMatrix.matrix left right := by
  simpa only [Presentation.matrix, spanPresentation] using
    classMatrix_eq K I (ofSpan K I left right) (spanPresentation K I left right)

variable [DecidableEq I]

theorem classMatrix_one : classMatrix K I 1 = 1 := by
  rw [classMatrix_eq K I 1 (identityPresentation K I)]
  exact FiniteSpanMatrix.matrix_id

omit [DecidableEq I] in
theorem classMatrix_mul (a b : SplitClass K I) :
    classMatrix K I (a * b) = classMatrix K I a * classMatrix K I b := by
  let Q := Classical.choice a.property
  let P := Classical.choice b.property
  rw [classMatrix_eq K I (a * b) (Presentation.comp K I Q P)]
  classical
  exact FiniteSpanMatrix.matrix_pullback P.left P.right Q.left Q.right

/-- The multiplicative point-cycle assignment on actual geometric classes. -/
def classMatrixHom : SplitClass K I →* Matrix I I ℚ where
  toFun := classMatrix K I
  map_one' := classMatrix_one K I
  map_mul' := classMatrix_mul K I

/-- The free rational algebra on split-presentable geometric classes. It
does not itself impose coproduct additivity. -/
abbrev FreeAlgebra := MonoidAlgebra ℚ (SplitClass K I)

/-- The constructed rational cycle-coefficient realization. -/
def realization : FreeAlgebra K I →ₐ[ℚ] Matrix I I ℚ :=
  MonoidAlgebra.lift ℚ (Matrix I I ℚ) (SplitClass K I) (classMatrixHom K I)

/-- A finite split span as a basis vector. -/
def ofSchemeSpan (left right : S → I) : FreeAlgebra K I :=
  MonoidAlgebra.single (ofSpan K I left right) 1

@[simp]
theorem realization_ofSchemeSpan (left right : S → I) :
    realization K I (ofSchemeSpan K I left right) = FiniteSpanMatrix.matrix left right := by
  simp [realization, ofSchemeSpan, classMatrixHom]

/-- The source is a genuine subalgebra of the existing free finite-étale
span algebra, via forgetting split-presentability. -/
def toFiniteEtaleFreeAlgebra :
    FreeAlgebra K I →ₐ[ℚ] SchemeCorrespondence.FiniteEtaleFreeAlgebra (toBase K I) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (classSubmonoid K I).subtype

omit [DecidableEq I] in
theorem toFiniteEtaleFreeAlgebra_injective :
    Function.Injective (toFiniteEtaleFreeAlgebra K I) :=
  MonoidAlgebra.mapDomain_injective Subtype.val_injective

omit [DecidableEq I] in
@[simp]
theorem toFiniteEtaleFreeAlgebra_ofSchemeSpan (left right : S → I) :
    toFiniteEtaleFreeAlgebra K I (ofSchemeSpan K I left right) =
      SchemeCorrespondence.finiteEtaleOfScheme (span K left right)
        (span_hasFiniteEtaleLegs K left right) := by
  simp [toFiniteEtaleFreeAlgebra, ofSchemeSpan,
    SchemeCorrespondence.finiteEtaleOfScheme, ofSpan, spanClass]

omit [DecidableEq I] in
/-- The same basis vector represents any actually isomorphic geometric span. -/
theorem toFiniteEtaleFreeAlgebra_ofSchemeSpan_isom
    (left right : S → I)
    {P : SchemeCorrespondence (toBase K I) (toBase K I)}
    (hP : SchemeCorrespondence.HasFiniteEtaleLegs P)
    (e : SchemeCorrespondence.Isom (span K left right) P) :
    toFiniteEtaleFreeAlgebra K I (ofSchemeSpan K I left right) =
      SchemeCorrespondence.finiteEtaleOfScheme P hP := by
  rw [toFiniteEtaleFreeAlgebra_ofSchemeSpan]
  unfold SchemeCorrespondence.finiteEtaleOfScheme
  congr 1
  apply Subtype.ext
  exact SchemeCorrespondence.classOf_eq_of_isom e

@[simp]
theorem realization_single_ofSpan (left right : S → I) (q : ℚ) :
    realization K I (MonoidAlgebra.single (ofSpan K I left right) q) =
      q • FiniteSpanMatrix.matrix left right := by
  simp [realization, classMatrixHom]

/-- Empty geometric carriers have zero cycle coefficients, though their
free span basis vector is not defined to be zero. -/
theorem realization_empty [IsEmpty S] (left right : S → I) :
    realization K I (ofSchemeSpan K I left right) = 0 := by
  rw [realization_ofSchemeSpan, FiniteSpanMatrix.matrix_empty]

/-- The realization kills the disjoint-union additivity relation. -/
theorem realization_sum (leftS rightS : S → I) (leftT rightT : T → I) :
    realization K I (ofSchemeSpan K I (Sum.elim leftS leftT) (Sum.elim rightS rightT)) =
      realization K I (ofSchemeSpan K I leftS rightS) +
        realization K I (ofSchemeSpan K I leftT rightT) := by
  simp only [realization_ofSchemeSpan]
  exact FiniteSpanMatrix.matrix_sum leftS rightS leftT rightT

omit [DecidableEq I] in
/-- The sum-indexed basis vector is the actual geometric coproduct class
under the source embedding. Together with `realization_sum`, this proves
geometric coproduct additivity, not only a law on labels. -/
theorem toFiniteEtaleFreeAlgebra_sum (leftS rightS : S → I) (leftT rightT : T → I)
    (hCoprod : SchemeCorrespondence.HasFiniteEtaleLegs
      (SchemeCorrespondence.coprod (span K leftS rightS) (span K leftT rightT))) :
    toFiniteEtaleFreeAlgebra K I
        (ofSchemeSpan K I (Sum.elim leftS leftT) (Sum.elim rightS rightT)) =
      SchemeCorrespondence.finiteEtaleOfScheme
        (SchemeCorrespondence.coprod (span K leftS rightS) (span K leftT rightT)) hCoprod :=
  toFiniteEtaleFreeAlgebra_ofSchemeSpan_isom K I _ _ hCoprod
    (span_sum_iso K leftS rightS leftT rightT)

omit [Fintype I] [DecidableEq I] in
/-- The finite-étale proof needed in the preceding comparison is constructed. -/
theorem coprod_hasFiniteEtaleLegs (leftS rightS : S → I) (leftT rightT : T → I) :
    SchemeCorrespondence.HasFiniteEtaleLegs
      (SchemeCorrespondence.coprod (span K leftS rightS) (span K leftT rightT)) :=
  SchemeCorrespondence.HasFiniteEtaleLegs.of_isom
    (span_sum_iso K leftS rightS leftT rightT)
    (span_hasFiniteEtaleLegs K _ _)

/-- Every rational point-pair cycle matrix is realized by a rational
combination of actual split point spans. -/
theorem realization_surjective : Function.Surjective (realization K I) := by
  intro M
  refine ⟨∑ i, ∑ j, MonoidAlgebra.single
    (ofSpan K I (fun _ : PUnit.{u+1} => j) (fun _ => i)) (M i j), ?_⟩
  simp only [map_sum, realization_single_ofSpan]
  ext i j
  simp [FiniteSpanMatrix.matrix, Matrix.single, Matrix.sum_apply, ite_and]

end SplitSpanRealization

end

end HodgeConjecture
