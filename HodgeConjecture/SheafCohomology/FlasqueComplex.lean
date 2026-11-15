module

public import HodgeConjecture.SheafCohomology.LinearCoefficients
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

@[expose] public section

/-!+# Sections of bounded-below acyclic complexes of flasque sheaves

The native cycles and their short exact sequences retain the original
complex. Native flasque quotient and section-lifting theorems supply
the bounded-below induction.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

namespace HodgeConjecture.SheafCohomology.FlasqueComplex

universe u

section Cycles

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- Exactness makes the original differential onto the native next-cycle object. -/
theorem epi_toCycles (hK : K.Acyclic) (n : ℤ) (m : ℤ := n + 1)
    (hnm : n + 1 = m := by rfl) : Epi (K.toCycles n m) := by
  have h : (K.sc' n m (m + 1)).Exact :=
    (K.exactAt_iff' n m (m + 1) (by simp; omega) (by simp)).mp (hK m)
  have := h.epi_toCycles
  have he := K.toCycles_cyclesIsoSc'_hom n m (m + 1) (by simp; omega) (by simp)
  have : Epi (K.toCycles n m ≫ (K.cyclesIsoSc' n m (m + 1) (by simp; omega) (by simp)).hom) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso (K.toCycles n m)
    (K.cyclesIsoSc' n m (m + 1) (by simp; omega) (by simp)).hom).mp this

/-- The native cycle inclusion and original differential factor form a short exact sequence. -/
theorem cycles_shortExact (hK : K.Acyclic) (n : ℤ) (m : ℤ := n + 1)
    (hnm : n + 1 = m := by rfl) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n m) (by
      rw [← cancel_mono (K.iCycles m), Category.assoc, toCycles_i, iCycles_d,
        zero_comp])).ShortExact := by
  have := epi_toCycles K hK n m hnm
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  exact isKernelOfComp (K.iCycles m) (K.d n m)
    (K.cyclesIsKernel n m (by simp; omega)) _ (toCycles_i K n m)

end Cycles

variable (X : TopCat.{u})

/-- A zero native sheaf is flasque, on the same space and opens. -/
theorem isFlasque_of_isZero {C : Type*} [Category* C] [Abelian C]
    (A : Sheaf (Opens.grothendieckTopology X) C) (hA : IsZero A) :
    TopCat.Sheaf.IsFlasque (X := X) A where
  epi {U V} i := by
    have hV := ((sheafToPresheaf (Opens.grothendieckTopology X) C) ⋙
      (evaluation _ _).obj V).map_isZero hA
    exact hV.epi (A.obj.map i)

/-- Exact bounded-below flasque terms have flasque native cycles. -/
theorem cycles_isFlasque (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    (hK : K.Acyclic) (hF : ∀ n, TopCat.Sheaf.IsFlasque (X := X) (K.X n))
    (b : ℤ) [K.IsStrictlyGE b] (n : ℤ) : TopCat.Sheaf.IsFlasque (X := X) (K.cycles n) := by
  have hnat : ∀ m : ℕ, TopCat.Sheaf.IsFlasque (X := X) (K.cycles (b + m)) := by
    intro m
    induction m with
    | zero =>
      have := epi_toCycles K hK (b - 1)
      have hz : IsZero (K.cycles b) := by
        simpa using IsZero.of_epi (K.toCycles (b - 1) (b - 1 + 1))
          (K.isZero_of_isStrictlyGE b (b - 1) (by omega))
      simpa using isFlasque_of_isZero X (K.cycles b) hz
    | succ m ih =>
      let : TopCat.Sheaf.IsFlasque (X := X) (K.cycles (b + m)) := ih
      let : TopCat.Sheaf.IsFlasque (X := X) (K.X (b + m)) := hF _
      have h := TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (cycles_shortExact K hK (b + m))
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
  by_cases hn : b ≤ n
  · have he : b + ((n - b).toNat : ℤ) = n := by omega
    rw [← he]
    exact hnat _
  · exact isFlasque_of_isZero X _ (IsZero.of_mono (K.iCycles n)
      (K.isZero_of_isStrictlyGE b n (by omega)))

/-- Sections on every original open preserve exactness of this bounded-below flasque complex. -/
theorem sections_acyclic (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    (hK : K.Acyclic) (hF : ∀ n, TopCat.Sheaf.IsFlasque (X := X) (K.X n))
    (b : ℤ) [K.IsStrictlyGE b] (U : Opens X) :
    (((Cohomology.Basis.secFunctor (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
      U).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let Γ := Cohomology.Basis.secFunctor (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) U
  have hΓ (m n : ℤ) (hmn : m + 1 = n) : Epi (Γ.map (K.toCycles m n)) := by
    let : TopCat.Sheaf.IsFlasque (X := X) (K.cycles m) := cycles_isFlasque X K hK hF b m
    exact TopCat.Sheaf.IsFlasque.epi_of_shortExact (cycles_shortExact K hK m n hmn) (U := U)
  intro n
  rw [((Γ.mapHomologicalComplex (.up ℤ)).obj K).exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)]
  let S := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  have hS : (S.map Γ).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    exact KernelFork.mapIsLimit _ (K.cyclesIsKernel n (n + 1) (by simp)) Γ
  have : Epi (Γ.map (K.toCycles (n - 1) n)) := hΓ (n - 1) n (by omega)
  let φ : (K.sc' (n - 1) n (n + 1)).map Γ ⟶ S.map Γ :=
    { τ₁ := Γ.map (K.toCycles (n - 1) n)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, ← Γ.map_comp]
      comm₂₃ := by simp [S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS

/-- A monomorphic quasi-isomorphism between bounded-below flasque complexes remains one on sections. -/
theorem sections_quasiIso_of_mono
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ}
    (f : K ⟶ L) [Mono f] [QuasiIso f]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (X := X) (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (X := X) (L.X n))
    (b : ℤ) [L.IsStrictlyGE b] (U : Opens X) :
    QuasiIso (((Cohomology.Basis.secFunctor (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
      U).mapHomologicalComplex (.up ℤ)).map f) := by
  let Γ := Cohomology.Basis.secFunctor (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) U
  let S := ShortComplex.cokernelSequence f
  have : Mono S.f := by change Mono f; infer_instance
  have : QuasiIso S.f := by change QuasiIso f; infer_instance
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  have : Epi S.g := hS.epi_g
  have hSn (n : ℤ) := hS.map_of_exact (HomologicalComplex.eval _ (.up ℤ) n)
  have hQ : ∀ n, TopCat.Sheaf.IsFlasque (X := X) (S.X₃.X n) := by
    intro n
    let : TopCat.Sheaf.IsFlasque (X := X) ((S.map (HomologicalComplex.eval _ (.up ℤ) n)).X₁) := hK n
    let : TopCat.Sheaf.IsFlasque (X := X) ((S.map (HomologicalComplex.eval _ (.up ℤ) n)).X₂) := hL n
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (hSn n)
  have : S.X₃.IsStrictlyGE b := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have := (hSn n).epi_g
    exact IsZero.of_epi (S.g.f n) (L.isZero_of_isStrictlyGE b n hn)
  have hQΓ := sections_acyclic X S.X₃ (hS.acyclic_X₃ inferInstance) hQ b U
  have hSΓ : (S.map (Γ.mapHomologicalComplex (.up ℤ))).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let : TopCat.Sheaf.IsFlasque (X := X) ((S.map (HomologicalComplex.eval _ (.up ℤ) n)).X₁) := hK n
    have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono Γ).mp
      inferInstance _ (hSn n)
    apply ShortComplex.ShortExact.mk'
    · exact hleft.1
    · exact hleft.2
    · exact TopCat.Sheaf.IsFlasque.epi_of_shortExact (hSn n) (U := U)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map f) n) :=
    (hSΓ.homology_exact₁ (n - 1) n (by simp)).mono_g
      ((hQΓ (n - 1)).isZero_homology.eq_zero_of_src _)
  have : Epi (homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map f) n) :=
    (hSΓ.homology_exact₂ n).epi_f ((hQΓ n).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end HodgeConjecture.SheafCohomology.FlasqueComplex
