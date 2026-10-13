import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.Torsion

/-!
# Relative lengths of lattices

The relative length of two lattices is computed from the actual finite
quotients in their common sum. It is additive through a third lattice,
invariant under linear isomorphisms, and gives a lattice-independent
integer for an automorphism. These are the lattice facts used in
Stacks Project, Tag 02MI: https://stacks.math.columbia.edu/tag/02MI

Finiteness is proved by clearing denominators and reducing to a nonzero
principal quotient. No freeness or normality is required.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (V : Type*) [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

omit [IsDomain R] in
theorem lattice_isLocalizedModule (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype := by
  let S := nonZeroDivisors R
  letI := isLocalizedModule_id S V K
  let f : LocalizedModule S M →ₗ[K] V := IsLocalizedModule.mapExtendScalars S
    (LocalizedModule.mkLinearMap S M) (LinearMap.id : V →ₗ[R] V) K M.subtype
  have hf : Function.Injective f :=
    IsLocalizedModule.map_injective S _ _ M.subtype M.subtype_injective
  have happ (m : M) : f (LocalizedModule.mkLinearMap S M m) = (m : V) :=
    IsLocalizedModule.map_apply S _ _ M.subtype m
  have hs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hM, Submodule.span_le]
    intro x hx
    exact ⟨LocalizedModule.mkLinearMap S M ⟨x, hx⟩, happ _⟩
  let e := (LinearEquiv.ofBijective f ⟨hf, hs⟩).restrictScalars R
  have h := IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  convert h using 1
  ext m
  exact (happ m).symm

omit [IsDomain R] in
theorem lattice_exists_smul_mem (M N : Submodule R V) [Submodule.IsLattice K M] (hN : N.FG) :
    ∃ a : nonZeroDivisors R, ∀ x ∈ N, (a : R) • x ∈ M := by
  letI := lattice_isLocalizedModule R K V M Submodule.IsLattice.span_eq_top
  obtain ⟨s, hs⟩ := hN
  obtain ⟨a, ha⟩ := IsLocalizedModule.exist_integer_multiples_of_finset
    (nonZeroDivisors R) M.subtype s
  refine ⟨a, ?_⟩
  have hle : N ≤ M.comap ((a : R) • (LinearMap.id : V →ₗ[R] V)) := by
    rw [← hs, Submodule.span_le]
    intro x hx
    obtain ⟨y, hy⟩ := ha x hx
    change (a : R) • x ∈ M
    rw [← hy]
    exact y.property
  exact fun x hx => hle hx

theorem finiteLength_of_killed_by_nonzero
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (ha : a ≠ 0) (hM : Module.IsTorsionBy R M a) : IsFiniteLength R M := by
  let I : Ideal R := Ideal.span {a}
  have hI : Module.IsTorsionBySet R M I := (Module.isTorsionBySet_span_singleton_iff a).mpr hM
  letI : Module (R ⧸ I) M := hI.module
  letI : IsScalarTower R (R ⧸ I) M := hI.isScalarTower
  have hfin := isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha)
  letI : IsArtinian R (R ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  letI : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R inferInstance
  letI : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R _ _
  letI : IsArtinian R M := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

theorem lattice_quotient_finiteLength [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M N : Submodule R V) [Submodule.IsLattice K M] (hN : N.FG) :
    IsFiniteLength R (N ⧸ M.comap N.subtype) := by
  letI : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  obtain ⟨a, ha⟩ := lattice_exists_smul_mem R K V M N hN
  apply finiteLength_of_killed_by_nonzero R _ (a : R) (nonZeroDivisors.ne_zero a.property)
  exact (Module.isTorsionBy_quotient_iff _ _).mpr (fun x => ha x.val x.property)

private theorem quotient_length_add {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (P N : Submodule R E) (hPN : P ≤ N) :
    Module.length R (E ⧸ P) = Module.length R (N ⧸ P.comap N.subtype) +
      Module.length R (E ⧸ N) := by
  let f := (P.comap N.subtype).mapQ P N.subtype le_rfl
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    dsimp [f, Submodule.mapQ]
    apply Submodule.ker_liftQ_eq_bot
    simp [LinearMap.ker_comp]
  have hex : Function.Exact f (Submodule.factor hPN) := by
    intro x
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    constructor
    · intro h
      have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (P.comap N.subtype).mkQ_surjective y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero N).mpr y.property
  exact Module.length_eq_add_of_exact f (Submodule.factor hPN) hf (Submodule.factor_surjective hPN) hex

abbrev submoduleQuotientLength {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (M N : Submodule R E) : ℕ∞ := Module.length R (M ⧸ N.comap M.subtype)

theorem submoduleQuotientLength_range {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (f : E →ₗ[R] F) (hf : Function.Injective f) (P : Submodule R E) :
    submoduleQuotientLength (LinearMap.range f) (P.map f) = Module.length R (E ⧸ P) := by
  let e := LinearEquiv.ofInjective f hf
  have h : P.map e.toLinearMap = (P.map f).comap (LinearMap.range f).subtype := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, congrArg Subtype.val hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, Subtype.ext hxy⟩
  exact (Submodule.Quotient.equiv _ _ e h).length_eq.symm

theorem submoduleQuotientLength_add {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (L M N : Submodule R E) (hLM : L ≤ M) (hMN : M ≤ N) :
    submoduleQuotientLength N L = submoduleQuotientLength M L + submoduleQuotientLength N M := by
  have h := quotient_length_add (L.comap N.subtype) (M.comap N.subtype)
    (Submodule.comap_mono hLM)
  let e := Submodule.comapSubtypeEquivOfLe hMN
  have he : ((L.comap N.subtype).comap (M.comap N.subtype).subtype).map e.toLinearMap =
      L.comap M.subtype := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact hxy ▸ hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      exact hx
  have hlen := (Submodule.Quotient.equiv _ _ e he).length_eq
  exact h.trans (congrArg (· + submoduleQuotientLength N M) hlen)

def latticeIndex {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (M N : Submodule R E) : ℤ :=
  ((submoduleQuotientLength (M ⊔ N) N).toNat : ℤ) - ((submoduleQuotientLength (M ⊔ N) M).toNat : ℤ)

theorem latticeIndex_common_upper [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M N P : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K N]
    (hP : P.FG) (hMP : M ≤ P) (hNP : N ≤ P) :
    latticeIndex M N = ((submoduleQuotientLength P N).toNat : ℤ) - ((submoduleQuotientLength P M).toNat : ℤ) := by
  have h1 := submoduleQuotientLength_add N (M ⊔ N) P le_sup_right (sup_le hMP hNP)
  have h2 := submoduleQuotientLength_add M (M ⊔ N) P le_sup_left (sup_le hMP hNP)
  have hfin (L : Submodule R V) [Submodule.IsLattice K L] (Q : Submodule R V) (hQ : Q.FG) :
      submoduleQuotientLength Q L ≠ ⊤ := Module.length_ne_top_iff.mpr (lattice_quotient_finiteLength R K V L Q hQ)
  rw [h1, h2, ENat.toNat_add (hfin N _ (Submodule.IsLattice.fg (M := M ⊔ N)))
    (hfin (M ⊔ N) P hP),
    ENat.toNat_add (hfin M _ (Submodule.IsLattice.fg (M := M ⊔ N)))
    (hfin (M ⊔ N) P hP), Nat.cast_add, Nat.cast_add]
  simp [latticeIndex]

theorem latticeIndex_add [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M N P : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K N]
    [Submodule.IsLattice K P] : latticeIndex M N + latticeIndex N P = latticeIndex M P := by
  let Q := M ⊔ N ⊔ P
  have hM : M ≤ Q := le_sup_left.trans le_sup_left
  have hN : N ≤ Q := le_sup_right.trans le_sup_left
  have hP : P ≤ Q := le_sup_right
  rw [latticeIndex_common_upper R K V M N Q Submodule.IsLattice.fg hM hN,
    latticeIndex_common_upper R K V N P Q Submodule.IsLattice.fg hN hP,
    latticeIndex_common_upper R K V M P Q Submodule.IsLattice.fg hM hP]
  omega

theorem submoduleQuotientLength_map {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (e : E ≃ₗ[R] F) (M N : Submodule R E) :
    submoduleQuotientLength (M.map e.toLinearMap) (N.map e.toLinearMap) = submoduleQuotientLength M N := by
  let eM := e.submoduleMap M
  have he : (N.comap M.subtype).map eM.toLinearMap =
      (N.map e.toLinearMap).comap (M.map e.toLinearMap).subtype := by
    ext x
    simp only [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.coe_subtype]
    rfl
  exact (Submodule.Quotient.equiv _ _ eM he).length_eq.symm

theorem latticeIndex_map {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (e : E ≃ₗ[R] F) (M N : Submodule R E) :
    latticeIndex (M.map e.toLinearMap) (N.map e.toLinearMap) = latticeIndex M N := by
  simp only [latticeIndex, ← Submodule.map_sup, submoduleQuotientLength_map]

omit [IsDomain R] [IsFractionRing R K] in
theorem lattice_map_isLattice {W : Type*} [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower R K W] (e : V ≃ₗ[K] W) (M : Submodule R V) [Submodule.IsLattice K M] :
    Submodule.IsLattice K (M.map (e.restrictScalars R).toLinearMap) where
  fg := Submodule.IsLattice.fg.map _
  span_eq_top := by
    change Submodule.span K (e.toLinearMap '' (M : Set V)) = ⊤
    rw [← Submodule.map_span, Submodule.IsLattice.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

theorem latticeIndex_independent [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (e : V ≃ₗ[K] V) (M N : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K N] :
    latticeIndex M (M.map (e.restrictScalars R).toLinearMap) =
      latticeIndex N (N.map (e.restrictScalars R).toLinearMap) := by
  letI := lattice_map_isLattice R K V e M
  letI := lattice_map_isLattice R K V e N
  have h1 := latticeIndex_add R K V M (M.map (e.restrictScalars R).toLinearMap)
    (N.map (e.restrictScalars R).toLinearMap)
  have h2 := latticeIndex_add R K V M N (N.map (e.restrictScalars R).toLinearMap)
  rw [latticeIndex_map] at h1
  omega

theorem latticeIndex_comp [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (e f : V ≃ₗ[K] V) (M : Submodule R V) [Submodule.IsLattice K M] :
    latticeIndex M (M.map ((f.trans e).restrictScalars R).toLinearMap) =
      latticeIndex M (M.map (e.restrictScalars R).toLinearMap) +
        latticeIndex M (M.map (f.restrictScalars R).toLinearMap) := by
  letI := lattice_map_isLattice R K V e M
  letI := lattice_map_isLattice R K V f M
  letI := lattice_map_isLattice R K V (f.trans e) M
  have h := latticeIndex_add R K V M (M.map (e.restrictScalars R).toLinearMap)
    (M.map ((f.trans e).restrictScalars R).toLinearMap)
  have heq : M.map ((f.trans e).restrictScalars R).toLinearMap =
      (M.map (f.restrictScalars R).toLinearMap).map (e.restrictScalars R).toLinearMap := by
    rw [← Submodule.map_comp]; rfl
  rw [heq, latticeIndex_map] at h
  rw [heq]
  exact h.symm

theorem latticeIndex_common_lower [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M N L : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K N]
    [Submodule.IsLattice K L] (hLM : L ≤ M) (hLN : L ≤ N) :
    latticeIndex M N = ((submoduleQuotientLength M L).toNat : ℤ) -
      ((submoduleQuotientLength N L).toNat : ℤ) := by
  have h1 := submoduleQuotientLength_add L M (M ⊔ N) hLM le_sup_left
  have h2 := submoduleQuotientLength_add L N (M ⊔ N) hLN le_sup_right
  have hfin (P Q : Submodule R V) [Submodule.IsLattice K P] [Submodule.IsLattice K Q] :
      submoduleQuotientLength Q P ≠ ⊤ := Module.length_ne_top_iff.mpr
    (lattice_quotient_finiteLength R K V P Q Submodule.IsLattice.fg)
  have h := congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (h1.symm.trans h2)
  dsimp only at h
  rw [ENat.toNat_add (hfin L M) (hfin M (M ⊔ N)),
    ENat.toNat_add (hfin L N) (hfin N (M ⊔ N)), Nat.cast_add, Nat.cast_add] at h
  dsimp [latticeIndex]
  omega

theorem latticeIndex_of_le {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (M N : Submodule R E) (hNM : N ≤ M) :
    latticeIndex M N = ((submoduleQuotientLength M N).toNat : ℤ) := by
  rw [latticeIndex, sup_eq_left.mpr hNM]
  letI : Subsingleton (M ⧸ M.comap M.subtype) :=
    (Submodule.Quotient.subsingleton_iff _).mpr (fun x => x.property)
  simp [submoduleQuotientLength, Module.length_eq_zero]

/-- The signed index of a lattice under an automorphism is additive under composition. -/
def latticeIndexHom [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M : Submodule R V) [Submodule.IsLattice K M] :
    (V ≃ₗ[K] V) →* Multiplicative ℤ where
  toFun e := Multiplicative.ofAdd (latticeIndex M (M.map (e.restrictScalars R).toLinearMap))
  map_one' := by
    change latticeIndex M (M.map LinearMap.id) = 0
    simp [latticeIndex]
  map_mul' e f := latticeIndex_comp R K V e f M

end

end HodgeConjecture.CommutativeAlgebra
