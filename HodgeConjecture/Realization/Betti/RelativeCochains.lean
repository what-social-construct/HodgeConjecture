module

public import HodgeConjecture.Realization.Betti.SubcomplexConnectingRepresentative
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

/-!
# Actual relative rational cochains

For a simplicial subcomplex B of S, relative cochains are the literal
kernel of restriction: original simplex functions vanishing on B. The
original alternating differential preserves this kernel. Inclusion and
restriction give the actual short exact relative/absolute/subcomplex
sequence, with native connecting maps and original maps of pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeCochains

open CategoryTheory HomologicalComplex Opposite Simplicial

universe u

section Pair

variable {S : SSet.{u}} (B : S.Subcomplex)

/-- Original cochain restriction to the actual subcomplex. -/
def restriction : SubcomplexCochains.complex S ⟶ SubcomplexCochains.complex B.toSSet :=
  SubcomplexCochains.pullback B.ι

def restrictionLinear (n : ℕ) :
    SubcomplexCochains.Cochain S n →ₗ[ℚ] SubcomplexCochains.Cochain B.toSSet n :=
  ((restriction B).f n).hom

@[simp]
theorem restrictionLinear_apply (n : ℕ) (φ : SubcomplexCochains.Cochain S n)
    (σ : B.toSSet.obj (op ⦋n⦌)) : restrictionLinear B n φ σ = φ σ.val := rfl

/-- Original simplex functions vanishing on the actual subcomplex. -/
abbrev Cochain (n : ℕ) := LinearMap.ker (restrictionLinear B n)

theorem cochain_vanish (n : ℕ) (φ : Cochain B n) (σ : B.toSSet.obj (op ⦋n⦌)) :
    φ.val σ.val = 0 := congrFun φ.property σ

/-- Original restriction commutes with the original alternating differential. -/
theorem restriction_differential (n : ℕ) (φ : SubcomplexCochains.Cochain S n) :
    restrictionLinear B (n + 1) (SubcomplexCochains.differential S n φ) =
      SubcomplexCochains.differential B.toSSet n (restrictionLinear B n φ) := by
  have h := congrArg (fun f ↦ f.hom φ) ((restriction B).comm n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, SubcomplexCochains.complex_d] at h
  exact h.symm

/-- The actual alternating differential restricted to relative cochains. -/
def differential (n : ℕ) : Cochain B n →ₗ[ℚ] Cochain B (n + 1) where
  toFun φ := ⟨SubcomplexCochains.differential S n φ.val, by
    rw [LinearMap.mem_ker, restriction_differential, φ.property, map_zero]⟩
  map_add' φ ψ := Subtype.ext (map_add _ _ _)
  map_smul' q φ := by
    apply Subtype.ext
    change SubcomplexCochains.differential S n (q • φ.val) =
      q • SubcomplexCochains.differential S n φ.val
    exact map_smul _ _ _

@[simp]
theorem differential_val (n : ℕ) (φ : Cochain B n) :
    (differential B n φ).val = SubcomplexCochains.differential S n φ.val := rfl

theorem differential_squared (n : ℕ) :
    differential B (n + 1) ∘ₗ differential B n = 0 := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  exact SubcomplexCochains.differential_squared S n φ.val

/-- The actual relative kernel-module cochain complex. -/
def complex : CochainComplex (ModuleCat.{u} ℚ) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℚ (Cochain B n))
    (fun n ↦ ModuleCat.ofHom (differential B n))
    (fun n ↦ ModuleCat.hom_ext (differential_squared B n))

@[simp]
theorem complex_d (n : ℕ) : (complex B).d n (n + 1) = ModuleCat.ofHom (differential B n) :=
  CochainComplex.of_d (fun n ↦ ModuleCat.of ℚ (Cochain B n))
    (fun n ↦ ModuleCat.ofHom (differential B n)) n

/-- The original inclusion of vanishing cochains in all simplex functions. -/
def inclusion : complex B ⟶ SubcomplexCochains.complex S where
  f n := ModuleCat.ofHom (LinearMap.ker (restrictionLinear B n)).subtype
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, SubcomplexCochains.complex_d]
    rfl

@[simp]
theorem inclusion_apply (n : ℕ) (φ : Cochain B n) : (inclusion B).f n φ = φ.val := rfl

theorem inclusion_comp_restriction : inclusion B ≫ restriction B = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact φ.property

/-- Extension by zero supplies every actual subcomplex cochain. -/
def extension (n : ℕ) (φ : SubcomplexCochains.Cochain B.toSSet n) :
    SubcomplexCochains.Cochain S n := by
  classical
  exact fun σ ↦ if h : σ ∈ B.obj (op ⦋n⦌) then φ ⟨σ, h⟩ else 0

@[simp]
theorem restriction_extension (n : ℕ) (φ : SubcomplexCochains.Cochain B.toSSet n) :
    restrictionLinear B n (extension B n φ) = φ := by
  classical
  funext σ
  simp only [restrictionLinear_apply, extension, dite_eq_left σ.property]
  exact congrArg φ (Subtype.ext rfl)

theorem restrictionLinear_surjective (n : ℕ) : Function.Surjective (restrictionLinear B n) :=
  fun φ ↦ ⟨extension B n φ, restriction_extension B n φ⟩

def shortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℕ) :=
  ShortComplex.mk (inclusion B) (restriction B) (inclusion_comp_restriction B)

theorem shortComplex_degreewise_shortExact (n : ℕ) :
    ((shortComplex B).map (HomologicalComplex.eval _ _ n)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro φ
    constructor
    · intro hφ
      exact ⟨⟨φ, hφ⟩, rfl⟩
    · rintro ⟨ψ, rfl⟩
      exact ψ.property
  · exact Subtype.val_injective
  · exact restrictionLinear_surjective B n

/-- The actual relative cochain sequence is short exact. -/
theorem shortComplex_shortExact : (shortComplex B).ShortExact :=
  shortExact_of_degreewise_shortExact _ (shortComplex_degreewise_shortExact B)

abbrev Cohomology (n : ℕ) := (complex B).homology n

/-- Forget relative support, using the original inclusion of actual cochains. -/
def forget (n : ℕ) : Cohomology B n ⟶ (SubcomplexCochains.complex S).homology n :=
  homologyMap (inclusion B) n

/-- Restriction on actual absolute cohomology. -/
def restrictCohomology (n : ℕ) :
    (SubcomplexCochains.complex S).homology n ⟶
      (SubcomplexCochains.complex B.toSSet).homology n :=
  homologyMap (restriction B) n

/-- The native relative connecting map from the original short exact sequence. -/
def connecting (n : ℕ) :
    (SubcomplexCochains.complex B.toSSet).homology n ⟶ Cohomology B (n + 1) :=
  (shortComplex_shortExact B).δ n (n + 1) (by simp)

def intersectionSequence (n : ℕ) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk (restrictCohomology B n) (connecting B n)
    ((shortComplex_shortExact B).comp_δ n (n + 1) (by simp))

theorem intersectionSequence_exact (n : ℕ) : (intersectionSequence B n).Exact :=
  (shortComplex_shortExact B).homology_exact₃ n (n + 1) (by simp)

@[simp]
theorem intersectionSequence_f (n : ℕ) : (intersectionSequence B n).f = restrictCohomology B n := rfl

@[simp]
theorem intersectionSequence_g (n : ℕ) : (intersectionSequence B n).g = connecting B n := rfl

def unionSequence (n : ℕ) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk (connecting B n) (forget B (n + 1))
    ((shortComplex_shortExact B).δ_comp n (n + 1) (by simp))

theorem unionSequence_exact (n : ℕ) : (unionSequence B n).Exact :=
  (shortComplex_shortExact B).homology_exact₁ n (n + 1) (by simp)

@[simp]
theorem unionSequence_f (n : ℕ) : (unionSequence B n).f = connecting B n := rfl

@[simp]
theorem unionSequence_g (n : ℕ) : (unionSequence B n).g = forget B (n + 1) := rfl

def pairSequence (n : ℕ) : ShortComplex (ModuleCat.{u} ℚ) :=
  (shortComplex B).map (homologyFunctor _ _ n)

theorem pairSequence_exact (n : ℕ) : (pairSequence B n).Exact :=
  (shortComplex_shortExact B).homology_exact₂ n

abbrev Cocycle (n : ℕ) := LinearMap.ker (differential B n)

def cocycleClass (n : ℕ) (φ : Cocycle B n) : Cohomology B n :=
  (complex B).homologyπ n ((complex B).cyclesMk φ.val (n + 1) (by simp) (by
    rw [complex_d]
    exact φ.property))

/-- Every actual relative class has a closed vanishing-cochain representative. -/
theorem cocycleClass_surjective (n : ℕ) : Function.Surjective (cocycleClass B n) := by
  intro z
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective ((complex B).homologyπ n)).mp inferInstance z
  let φ : Cocycle B n := ⟨(complex B).iCycles n c, by
    have h := congrArg (fun f ↦ f c) ((complex B).iCycles_d n (n + 1))
    rw [complex_d] at h
    exact h⟩
  refine ⟨φ, ?_⟩
  rw [cocycleClass]
  have hcycles : (complex B).cyclesMk φ.val (n + 1) (by simp) (by
      rw [complex_d]
      exact φ.property) = c := by
    apply (ModuleCat.mono_iff_injective ((complex B).iCycles n)).mp inferInstance
    exact (complex B).i_cyclesMk (i := n) φ.val (n + 1) (by simp) (by
      rw [complex_d]
      exact φ.property)
  rw [hcycles]
  exact hc

/-- The native relative boundary has the positive differential-of-extension sign. -/
theorem connecting_cocycleClass (n : ℕ)
    (u : SubcomplexConnectingRepresentative.Cocycle B.toSSet n)
    (v : SubcomplexCochains.Cochain S n) (w : Cocycle B (n + 1))
    (hv : restrictionLinear B n v = u.val)
    (hw : w.val.val = SubcomplexCochains.differential S n v) :
    connecting B n (SubcomplexConnectingRepresentative.cocycleClass B.toSSet n u) =
      cocycleClass B (n + 1) w := by
  exact (shortComplex_shortExact B).δ_apply n (n + 1) (by simp) u.val
    (by
      change (SubcomplexCochains.complex B.toSSet).d n (n + 1) u.val = 0
      rw [SubcomplexCochains.complex_d]
      exact u.property) v hv w.val
    (by
      change (inclusion B).f (n + 1) w.val = (SubcomplexCochains.complex S).d n (n + 1) v
      rw [SubcomplexCochains.complex_d]
      exact hw) ((n + 1) + 1) (by simp)

/-- Every original cocycle has an actual extension and a closed relative differential representative. -/
theorem exists_connecting_representative (n : ℕ)
    (u : SubcomplexConnectingRepresentative.Cocycle B.toSSet n) :
    ∃ (v : SubcomplexCochains.Cochain S n) (w : Cocycle B (n + 1)),
      restrictionLinear B n v = u.val ∧
      w.val.val = SubcomplexCochains.differential S n v ∧
      connecting B n (SubcomplexConnectingRepresentative.cocycleClass B.toSSet n u) =
        cocycleClass B (n + 1) w := by
  let v := extension B n u.val
  have hv : restrictionLinear B n v = u.val := restriction_extension B n u.val
  let w₀ : Cochain B (n + 1) := ⟨SubcomplexCochains.differential S n v, by
    rw [LinearMap.mem_ker, restriction_differential, hv]
    exact u.property⟩
  let w : Cocycle B (n + 1) := ⟨w₀, by
    apply Subtype.ext
    exact SubcomplexCochains.differential_squared S n v⟩
  exact ⟨v, w, hv, rfl, connecting_cocycleClass B n u v w hv rfl⟩

end Pair

section PairMaps

variable {S T : SSet.{u}} {A : S.Subcomplex} {B : T.Subcomplex}

/-- Original pullback under a genuine map of simplicial pairs. -/
def pullbackLinear (f : S ⟶ T) (h : A ≤ B.preimage f) (n : ℕ) :
    Cochain B n →ₗ[ℚ] Cochain A n where
  toFun φ := ⟨(SubcomplexCochains.pullback f).f n φ.val, by
    funext σ
    exact cochain_vanish B n φ ⟨f.app (op ⦋n⦌) σ.val, h _ σ.property⟩⟩
  map_add' φ ψ := Subtype.ext (map_add _ _ _)
  map_smul' q φ := by
    apply Subtype.ext
    funext σ
    rfl

def pullback (f : S ⟶ T) (h : A ≤ B.preimage f) : complex B ⟶ complex A where
  f n := ModuleCat.ofHom (pullbackLinear f h n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    have he := congrArg (fun g ↦ g.hom φ.val)
      ((SubcomplexCochains.pullback f).comm i (i + 1))
    rw [SubcomplexCochains.complex_d, SubcomplexCochains.complex_d] at he
    change SubcomplexCochains.differential S i ((SubcomplexCochains.pullback f).f i φ.val) =
      (SubcomplexCochains.pullback f).f (i + 1) (SubcomplexCochains.differential T i φ.val) at he
    exact he

@[reassoc]
theorem pullback_inclusion (f : S ⟶ T) (h : A ≤ B.preimage f) :
    pullback f h ≫ inclusion A = inclusion B ≫ SubcomplexCochains.pullback f := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- The original simplex map restricted to its actual subcomplexes. -/
def subcomplexMap (f : S ⟶ T) (h : A ≤ B.preimage f) : A.toSSet ⟶ B.toSSet where
  app n := ↾fun σ ↦ ⟨f.app n σ.val, h _ σ.property⟩
  naturality n m g := by
    ext σ
    apply Subtype.ext
    exact congrArg (fun p ↦ p σ.val) (f.naturality g)

@[reassoc]
theorem pullback_restriction (f : S ⟶ T) (h : A ≤ B.preimage f) :
    SubcomplexCochains.pullback f ≫ restriction A =
      restriction B ≫ SubcomplexCochains.pullback (subcomplexMap f h) := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- The original map of pairs gives a map of the actual relative short exact sequences. -/
def shortComplexMap (f : S ⟶ T) (h : A ≤ B.preimage f) : shortComplex B ⟶ shortComplex A where
  τ₁ := pullback f h
  τ₂ := SubcomplexCochains.pullback f
  τ₃ := SubcomplexCochains.pullback (subcomplexMap f h)
  comm₁₂ := pullback_inclusion f h
  comm₂₃ := pullback_restriction f h

/-- Naturality retains the original native relative connecting morphisms. -/
@[reassoc]
theorem connecting_naturality (f : S ⟶ T) (h : A ≤ B.preimage f) (n : ℕ) :
    connecting B n ≫ homologyMap (pullback f h) (n + 1) =
      homologyMap (SubcomplexCochains.pullback (subcomplexMap f h)) n ≫ connecting A n :=
  HomologySequence.δ_naturality (shortComplexMap f h)
    (shortComplex_shortExact B) (shortComplex_shortExact A) n (n + 1) (by simp)

/-- An actual simplicial isomorphism preserving both subcomplexes gives its original relative isomorphism. -/
def pullbackIsoOfLE (e : S ≅ T) (h : A ≤ B.preimage e.hom)
    (h' : B ≤ A.preimage e.inv) : complex B ≅ complex A where
  hom := pullback e.hom h
  inv := pullback e.inv h'
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext σ
    change φ.val ((e.inv ≫ e.hom).app (op ⦋n⦌) σ) = φ.val σ
    rw [e.inv_hom_id]
    rfl
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext σ
    change φ.val ((e.hom ≫ e.inv).app (op ⦋n⦌) σ) = φ.val σ
    rw [e.hom_inv_id]
    rfl

/-- Exact preimage identification supplies both original maps of pairs. -/
def pullbackIso (e : S ≅ T) (h : A = B.preimage e.hom) : complex B ≅ complex A :=
  pullbackIsoOfLE e h.le (by
    rw [h, ← SSet.Subcomplex.preimage_comp, e.inv_hom_id, SSet.Subcomplex.preimage_id])

@[simp]
theorem pullbackIso_hom (e : S ≅ T) (h : A = B.preimage e.hom) :
    (pullbackIso e h).hom = pullback e.hom h.le := rfl

end PairMaps

end HodgeConjecture.RelativeCochains
