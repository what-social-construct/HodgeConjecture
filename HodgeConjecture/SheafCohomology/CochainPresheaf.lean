module

public import HodgeConjecture.SheafCohomology.LinearSheaves
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Homotopy.LocallyContractible

@[expose] public noncomputable section

/-!
# Open-subspace presheaves of an existing cochain functor

This constructs no new cochain model. It evaluates the given functor on
native open subspaces, retaining its differentials, restrictions and unit.
Contractible-neighborhood arguments are shared between coefficient rings.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite Filter Topology

namespace HodgeConjecture.SheafCohomology.CochainPresheaf

variable (k : Type) [CommRing k]
  (F : TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} k) ℕ) (X : TopCat.{0})

def presheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{0} k) X where
  obj U := (F.obj (op ((Opens.toTopCat X).obj U.unop))).X n
  map i := (F.map ((Opens.toTopCat X).map i.unop).op).f n
  map_id U := by simp
  map_comp i j := by simp

def differential (n : ℕ) : presheaf k F X n ⟶ presheaf k F X (n + 1) where
  app U := (F.obj (op ((Opens.toTopCat X).obj U.unop))).d n (n + 1)
  naturality _ _ i := (F.map ((Opens.toTopCat X).map i.unop).op).comm n (n + 1)

theorem differential_comp (n : ℕ) : differential k F X n ≫ differential k F X (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  exact (F.obj (op ((Opens.toTopCat X).obj U.unop))).d_comp_d _ _ _

def complex : CochainComplex (TopCat.Presheaf (ModuleCat.{0} k) X) ℕ :=
  CochainComplex.of (presheaf k F X) (differential k F X) (differential_comp k F X)

@[simp]
theorem complex_d (n : ℕ) : (complex k F X).d n (n + 1) = differential k F X n :=
  CochainComplex.of_d _ _ n

def sectionComplexIso (U : Opens X) : F.obj (op ((Opens.toTopCat X).obj U)) ≅
    (((evaluation _ (ModuleCat.{0} k)).obj (op U)).mapHomologicalComplex (.up ℕ)).obj
      (complex k F X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ ((complex k F X).d i (i + 1)).app (op U) =
      (F.obj (op ((Opens.toTopCat X).obj U))).d i (i + 1) ≫ 𝟙 _
    rw [complex_d]
    simp only [differential, Category.id_comp, Category.comp_id])

def sheaf (n : ℕ) : TopCat.Sheaf (ModuleCat.{0} k) X :=
  (sheafification k X).obj (presheaf k F X n)

def sheafDifferential (n : ℕ) : sheaf k F X n ⟶ sheaf k F X (n + 1) :=
  (sheafification k X).map (differential k F X n)

theorem sheafDifferential_comp (n : ℕ) :
    sheafDifferential k F X n ≫ sheafDifferential k F X (n + 1) = 0 := by
  rw [sheafDifferential, sheafDifferential, ← Functor.map_comp, differential_comp, Functor.map_zero]

def sheafComplex : CochainComplex (TopCat.Sheaf (ModuleCat.{0} k) X) ℕ :=
  sheafifyComplex k X (complex k F X)

@[simp]
theorem sheafComplex_d (n : ℕ) :
    (sheafComplex k F X).d n (n + 1) = sheafDifferential k F X n :=
  congrArg ((sheafification k X).map) (CochainComplex.of_d _ _ n)

def globalUnit : F.obj (op X) ⟶
    ((SheafHypercohomology.globalSections k X).mapHomologicalComplex (.up ℕ)).obj
      (sheafComplex k F X) :=
  (F.mapIso (Opens.inclusionTopIso X).op).hom ≫ (sectionComplexIso k F X ⊤).hom ≫
    (((evaluation _ (ModuleCat.{0} k)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).map
      (toSheafifyComplex k X (complex k F X))

/-- Local positive primitives use the same contractible-neighborhood argument for every coefficient ring. -/
theorem locally_exact_positive [StronglyLocallyContractibleSpace X]
    (hpos : ∀ (S : TopCat.{0}) [ContractibleSpace S] (n : ℕ)
      (z : (F.obj (op S)).X (n + 1)), (F.obj (op S)).d (n + 1) (n + 2) z = 0 →
        ∃ b : (F.obj (op S)).X n, (F.obj (op S)).d n (n + 1) b = z)
    (n : ℕ) (U : Opens X) (z : (presheaf k F X (n + 1)).obj (op U))
    (hz : (differential k F X (n + 1)).app (op U) z = 0) (p : X) (hp : p ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), p ∈ V ∧
      ∃ b : (presheaf k F X n).obj (op V),
        (differential k F X n).app (op V) b = (presheaf k F X (n + 1)).map (homOfLE hVU).op z := by
  change (F.obj (op ((Opens.toTopCat X).obj U))).d (n + 1) (n + 2) z = 0 at hz
  obtain ⟨S, ⟨hS, hcS⟩, hSU⟩ := (contractible_basis p).mem_iff.mp (U.isOpen.mem_nhds hp)
  let : ContractibleSpace S := hcS
  let f : TopCat.of S ⟶ (Opens.toTopCat X).obj U := TopCat.ofHom (ContinuousMap.inclusion hSU)
  obtain ⟨b, hb⟩ := hpos (TopCat.of S) n ((F.map f.op).f (n + 1) z) (by
    rw [← ConcreteCategory.comp_apply, (F.map f.op).comm, ConcreteCategory.comp_apply, hz, map_zero])
  obtain ⟨V, hVS, hVo, hpV⟩ := mem_nhds_iff.mp hS
  let g : (Opens.toTopCat X).obj ⟨V, hVo⟩ ⟶ TopCat.of S := TopCat.ofHom (ContinuousMap.inclusion hVS)
  refine ⟨⟨V, hVo⟩, hVS.trans hSU, hpV, (F.map g.op).f n b, ?_⟩
  change (F.obj (op ((Opens.toTopCat X).obj ⟨V, hVo⟩))).d n (n + 1) ((F.map g.op).f n b) = _
  rw [← ConcreteCategory.comp_apply, (F.map g.op).comm, ConcreteCategory.comp_apply, hb]
  change ((F.map f.op ≫ F.map g.op).f (n + 1)) z = _
  rw [← F.map_comp]
  rfl

/-- The same neighborhood argument for degree-zero constants and every coefficient ring. -/
theorem locally_constant_zero [StronglyLocallyContractibleSpace X]
    (c : ∀ Y : TopCat.{0}, k →ₗ[k] (F.obj (op Y)).X 0)
    (hc : ∀ {Y Z : TopCat.{0}} (f : Y ⟶ Z) (a : k), (F.map f.op).f 0 (c Z a) = c Y a)
    (hzero : ∀ (S : TopCat.{0}) [ContractibleSpace S] (_x : S) (z : (F.obj (op S)).X 0),
      (F.obj (op S)).d 0 1 z = 0 → ∃ a : k, c S a = z)
    (U : Opens X) (z : (presheaf k F X 0).obj (op U))
    (hz : (differential k F X 0).app (op U) z = 0) (p : X) (hp : p ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), p ∈ V ∧ ∃ a : k,
      c ((Opens.toTopCat X).obj V) a = (presheaf k F X 0).map (homOfLE hVU).op z := by
  change (F.obj (op ((Opens.toTopCat X).obj U))).d 0 1 z = 0 at hz
  obtain ⟨S, ⟨hS, hcS⟩, hSU⟩ := (contractible_basis p).mem_iff.mp (U.isOpen.mem_nhds hp)
  let : ContractibleSpace S := hcS
  let f : TopCat.of S ⟶ (Opens.toTopCat X).obj U := TopCat.ofHom (ContinuousMap.inclusion hSU)
  obtain ⟨a, ha⟩ := hzero (TopCat.of S) ⟨p, mem_of_mem_nhds hS⟩ ((F.map f.op).f 0 z) (by
    rw [← ConcreteCategory.comp_apply, (F.map f.op).comm, ConcreteCategory.comp_apply, hz, map_zero])
  obtain ⟨V, hVS, hVo, hpV⟩ := mem_nhds_iff.mp hS
  let g : (Opens.toTopCat X).obj ⟨V, hVo⟩ ⟶ TopCat.of S := TopCat.ofHom (ContinuousMap.inclusion hVS)
  refine ⟨⟨V, hVo⟩, hVS.trans hSU, hpV, a, ?_⟩
  have he := congrArg (fun w ↦ (F.map g.op).f 0 w) ha
  rw [hc] at he
  change c ((Opens.toTopCat X).obj ⟨V, hVo⟩) a = ((F.map f.op ≫ F.map g.op).f 0) z at he
  rw [← F.map_comp] at he
  exact he

end HodgeConjecture.SheafCohomology.CochainPresheaf
