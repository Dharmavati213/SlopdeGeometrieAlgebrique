/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# SGA 1, Exposé IX, §§5–6: functors between Galois categories

The translations of IX.5 and IX.6 into statements on fundamental groups rest on the dictionary of
V.6 between functors of Galois categories and continuous homomorphisms of fundamental groups. For
`H : C ⥤ C'` and a fibre functor `F'` on `C'` such that `H ⋙ F'` is a fibre functor,
`autMap H F' : Aut F' →* Aut (H ⋙ F')` is the induced continuous homomorphism; for the inverse
image along `S' ⟶ S` it is `π₁(S') → π₁(S)`.

* V.6.9, used in IX.5.6 and IX.6.1: `autMap` is surjective iff `H` preserves connected objects iff
  `H` is full (`tfae_surjective_autMap`).
* V.6.10, used in the remark after IX.5.3: `autMap` is bijective iff `H` is an equivalence.
* V.6.7: when `autMap` is surjective, the essential image of `H` consists of the objects on whose
  fibre the kernel acts trivially (`mem_essImage_iff`). The recognition of the kernel from the
  essential image (`ker_autMap_eq_iff`, `ker_autMap_eq_iff_of_family`) is how IX.5.6, IX.5.8,
  IX.6.2 and IX.6.11 pass from categories to groups.
-/

universe u₁ u₂ u₃ u₄ w

namespace SGA.SGA1.ExposeIX

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits PreGaloisCategory

section autMap

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w})

/-- The homomorphism `Aut F' → Aut (H ⋙ F')` induced by a functor `H : C ⥤ C'`. When `F'` is the
fibre functor at a geometric point of `S'` and `H` is the inverse image along `S' → S`, this is
the homomorphism `π₁(S') → π₁(S)`. -/
def autMap : Aut F' →* Aut (H ⋙ F') :=
  ((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F'

@[simp]
lemma autMap_hom_app (σ : Aut F') (X : C) :
    (autMap H F' σ).hom.app X = σ.hom.app (H.obj X) :=
  rfl

/-- `Aut F'` acts on the fibres of `H ⋙ F'`. -/
instance mulActionAutCompObj (X : C) : MulAction (Aut F') ((H ⋙ F').obj X) :=
  inferInstanceAs <| MulAction (Aut F') (F'.obj (H.obj X))

lemma autMap_smul (σ : Aut F') {X : C} (x : (H ⋙ F').obj X) :
    autMap H F' σ • x = σ • x :=
  rfl

instance isNaturalSMul_autComp : IsNaturalSMul (H ⋙ F') (Aut F') where
  naturality σ _ _ f x := (NatTrans.naturality_apply σ.hom (H.map f) x).symm

lemma toAut_eq_autMap : toAut (H ⋙ F') (Aut F') = autMap H F' := by
  ext σ X x
  rfl

lemma continuous_autMap : Continuous (autMap H F') := by
  rw [(autEmbedding_isClosedEmbedding (H ⋙ F')).isInducing.continuous_iff, continuous_pi_iff]
  intro X
  exact (continuous_apply (H.obj X)).comp (autEmbedding_isClosedEmbedding F').continuous

/-- Conjugation by an isomorphism of functors is continuous on automorphism groups. -/
lemma continuous_conjAut {F₁ F₂ : C ⥤ FintypeCat.{w}} (e : F₁ ≅ F₂) :
    Continuous (e.conjAut : Aut F₁ → Aut F₂) := by
  rw [(autEmbedding_isClosedEmbedding F₂).isInducing.continuous_iff, continuous_pi_iff]
  intro X
  have h : (fun σ ↦ autEmbedding F₂ (e.conjAut σ) X) =
      (e.app X).conjAut ∘ fun σ ↦ autEmbedding F₁ σ X := by
    ext σ : 1
    apply Iso.ext
    change ((e.conjAut σ).hom).app X = ((e.app X).conjAut (σ.app X)).hom
    rw [Iso.conjAut_hom, Iso.conj_apply]
    erw [Iso.conjAut_hom, Iso.conj_apply]
    simp
    rfl
  change Continuous (fun σ ↦ autEmbedding F₂ (e.conjAut σ) X)
  rw [h]
  exact continuous_of_discreteTopology.comp
    ((continuous_apply X).comp (autEmbedding_isClosedEmbedding F₁).continuous)

end autMap

/-- A normal subgroup `V` acts trivially on `G ⧸ V`. -/
lemma smul_quotient_eq_of_mem {G : Type*} [Group G] {V : Subgroup G} [V.Normal] {τ : G}
    (hτ : τ ∈ V) (x : G ⧸ V) : τ • x = x := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  rw [smul_eq_mul, mul_inv_rev]
  exact Subgroup.Normal.conj_mem' ‹_› _ (V.inv_mem hτ) g

section fiberKernel

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- The subgroup of `Aut F` acting trivially on the fibre `F.obj Y`. -/
def fiberKernel (Y : C) : Subgroup (Aut F) :=
  (MulAction.toPermHom (Aut F) (F.obj Y)).ker

lemma mem_fiberKernel {Y : C} {σ : Aut F} :
    σ ∈ fiberKernel F Y ↔ ∀ y : F.obj Y, σ • y = y := by
  simp [fiberKernel, MonoidHom.mem_ker, Equiv.Perm.ext_iff]

instance fiberKernel_normal (Y : C) : (fiberKernel F Y).Normal :=
  MonoidHom.normal_ker _

lemma isClosed_fiberKernel (Y : C) : IsClosed (fiberKernel F Y : Set (Aut F)) := by
  have : (fiberKernel F Y : Set (Aut F)) =
      ⋂ y : F.obj Y, (MulAction.stabilizer (Aut F) y : Set (Aut F)) := by
    ext σ
    simp [mem_fiberKernel]
  rw [this]
  exact isClosed_iInter fun y ↦ Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ y)

/-- The closed normal subgroup generated by `S` acts trivially on a fibre if and only if `S`
does. -/
lemma forall_mem_normalClosure_smul_eq_iff (S : Set (Aut F)) (Y : C) :
    (∀ σ ∈ (Subgroup.normalClosure S).topologicalClosure, ∀ y : F.obj Y, σ • y = y) ↔
      ∀ σ ∈ S, ∀ y : F.obj Y, σ • y = y := by
  simp only [← mem_fiberKernel]
  refine ⟨fun h σ hσ ↦ h σ (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)),
    fun h σ hσ ↦ ?_⟩
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal h)
    (isClosed_fiberKernel F Y) hσ

end fiberKernel

section connected

variable {C : Type u₁} [Category.{u₂} C] [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- V.5.3, converse direction: an object with nonempty fibre on which `Aut F` acts transitively is
connected. -/
lemma isConnected_of_isPretransitive (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] : IsConnected X where
  notInitial h := not_initial_of_inhabited F (Classical.arbitrary _) h
  noTrivialComponent Y i _ hY := by
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty F Y).mp hY
    have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    have hsurj : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) (F.map i y) x
      exact ⟨σ • y, by rw [← mulAction_naturality, hσ]⟩
    have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i F

lemma subsingleton_of_isTerminal {T : FintypeCat.{w}} (h : IsTerminal T) : Subsingleton T :=
  ⟨fun x y ↦ ConcreteCategory.congr_hom
    (h.hom_ext (FintypeCat.homMk fun _ : T ↦ x) (FintypeCat.homMk fun _ ↦ y)) x⟩

/-- The fibre of the terminal object is a point. -/
instance subsingleton_fiber_terminal : Subsingleton (F.obj (⊤_ C)) :=
  subsingleton_of_isTerminal ((IsTerminal.isTerminalObj F _ terminalIsTerminal))

instance nonempty_fiber_terminal : Nonempty (F.obj (⊤_ C)) :=
  ⟨(IsTerminal.isTerminalObj F _ terminalIsTerminal).from (FintypeCat.of PUnit) PUnit.unit⟩

/-- The two points of the fibre of `⊤ ⨿ ⊤` coming from the two summands are distinct. -/
lemma fiber_coprod_inl_ne_inr (t : F.obj (⊤_ C)) :
    F.map (coprod.inl : ⊤_ C ⟶ (⊤_ C) ⨿ (⊤_ C)) t ≠ F.map coprod.inr t := by
  have h := isColimitMapCoconeBinaryCofanEquiv (F ⋙ FintypeCat.incl) coprod.inl coprod.inr
    (isColimitOfPreserves (F ⋙ FintypeCat.incl) (coprodIsCoprod (⊤_ C) (⊤_ C)))
  obtain ⟨-, -, hc⟩ := (Types.binaryCofan_isColimit_iff _).mp ⟨h⟩
  intro heq
  exact Set.disjoint_iff.mp hc.disjoint ⟨⟨t, heq⟩, ⟨t, rfl⟩⟩

end connected

section galois

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- In the fundamental group `Aut F`, a closed normal subgroup `N` is separated from any element
outside it by an open normal subgroup containing `N` (`Aut F` is profinite). -/
lemma exists_normal_isOpen_of_notMem {N : Subgroup (Aut F)} [N.Normal]
    (hN : IsClosed (N : Set (Aut F))) {σ : Aut F} (hσ : σ ∉ N) :
    ∃ V : Subgroup (Aut F), V.Normal ∧ IsOpen (V : Set (Aut F)) ∧ N ≤ V ∧ σ ∉ V := by
  have hU : {τ : Aut F | σ * τ ∉ N} ∈ nhds (1 : Aut F) :=
    (hN.isOpen_compl.preimage (continuous_const_mul σ)).mem_nhds (by simpa using hσ)
  obtain ⟨⟨A, a, _⟩, -, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.mp hU
  have hW : (MulAction.stabilizer (Aut F) a).Normal := stabilizer_normal_of_isGalois F A a
  refine ⟨N ⊔ MulAction.stabilizer (Aut F) a, inferInstance,
    Subgroup.isOpen_mono le_sup_right (stabilizer_isOpen _ a), le_sup_left, fun h ↦ ?_⟩
  obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp h
  exact hA (Subgroup.inv_mem _ hw) (by simpa using hn)

/-- In the fundamental group `Aut F`, a closed subgroup `N` (not necessarily normal) is separated
from any element `σ` outside it by an open normal subgroup `V`: `σ ∉ N ⊔ V`, where `N ⊔ V = N V` is
an open subgroup containing `N`. -/
lemma exists_normal_isOpen_notMem_sup {N : Subgroup (Aut F)} (hN : IsClosed (N : Set (Aut F)))
    {σ : Aut F} (hσ : σ ∉ N) :
    ∃ V : Subgroup (Aut F), V.Normal ∧ IsOpen (V : Set (Aut F)) ∧ σ ∉ N ⊔ V := by
  have hU : {τ : Aut F | σ * τ ∉ N} ∈ nhds (1 : Aut F) :=
    (hN.isOpen_compl.preimage (continuous_const_mul σ)).mem_nhds (by simpa using hσ)
  obtain ⟨⟨A, a, _⟩, -, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.mp hU
  have hW : (MulAction.stabilizer (Aut F) a).Normal := stabilizer_normal_of_isGalois F A a
  refine ⟨MulAction.stabilizer (Aut F) a, hW, stabilizer_isOpen _ a, fun h ↦ ?_⟩
  obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp h
  exact hA (Subgroup.inv_mem _ hw) (by simpa using hn)

open scoped FintypeCatDiscrete in
private lemma exists_fiber_equiv_aux (T : Type w) [Finite T] [MulAction (Aut F) T]
    (hT : ∀ x : T, IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F))) :
    ∃ (X : C) (e : F.obj X ≃ T), ∀ (σ : Aut F) (x : F.obj X), e (σ • x) = σ • e x := by
  let _ : TopologicalSpace T := ⊥
  have : DiscreteTopology T := ⟨rfl⟩
  have hc : ContinuousSMul (Aut F) T := continuousSMul_iff_stabilizer_isOpen.mpr hT
  let X₀ : ContAction FintypeCat (Aut F) :=
    ⟨Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of T), hc⟩
  obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := functorToContAction F) X₀
  let j := (Action.forget FintypeCat (Aut F)).mapIso ((ObjectProperty.ι _).mapIso i)
  refine ⟨X, FintypeCat.equivEquivIso.symm j, fun σ x ↦ ?_⟩
  exact ConcreteCategory.congr_hom (((ObjectProperty.ι _).mapIso i).hom.comm σ) x

/-- Every finite `Aut F`-set with open stabilizers is the fibre of an object (essential
surjectivity in V.4.1, in a form without universe restrictions). -/
lemma exists_fiber_equiv (T : Type*) [Finite T] [MulAction (Aut F) T]
    (hT : ∀ x : T, IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F))) :
    ∃ (X : C) (e : F.obj X ≃ T), ∀ (σ : Aut F) (x : F.obj X), e (σ • x) = σ • e x := by
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin T
  let e₁ : ULift.{w} (Fin n) ≃ T := Equiv.ulift.trans e₀.symm
  let _ : MulAction (Aut F) (ULift.{w} (Fin n)) := e₁.mulAction (Aut F)
  have hT' (x : ULift.{w} (Fin n)) :
      IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F)) := by
    convert hT (e₁ x) using 2
    ext σ
    change e₁.symm (σ • e₁ x) = x ↔ σ • e₁ x = e₁ x
    rw [Equiv.symm_apply_eq]
  obtain ⟨X, e, he⟩ := exists_fiber_equiv_aux F (ULift.{w} (Fin n)) hT'
  refine ⟨X, e.trans e₁, fun σ x ↦ ?_⟩
  change e₁ (e (σ • x)) = σ • e₁ (e x)
  rw [he]
  exact e₁.apply_symm_apply _

end galois

section V69

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  [GaloisCategory C] [GaloisCategory C'] (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w})
  [FiberFunctor F'] [FiberFunctor (H ⋙ F')]

/-- V.6.9, (i) ⇒ (ii): if `Aut F' → Aut (H ⋙ F')` is surjective, `H` preserves connected
objects. -/
lemma preservesIsConnected_of_surjective (hu : Function.Surjective (autMap H F')) :
    PreservesIsConnected H where
  preserves {X} _ := by
    have : Nonempty (F'.obj (H.obj X)) := nonempty_fiber_of_isConnected (H ⋙ F') X
    have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := ⟨fun x y ↦ by
      obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut (H ⋙ F'))
        (show (H ⋙ F').obj X from x) (show (H ⋙ F').obj X from y)
      obtain ⟨σ, rfl⟩ := hu τ
      exact ⟨σ, hτ⟩⟩
    exact isConnected_of_isPretransitive F' (H.obj X)

/-- V.6.9, (ii) ⇒ (i): if `H` preserves connected objects, `Aut F' → Aut (H ⋙ F')` is
surjective. -/
lemma surjective_of_preservesIsConnected [PreservesIsConnected H] :
    Function.Surjective (autMap H F') := by
  have (X : C) : ContinuousSMul (Aut F') ((H ⋙ F').obj X) := continuousSMul_aut_fiber F' (H.obj X)
  rw [← toAut_eq_autMap]
  refine toAut_surjective_of_isPretransitive _ _ fun X _ ↦ ?_
  have : IsConnected (H.obj X) := PreservesIsConnected.preserves
  exact ⟨fun x y ↦ MulAction.exists_smul_eq (Aut F') (show F'.obj (H.obj X) from x) y⟩

/-- V.6.9, (i) ⇒ (iii): if `Aut F' → Aut (H ⋙ F')` is surjective, `H` is full. -/
lemma full_of_surjective (hu : Function.Surjective (autMap H F')) : H.Full where
  map_surjective {X Y} f := by
    let g : (functorToAction (H ⋙ F')).obj X ⟶ (functorToAction (H ⋙ F')).obj Y :=
      { hom := F'.map f
        comm := fun τ ↦ by
          obtain ⟨σ, rfl⟩ := hu τ
          exact (σ.hom.naturality f).symm }
    obtain ⟨g', hg'⟩ := (functorToAction (H ⋙ F')).map_surjective g
    exact ⟨g', F'.map_injective (congrArg Action.Hom.hom hg')⟩

include F' in
/-- V.6.9, (iii) ⇒ (ii): if `H` is full, `H` preserves connected objects. -/
lemma preservesIsConnected_of_full [H.Full] : PreservesIsConnected H where
  preserves {X} _ := by
    let F := H ⋙ F'
    have : Nonempty (F'.obj (H.obj X)) := nonempty_fiber_of_isConnected F X
    by_contra hX
    obtain ⟨x₀, y₀, hxy⟩ : ∃ x₀ y₀ : F'.obj (H.obj X), ∀ σ : Aut F', σ • x₀ ≠ y₀ := by
      by_contra! h
      exact hX (have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := ⟨h⟩
        isConnected_of_isPretransitive F' _)
    obtain ⟨t⟩ : Nonempty (F.obj (⊤_ C)) := inferInstance
    let T : C := (⊤_ C) ⨿ (⊤_ C)
    let a : F'.obj (H.obj T) := F.map coprod.inl t
    let b : F'.obj (H.obj T) := F.map coprod.inr t
    have hab : a ≠ b := fiber_coprod_inl_ne_inr F t
    have hfix (σ : Aut F') (f : ⊤_ C ⟶ T) : σ • F.map f t = F.map f t := by
      change σ • F'.map (H.map f) t = F'.map (H.map f) t
      rw [mulAction_naturality]
      congr 1
      exact Subsingleton.elim (α := F.obj (⊤_ C)) _ _
    have hfixF (τ : Aut F) (f : ⊤_ C ⟶ T) : τ • F.map f t = F.map f t := by
      rw [mulAction_naturality]
      congr 1
      exact Subsingleton.elim _ _
    classical
    let O := MulAction.orbit (Aut F') x₀
    have hO (σ : Aut F') (x : F'.obj (H.obj X)) : σ • x ∈ O ↔ x ∈ O := by
      simp only [O, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨σ⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul]⟩
      · rintro ⟨g, hg⟩
        exact ⟨σ * g, by rw [mul_smul, hg]⟩
    let φ₀ : F'.obj (H.obj X) → F'.obj (H.obj T) := fun x ↦ if x ∈ O then a else b
    have hφ₀ (σ : Aut F') (x : F'.obj (H.obj X)) : φ₀ (σ • x) = σ • φ₀ x := by
      simp only [φ₀, hO]
      split_ifs
      · exact (hfix σ _).symm
      · exact (hfix σ _).symm
    let φ : (functorToAction F').obj (H.obj X) ⟶ (functorToAction F').obj (H.obj T) :=
      { hom := FintypeCat.homMk φ₀
        comm := fun σ ↦ by
          ext x
          exact hφ₀ σ x }
    obtain ⟨ψ, hψ⟩ := (functorToAction F').map_surjective φ
    obtain ⟨g, hg⟩ := H.map_surjective ψ
    have hFg (x : F.obj X) : F.map g x = φ₀ x := by
      change F'.map (H.map g) x = φ₀ x
      rw [hg]
      exact ConcreteCategory.congr_hom (congrArg Action.Hom.hom hψ) x
    obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut F) (show F.obj X from x₀) y₀
    have h₁ : φ₀ y₀ = b := ite_eq_right (fun ⟨σ, hσ⟩ ↦ hxy σ hσ)
    have h₂ : φ₀ x₀ = a := ite_eq_left (MulAction.mem_orbit_self x₀)
    apply hab
    rw [← h₁, ← hFg, ← hτ, ← mulAction_naturality, hFg, h₂]
    exact (hfixF τ _).symm

/-- V.6.9. -/
theorem tfae_surjective_autMap :
    List.TFAE [Function.Surjective (autMap H F'), PreservesIsConnected H, H.Full] := by
  tfae_have 1 → 2 := preservesIsConnected_of_surjective H F'
  tfae_have 2 → 1 := fun _ ↦ surjective_of_preservesIsConnected H F'
  tfae_have 1 → 3 := full_of_surjective H F'
  tfae_have 3 → 2 := fun _ ↦ preservesIsConnected_of_full H F'
  tfae_finish

omit [GaloisCategory C'] [FiberFunctor F'] in
include F' in
lemma faithful_of_fiberFunctor : H.Faithful := Functor.Faithful.of_comp H F'

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
/-- The kernel of `Aut F' → Aut (H ⋙ F')` acts trivially on the fibres of objects in the essential
image of `H`. -/
lemma smul_eq_of_mem_essImage {Y : C'} (hY : H.essImage Y) {σ : Aut F'}
    (hσ : σ ∈ (autMap H F').ker) (y : F'.obj Y) : σ • y = y := by
  obtain ⟨X, ⟨e⟩⟩ := hY
  have h1 : σ.hom.app (H.obj X) = 𝟙 _ :=
    congrArg (fun τ : Aut (H ⋙ F') ↦ τ.hom.app X) (MonoidHom.mem_ker.mp hσ)
  obtain ⟨x, rfl⟩ : ∃ x, F'.map e.hom x = y :=
    ⟨F'.map e.inv y, FintypeCat.inv_hom_id_apply (F'.mapIso e) y⟩
  rw [mulAction_naturality]
  congr 1
  exact ConcreteCategory.congr_hom h1 x

/-- Conversely, when `Aut F' → Aut (H ⋙ F')` is surjective, an object on whose fibre the kernel
acts trivially is in the essential image of `H` (V.6.7, second part). -/
lemma mem_essImage_of_smul_eq (hu : Function.Surjective (autMap H F')) (Y : C')
    (hY : ∀ σ ∈ (autMap H F').ker, ∀ y : F'.obj Y, σ • y = y) : H.essImage Y := by
  let s := Function.surjInv hu
  have hs (σ : Aut F') (y : F'.obj Y) : s (autMap H F' σ) • y = σ • y := by
    have hk : σ⁻¹ * s (autMap H F' σ) ∈ (autMap H F').ker := by
      simp [MonoidHom.mem_ker, Function.surjInv_eq hu, s]
    calc s (autMap H F' σ) • y = σ • (σ⁻¹ * s (autMap H F' σ)) • y := by
          rw [smul_smul, mul_inv_cancel_left]
      _ = σ • y := by rw [hY _ hk]
  let _ : MulAction (Aut (H ⋙ F')) (F'.obj Y) :=
    { smul τ y := s τ • y
      one_smul y := hY _ (by simp [MonoidHom.mem_ker, Function.surjInv_eq hu, s]) y
      mul_smul τ₁ τ₂ y := by
        change s (τ₁ * τ₂) • y = s τ₁ • s τ₂ • y
        have hk : (s τ₁ * s τ₂)⁻¹ * s (τ₁ * τ₂) ∈ (autMap H F').ker := by
          simp [MonoidHom.mem_ker, Function.surjInv_eq hu, s]
        calc s (τ₁ * τ₂) • y = (s τ₁ * s τ₂) • ((s τ₁ * s τ₂)⁻¹ * s (τ₁ * τ₂)) • y := by
              rw [smul_smul, mul_inv_cancel_left]
          _ = s τ₁ • s τ₂ • y := by rw [hY _ hk, mul_smul] }
  have hq : Topology.IsQuotientMap (autMap H F') :=
    (continuous_autMap H F').isClosedMap.isQuotientMap (continuous_autMap H F') hu
  have hstab (y : F'.obj Y) :
      IsOpen (MulAction.stabilizer (Aut (H ⋙ F')) y : Set (Aut (H ⋙ F'))) := by
    rw [← hq.isOpen_preimage]
    convert stabilizer_isOpen (Aut F') y using 1
    ext σ
    change s (autMap H F' σ) • y = y ↔ σ • y = y
    rw [hs]
  obtain ⟨X, e, he⟩ := exists_fiber_equiv (H ⋙ F') (F'.obj Y) hstab
  let i : (functorToAction F').obj (H.obj X) ≅ (functorToAction F').obj Y :=
    Action.mkIso (FintypeCat.equivEquivIso e) fun σ ↦ by
      ext x
      exact (he (autMap H F' σ) x).trans (hs σ _)
  exact ⟨X, ⟨(functorToAction F').preimageIso i⟩⟩

/-- When `Aut F' → Aut (H ⋙ F')` is surjective, the essential image of `H` consists of the objects
on whose fibre its kernel acts trivially (V.6.7). -/
theorem mem_essImage_iff (hu : Function.Surjective (autMap H F')) (Y : C') :
    H.essImage Y ↔ ∀ σ ∈ (autMap H F').ker, ∀ y : F'.obj Y, σ • y = y :=
  ⟨fun hY _ hσ y ↦ smul_eq_of_mem_essImage H F' hY hσ y, mem_essImage_of_smul_eq H F' hu Y⟩

omit [GaloisCategory C] [FiberFunctor (H ⋙ F')] in
/-- Recognition of the kernel of `Aut F' → Aut (H ⋙ F')`: if the objects of `C'` in the essential
image of `H` are exactly those on whose fibre the closed normal subgroup `N` acts trivially, then
`N` is the kernel. This is how the descriptions of fundamental groups in IX.5 and IX.6 are
obtained from descent statements. -/
theorem ker_autMap_eq (N : Subgroup (Aut F')) [N.Normal] (hN : IsClosed (N : Set (Aut F')))
    (h : ∀ Y : C', H.essImage Y ↔ ∀ σ ∈ N, ∀ y : F'.obj Y, σ • y = y) :
    (autMap H F').ker = N := by
  apply le_antisymm
  · intro σ hσ
    by_contra hσN
    obtain ⟨V, hVn, hVo, hNV, hσV⟩ := exists_normal_isOpen_of_notMem F' hN hσN
    have : Finite (Aut F' ⧸ V) := V.quotient_finite_of_isOpen hVo
    have hstab (x : Aut F' ⧸ V) : IsOpen (MulAction.stabilizer (Aut F') x : Set (Aut F')) :=
      Subgroup.isOpen_mono (fun τ hτ ↦ smul_quotient_eq_of_mem hτ x) hVo
    obtain ⟨Y, e, he⟩ := exists_fiber_equiv F' (Aut F' ⧸ V) hstab
    have hY : H.essImage Y := (h Y).mpr fun τ hτ y ↦
      e.injective (by rw [he, smul_quotient_eq_of_mem (hNV hτ)])
    have h1 := congrArg e (smul_eq_of_mem_essImage H F' hY hσ (e.symm 1))
    rw [he, Equiv.apply_symm_apply, ← QuotientGroup.mk_one, MulAction.Quotient.smul_mk,
      smul_eq_mul, mul_one, QuotientGroup.mk_one, QuotientGroup.eq_one_iff] at h1
    exact hσV h1
  · intro σ hσ
    rw [MonoidHom.mem_ker]
    ext X x
    exact (h (H.obj X)).mp (H.obj_mem_essImage X) σ hσ x

/-- When `Aut F' → Aut (H ⋙ F')` is surjective, its kernel is the closed normal subgroup `N` if and
only if the essential image of `H` consists of the objects on whose fibre `N` acts trivially. -/
theorem ker_autMap_eq_iff (hu : Function.Surjective (autMap H F')) (N : Subgroup (Aut F'))
    [N.Normal] (hN : IsClosed (N : Set (Aut F'))) :
    (autMap H F').ker = N ↔ ∀ Y : C', H.essImage Y ↔ ∀ σ ∈ N, ∀ y : F'.obj Y, σ • y = y := by
  refine ⟨fun h Y ↦ ?_, ker_autMap_eq H F' N hN⟩
  rw [← h]
  exact mem_essImage_iff H F' hu Y

/-- Variant of `ker_autMap_eq_iff` for the closed normal subgroup generated by the images of a
family of homomorphisms `vᵢ : Gᵢ → Aut F'`: when `Aut F' → Aut (H ⋙ F')` is surjective, this
subgroup is its kernel if and only if the essential image of `H` consists of the objects on whose
fibre all the `vᵢ(Gᵢ)` act trivially. This is the abstract form of IX.5.8 (with the inertia
groups) and of IX.6.11 (with the fundamental groups of the geometric fibres). -/
theorem ker_autMap_eq_iff_of_family (hu : Function.Surjective (autMap H F')) {ι : Type*}
    {G : ι → Type*} [∀ i, Group (G i)] (v : ∀ i, G i →* Aut F') :
    (autMap H F').ker =
        (Subgroup.normalClosure (⋃ i, Set.range (v i))).topologicalClosure ↔
      ∀ Y : C', H.essImage Y ↔ ∀ i (g : G i) (y : F'.obj Y), v i g • y = y := by
  have := Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure (⋃ i, Set.range (v i)))
  rw [ker_autMap_eq_iff H F' hu _ (Subgroup.isClosed_topologicalClosure _)]
  refine forall_congr' fun Y ↦ iff_congr Iff.rfl ?_
  rw [forall_mem_normalClosure_smul_eq_iff]
  refine ⟨fun h i g y ↦ h _ (Set.mem_iUnion.mpr ⟨i, g, rfl⟩) y, fun h σ hσ y ↦ ?_⟩
  obtain ⟨i, g, rfl⟩ := Set.mem_iUnion.mp hσ
  exact h i g y

/-- A surjective `Aut F' → Aut (H ⋙ F')` identifies `Aut (H ⋙ F')` with the quotient of `Aut F'` by
its kernel, as topological groups. -/
noncomputable def quotientKerAutMapEquiv (hu : Function.Surjective (autMap H F')) :
    Aut F' ⧸ (autMap H F').ker ≃ₜ* Aut (H ⋙ F') :=
  let e := QuotientGroup.quotientKerEquivOfSurjective (autMap H F') hu
  have he : e ∘ QuotientGroup.mk = autMap H F' := rfl
  have hc : Continuous e :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (he ▸ continuous_autMap H F')
  { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
/-- If `Aut F' → Aut (H ⋙ F')` is surjective and `Aut F'` is topologically generated by a finite
set, so is `Aut (H ⋙ F')`. -/
lemma exists_finite_topologicalClosure_eq_top (hu : Function.Surjective (autMap H F'))
    {s : Set (Aut F')} (hs : s.Finite) (h : (Subgroup.closure s).topologicalClosure = ⊤) :
    ∃ t : Set (Aut (H ⋙ F')), t.Finite ∧ (Subgroup.closure t).topologicalClosure = ⊤ :=
  ⟨autMap H F' '' s, hs.image _, by
    rw [← MonoidHom.map_closure]
    exact hu.denseRange.topologicalClosure_map_subgroup (continuous_autMap H F') h⟩

/-- Variant of `quotientKerAutMapEquiv` for a subgroup known to be the kernel. -/
noncomputable def quotientEquivOfKerEq (hu : Function.Surjective (autMap H F'))
    (N : Subgroup (Aut F')) [N.Normal] (h : (autMap H F').ker = N) :
    Aut F' ⧸ N ≃ₜ* Aut (H ⋙ F') := by
  subst h
  exact quotientKerAutMapEquiv H F' hu

/-- V.6.10: `Aut F' → Aut (H ⋙ F')` is bijective if and only if `H` is an equivalence. -/
theorem bijective_autMap_iff : Function.Bijective (autMap H F') ↔ H.IsEquivalence := by
  constructor
  · rintro ⟨hi, hs⟩
    have := full_of_surjective H F' hs
    have := faithful_of_fiberFunctor H F'
    have : H.EssSurj := ⟨fun Y ↦ mem_essImage_of_smul_eq H F' hs Y fun σ hσ y ↦ by
      rw [(injective_iff_map_eq_one _).mp hi σ hσ, one_smul]⟩
    exact { }
  · intro _
    have := preservesIsConnected_of_full H F'
    refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_,
      surjective_of_preservesIsConnected H F'⟩
    ext Y y
    exact smul_eq_of_mem_essImage H F' (Functor.EssSurj.mem_essImage H Y) hσ y

/-- The remark after IX.5.3 in abstract form: an equivalence `H` induces an isomorphism of
fundamental groups (applied with IX.4.10, this is the topological invariance of `π₁`). -/
noncomputable def autMapEquiv [H.IsEquivalence] : Aut F' ≃ₜ* Aut (H ⋙ F') :=
  let e := MulEquiv.ofBijective (autMap H F') ((bijective_autMap_iff H F').mpr inferInstance)
  have hc : Continuous e := continuous_autMap H F'
  { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

end V69

end SGA.SGA1.ExposeIX
