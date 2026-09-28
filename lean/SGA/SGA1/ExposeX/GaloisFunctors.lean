/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Galois.EssSurj

/-!
# SGA 1, Exposé X: functors of Galois categories and homotopy exact sequences

Exposé X proves its statements on fundamental groups (X.1.4, X.2.1, X.3.3, …) by proving
statements on étale coverings and translating them through the dictionary of Exposé V, §6
between exact functors of Galois categories and continuous homomorphisms of their fundamental
groups. This file proves the part of that dictionary used in Exposé X, for mathlib's Galois
categories (`GaloisCategory`, `FiberFunctor`), with fundamental group `Aut F`:

* a functor `H : C ⥤ D` with `H ⋙ F' ≅ F` induces a continuous homomorphism
  `autWhiskerLeft H e : Aut F' →* Aut F` (V.6.1–V.6.3);
* `autWhiskerLeft H e` is surjective iff `H` sends connected objects to connected objects
  (V.6.9);
* an equivalence induces an isomorphism (V.6.10);
* sections are fixed points, and completely decomposed objects are those on whose fibre
  `Aut F` acts trivially (V.6.4); `autWhiskerLeft H e` is trivial iff `H` sends every object
  to a completely decomposed one (V.6.5);
* the exactness criterion V.6.11 in both directions, whence the formal part of the homotopy
  exact sequence X.1.4 and its equivalence with X.1.3 (`surjective_and_range_eq_ker`,
  `range_eq_ker_iff`).

These are the steps by which SGA deduces X.1.4 from X.1.3, X.2.1 from IX.1.10 and the last
assertion of X.3.3 from its first.
-/

universe u₁ u₂ v₁ v₂ t₁ t₂ w

namespace SGA.SGA1.ExposeX

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open scoped Pointwise

variable {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]
  {E : Type t₁} [Category.{t₂} E]

section Hom

variable {F : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}} (H : C ⥤ D) (e : H ⋙ F' ≅ F)

/-- V.6.1: the homomorphism `Aut F' → Aut F` of fundamental groups induced by a functor
`H : C ⥤ D` together with an isomorphism `H ⋙ F' ≅ F` of fibre functors. It sends `σ` to the
automorphism `σ` whiskered by `H`, transported along `e`. -/
def autWhiskerLeft : Aut F' →* Aut F where
  toFun σ := e.symm ≪≫ Functor.isoWhiskerLeft H σ ≪≫ e
  map_one' := Aut.ext <| by
    ext X : 2
    change e.inv.app X ≫ 𝟙 _ ≫ e.hom.app X = 𝟙 _
    simp
  map_mul' σ τ := Aut.ext <| by
    ext X : 2
    change e.inv.app X ≫ (τ.hom.app (H.obj X) ≫ σ.hom.app (H.obj X)) ≫ e.hom.app X =
      (e.inv.app X ≫ τ.hom.app (H.obj X) ≫ e.hom.app X) ≫
        (e.inv.app X ≫ σ.hom.app (H.obj X) ≫ e.hom.app X)
    simp

lemma autWhiskerLeft_smul (σ : Aut F') {X : C} (x : F.obj X) :
    autWhiskerLeft H e σ • x = e.hom.app X (σ.hom.app (H.obj X) (e.inv.app X x)) := rfl

lemma autWhiskerLeft_smul_hom (σ : Aut F') {X : C} (y : F'.obj (H.obj X)) :
    autWhiskerLeft H e σ • e.hom.app X y = e.hom.app X (σ • y) := by
  rw [autWhiskerLeft_smul]
  simp
  rfl

lemma autWhiskerLeft_smul_inv (σ : Aut F') {X : C} (x : F.obj X) :
    σ.hom.app (H.obj X) (e.inv.app X x) = e.inv.app X (autWhiskerLeft H e σ • x) := by
  rw [autWhiskerLeft_smul]
  simp

lemma autWhiskerLeft_id :
    autWhiskerLeft (𝟭 C) (Functor.leftUnitor F) = MonoidHom.id (Aut F) := by
  ext σ X x
  rfl

/-- `autWhiskerLeft` only depends on `H` up to isomorphism. -/
lemma autWhiskerLeft_congr {H' : C ⥤ D} (ρ : H ≅ H') (e' : H' ⋙ F' ≅ F) :
    autWhiskerLeft H (Functor.isoWhiskerRight ρ F' ≪≫ e') = autWhiskerLeft H' e' := by
  ext σ X x
  change e'.hom.app X (F'.map (ρ.hom.app X) (σ.hom.app (H.obj X)
      (F'.map (ρ.inv.app X) (e'.inv.app X x)))) =
    e'.hom.app X (σ.hom.app (H'.obj X) (e'.inv.app X x))
  rw [FunctorToFintypeCat.naturality]
  congr 1
  exact FintypeCat.inv_hom_id_apply (F'.mapIso (ρ.app X)) _

/-- Functoriality of `autWhiskerLeft` (V.6.3: `ᵗ(H' H) = ᵗH ᵗH'`). -/
lemma autWhiskerLeft_comp {F'' : E ⥤ FintypeCat.{w}} (K : D ⥤ E) (e' : K ⋙ F'' ≅ F') :
    autWhiskerLeft (H ⋙ K) (Functor.associator H K F'' ≪≫ Functor.isoWhiskerLeft H e' ≪≫ e) =
      (autWhiskerLeft H e).comp (autWhiskerLeft K e') := by
  ext σ X x
  rfl

end Hom

section Fibre

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

lemma subsingleton_fiber_terminal : Subsingleton (F.obj (⊤_ C)) := by
  have ht : IsTerminal (F.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj F _
  constructor
  intro a b
  have := ht.hom_ext (FintypeCat.homMk (X := FintypeCat.of PUnit.{w + 1}) fun _ ↦ a)
    (FintypeCat.homMk fun _ ↦ b)
  have h := congrArg (fun f ↦ f PUnit.unit) this
  simp only at h
  exact h

lemma nonempty_fiber_terminal : Nonempty (F.obj (⊤_ C)) := by
  have ht : IsTerminal (F.obj (⊤_ C)) := terminalIsTerminal.isTerminalObj F _
  exact ⟨ht.from (FintypeCat.of PUnit.{w + 1}) PUnit.unit⟩

/-- A point of the fibre is fixed by `Aut F` as soon as it comes from a section. -/
lemma smul_eq_of_mem_range_section {Y : C} (s : ⊤_ C ⟶ Y) {y : F.obj Y}
    (hy : y ∈ Set.range (F.map s)) (σ : Aut F) : σ • y = y := by
  have := subsingleton_fiber_terminal F
  obtain ⟨p, rfl⟩ := hy
  rw [mulAction_naturality, Subsingleton.elim (σ • p) p]

/-- V.6.4 (sections): a point of `F.obj Y` comes from a section `⊤_ C ⟶ Y` iff it is fixed by
`Aut F`. -/
lemma exists_section_iff_forall_smul_eq (Y : C) (y : F.obj Y) :
    (∃ s : ⊤_ C ⟶ Y, y ∈ Set.range (F.map s)) ↔ ∀ σ : Aut F, σ • y = y := by
  refine ⟨fun ⟨s, hs⟩ ↦ smul_eq_of_mem_range_section F s hs, fun h ↦ ?_⟩
  obtain ⟨p⟩ := nonempty_fiber_terminal F
  let f : (functorToAction F).obj (⊤_ C) ⟶ (functorToAction F).obj Y :=
    { hom := FintypeCat.homMk fun _ ↦ y
      comm := fun σ ↦ by
        ext q
        exact (h σ).symm }
  refine ⟨(functorToAction F).preimage f, p, ?_⟩
  rw [← functorToAction_map, Functor.map_preimage]
  rfl

/-- An object whose fibre is nonempty and on which `Aut F` acts transitively is connected
(the converse of `FiberFunctor.isPretransitive_of_isConnected`). -/
theorem isConnected_of_isPretransitive (Y : C) [Nonempty (F.obj Y)]
    [MulAction.IsPretransitive (Aut F) (F.obj Y)] : IsConnected Y := by
  refine ⟨fun hin ↦ not_initial_of_inhabited F (Classical.arbitrary _) hin, fun Z i _ hZ ↦ ?_⟩
  obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty F Z).mp hZ
  have hinj : Function.Injective (F.map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
  have hsurj : Function.Surjective (F.map i) := by
    intro y
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) (F.map i z) y
    exact ⟨σ • z, (mulAction_naturality F σ i z).symm⟩
  have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  exact isIso_of_reflects_iso i F

/-- V.6.4 (the connected pointed object attached to an open subgroup): for every open subgroup
`U` of `Aut F` there are a connected object `Y` and a point `y₀` of its fibre whose stabilizer
is `U`. (Mathlib proves this when `F` takes values in `FintypeCat.{u₁}`; we switch universes.) -/
theorem exists_isConnected_stabilizer_eq (U : OpenSubgroup (Aut F)) :
    ∃ (Y : C) (y₀ : F.obj Y), IsConnected Y ∧ MulAction.stabilizer (Aut F) y₀ = U := by
  classical
  let F₁ : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  have : FiberFunctor F₁ := FiberFunctor.comp_right _
  let ψ : Aut F ≃ₜ* Aut F₁ :=
    autEquivAutWhiskerRight F FintypeCat.uSwitchEquivalence.fullyFaithfulFunctor
  let U₁ : OpenSubgroup (Aut F₁) :=
    OpenSubgroup.comap (ψ.symm : Aut F₁ →* Aut F) ψ.symm.continuous U
  obtain ⟨Y, ⟨φ⟩⟩ := exists_lift_of_quotient_openSubgroup U₁
  let ι : (Aut F₁ ⧸ U₁.toSubgroup) → F₁.obj Y := fun q ↦ φ.inv.hom q
  have hι : Function.Bijective ι :=
    ConcreteCategory.bijective_of_isIso ((Action.forget _ _).map φ.inv)
  have hισ (τ : Aut F₁) (q : Aut F₁ ⧸ U₁.toSubgroup) : ι (τ • q) = τ • ι q :=
    ConcreteCategory.congr_hom (φ.inv.comm τ) q
  let y₁ : F₁.obj Y := ι (QuotientGroup.mk 1)
  let y₀ : F.obj Y := (F.obj Y).uSwitchEquiv y₁
  have hψ (σ : Aut F) (y : F₁.obj Y) :
      (F.obj Y).uSwitchEquiv (ψ σ • y) = σ • (F.obj Y).uSwitchEquiv y :=
    (FintypeCat.uSwitchEquiv_naturality (σ.hom.app Y) y).symm
  have : Nonempty (F₁.obj Y) := ⟨y₁⟩
  have : MulAction.IsPretransitive (Aut F₁) (F₁.obj Y) := by
    refine ⟨fun y y' ↦ ?_⟩
    obtain ⟨q, rfl⟩ := hι.surjective y
    obtain ⟨q', rfl⟩ := hι.surjective y'
    obtain ⟨τ, rfl⟩ := MulAction.exists_smul_eq (Aut F₁) q q'
    exact ⟨τ, (hισ τ q).symm⟩
  refine ⟨Y, y₀, isConnected_of_isPretransitive F₁ Y, ?_⟩
  ext σ
  rw [MulAction.mem_stabilizer_iff, ← hψ, (F.obj Y).uSwitchEquiv.injective.eq_iff, ← hισ,
    hι.injective.eq_iff, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
    mul_one]
  change (ψ σ)⁻¹ ∈ U₁ ↔ σ ∈ U
  rw [inv_mem_iff]
  change ψ.symm (ψ σ) ∈ U ↔ σ ∈ U
  rw [ψ.symm_apply_apply]

/-- V.6.4: a connected pointed object is determined up to isomorphism by the stabilizer of its
point: two connected objects having points with the same stabilizer are isomorphic. -/
theorem nonempty_iso_of_stabilizer_eq {A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
    (b : F.obj B) (h : MulAction.stabilizer (Aut F) a = MulAction.stabilizer (Aut F) b) :
    Nonempty (A ≅ B) := by
  choose σ hσ using fun x : F.obj A ↦ MulAction.exists_smul_eq (Aut F) a x
  let g : F.obj A → F.obj B := fun x ↦ σ x • b
  have hstab (τ τ' : Aut F) : τ • a = τ' • a ↔ τ • b = τ' • b := by
    rw [← inv_smul_eq_iff, ← mul_smul, ← MulAction.mem_stabilizer_iff, h,
      MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  have hg (τ : Aut F) (x : F.obj A) : g (τ • x) = τ • g x := by
    change σ (τ • x) • b = τ • σ x • b
    rw [← mul_smul, ← hstab, mul_smul, hσ, hσ]
  let φ : (functorToAction F).obj A ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk g
      comm := fun τ ↦ by
        ext x
        exact hg τ x }
  let f : A ⟶ B := (functorToAction F).preimage φ
  have hf (x : F.obj A) : F.map f x = g x := by
    rw [← functorToAction_map, Functor.map_preimage]
    rfl
  have hbij : Function.Bijective (F.map f) := by
    constructor
    · intro x y hxy
      rw [hf, hf] at hxy
      rw [← hσ x, ← hσ y]
      exact (hstab _ _).mpr hxy
    · intro y
      obtain ⟨τ, rfl⟩ := MulAction.exists_smul_eq (Aut F) b y
      refine ⟨τ • a, ?_⟩
      rw [hf, hg]
      congr 1
      have : σ a ∈ MulAction.stabilizer (Aut F) b := by
        rw [← h, MulAction.mem_stabilizer_iff]
        exact hσ a
      exact this
  have : IsIso (F.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso f := isIso_of_reflects_iso f F
  exact ⟨asIso f⟩

end Fibre

section CompletelyDecomposed

/-- V.6.4: an object of a Galois category is *completely decomposed* if it is isomorphic to a
finite sum of copies of the final object. -/
def IsCompletelyDecomposed [PreGaloisCategory C] (Y : C) : Prop :=
  ∃ n : ℕ, Nonempty (Y ≅ ∐ fun _ : Fin n ↦ ⊤_ C)

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.6.4: an object is completely decomposed iff `Aut F` acts trivially on its fibre. -/
theorem isCompletelyDecomposed_iff (Y : C) :
    IsCompletelyDecomposed Y ↔ ∀ (σ : Aut F) (y : F.obj Y), σ • y = y := by
  have := subsingleton_fiber_terminal F
  constructor
  · rintro ⟨n, ⟨φ⟩⟩ σ y
    have hc := isColimitOfPreserves F (coproductIsCoproduct fun _ : Fin n ↦ ⊤_ C)
    obtain ⟨⟨j⟩, a, ha⟩ := Limits.FintypeCat.jointly_surjective _ _ hc (F.map φ.hom y)
    refine smul_eq_of_mem_range_section F (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j ≫ φ.inv) ⟨a, ?_⟩ σ
    change F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j ≫ φ.inv) a = y
    rw [F.map_comp, FintypeCat.comp_apply]
    erw [ha]
    exact FintypeCat.hom_inv_id_apply (F.mapIso φ) y
  · intro h
    have : Finite (F.obj Y) := inferInstance
    let n := Nat.card (F.obj Y)
    let eqv : F.obj Y ≃ Fin n := Finite.equivFin _
    have hs (j : Fin n) : ∃ s : ⊤_ C ⟶ Y, eqv.symm j ∈ Set.range (F.map s) :=
      (exists_section_iff_forall_smul_eq F Y _).mpr fun σ ↦ h σ _
    choose s hs using hs
    have hs' (j : Fin n) (a : F.obj (⊤_ C)) : F.map (s j) a = eqv.symm j := by
      obtain ⟨b, hb⟩ := hs j
      rw [Subsingleton.elim a b, hb]
    let d : (∐ fun _ : Fin n ↦ ⊤_ C) ⟶ Y := Sigma.desc s
    have hc := isColimitOfPreserves F (coproductIsCoproduct fun _ : Fin n ↦ ⊤_ C)
    have hd (j : Fin n) (a : F.obj (⊤_ C)) :
        F.map d (F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j) a) = eqv.symm j := by
      rw [← FintypeCat.comp_apply, ← F.map_comp, Sigma.ι_desc, hs']
    have hbij : Function.Bijective (F.map d) := by
      constructor
      · intro z₁ z₂ hz
        obtain ⟨⟨j₁⟩, a₁, rfl⟩ := Limits.FintypeCat.jointly_surjective _ _ hc z₁
        obtain ⟨⟨j₂⟩, a₂, rfl⟩ := Limits.FintypeCat.jointly_surjective _ _ hc z₂
        have h₁ := hd j₁ a₁
        have h₂ := hd j₂ a₂
        have hz' : F.map d (F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j₁) a₁) =
            F.map d (F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j₂) a₂) := hz
        have hj : j₁ = j₂ := eqv.symm.injective (h₁.symm.trans (hz'.trans h₂))
        subst hj
        rw [Subsingleton.elim (α := F.obj (⊤_ C)) a₁ a₂]
      · intro y
        obtain ⟨a⟩ := nonempty_fiber_terminal F
        refine ⟨F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) (eqv y)) a, ?_⟩
        rw [hd, Equiv.symm_apply_apply]
    have : IsIso (F.map d) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso d := isIso_of_reflects_iso d F
    exact ⟨n, ⟨(asIso d).symm⟩⟩

end CompletelyDecomposed

section Galois

variable [GaloisCategory C] [GaloisCategory D] [GaloisCategory E]
  {F : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}} {F'' : E ⥤ FintypeCat.{w}}
  [FiberFunctor F] [FiberFunctor F'] [FiberFunctor F'']
  (H : C ⥤ D) (e : H ⋙ F' ≅ F)

omit [GaloisCategory D] [FiberFunctor F'] in
/-- V.6.3: the homomorphism induced by a functor of Galois categories is continuous. -/
theorem continuous_autWhiskerLeft : Continuous (autWhiskerLeft H e) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  let y : F'.obj (H.obj X.obj) := e.inv.app X.obj X.pt
  refine ⟨MulAction.stabilizer (Aut F') y, fun σ (hσ : σ • y = y) ↦ hX ?_,
    stabilizer_isOpen _ _, one_mem _⟩
  change autWhiskerLeft H e σ • X.pt = X.pt
  rw [autWhiskerLeft_smul]
  change e.hom.app X.obj (σ • y) = X.pt
  rw [hσ]
  exact FintypeCat.inv_hom_id_apply (e.app X.obj) X.pt

/-- V.6.9, (ii) ⇒ (i): if `H` sends connected objects to connected objects, the induced
homomorphism of fundamental groups is surjective. -/
theorem autWhiskerLeft_surjective_of_isConnected
    (h : ∀ X : C, IsConnected X → IsConnected (H.obj X)) :
    Function.Surjective (autWhiskerLeft H e) := by
  let _ (X : C) : MulAction (Aut F') (F.obj X) := MulAction.compHom _ (autWhiskerLeft H e)
  have : IsNaturalSMul F (Aut F') :=
    ⟨fun σ _ _ f x ↦ (mulAction_naturality F (autWhiskerLeft H e σ) f x).symm⟩
  have (X : C) : ContinuousSMul (Aut F') (F.obj X) :=
    ⟨(continuous_smul (M := Aut F) (X := F.obj X)).comp
      (((continuous_autWhiskerLeft H e).comp continuous_fst).prodMk continuous_snd)⟩
  have key : toAut F (Aut F') = autWhiskerLeft H e := by
    ext σ X x
    rfl
  rw [← key]
  refine toAut_surjective_of_isPretransitive F (Aut F') fun X _ ↦ ⟨fun x y ↦ ?_⟩
  have := h X inferInstance
  let x' : F'.obj (H.obj X) := e.inv.app X x
  let y' : F'.obj (H.obj X) := e.inv.app X y
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F') x' y'
  refine ⟨σ, ?_⟩
  change autWhiskerLeft H e σ • x = y
  rw [autWhiskerLeft_smul]
  change e.hom.app X (σ • x') = y
  rw [hσ]
  exact FintypeCat.inv_hom_id_apply (e.app X) y

/-- V.6.9, (i) ⇒ (ii): if the induced homomorphism is surjective, `H` sends connected objects to
connected objects. -/
theorem isConnected_obj_of_autWhiskerLeft_surjective
    (h : Function.Surjective (autWhiskerLeft H e)) (X : C) [IsConnected X] :
    IsConnected (H.obj X) := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  have : Nonempty (F'.obj (H.obj X)) := ⟨e.inv.app X x⟩
  have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) := by
    refine ⟨fun y₁ y₂ ↦ ?_⟩
    obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut F) (e.hom.app X y₁) (e.hom.app X y₂)
    obtain ⟨σ, rfl⟩ := h τ
    refine ⟨σ, ?_⟩
    rw [autWhiskerLeft_smul_hom] at hτ
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app X)).injective hτ
  exact isConnected_of_isPretransitive F' _

/-- V.6.9, (i) ⇔ (ii): the homomorphism induced by `H` is surjective iff `H` sends connected
objects to connected objects. -/
theorem autWhiskerLeft_surjective_iff :
    Function.Surjective (autWhiskerLeft H e) ↔ ∀ X : C, IsConnected X → IsConnected (H.obj X) :=
  ⟨fun h X _ ↦ isConnected_obj_of_autWhiskerLeft_surjective H e h X,
    autWhiskerLeft_surjective_of_isConnected H e⟩

/-- V.6.10, sufficiency: an equivalence of Galois categories compatible with the fibre functors
induces an isomorphism of fundamental groups. -/
theorem autWhiskerLeft_bijective_of_isEquivalence [H.IsEquivalence] :
    Function.Bijective (autWhiskerLeft H e) := by
  refine ⟨fun σ τ hστ ↦ ?_, autWhiskerLeft_surjective_of_isConnected H e fun X hX ↦ ?_⟩
  · have hfix (Y : D) (y : F'.obj Y) : σ • y = τ • y := by
      let φ : H.obj (H.inv.obj Y) ≅ Y := H.asEquivalence.counitIso.app Y
      obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F'.map φ.hom)).surjective y
      rw [mulAction_naturality, mulAction_naturality]
      congr 1
      apply (ConcreteCategory.bijective_of_isIso (e.hom.app (H.inv.obj Y))).injective
      rw [← autWhiskerLeft_smul_hom, ← autWhiskerLeft_smul_hom, hστ]
    exact Aut.ext (NatTrans.ext (funext fun Y ↦ FintypeCat.hom_ext _ _ (hfix Y)))
  · refine ⟨fun hin ↦ ?_, fun Z i _ hZ ↦ ?_⟩
    · obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
      exact not_initial_of_inhabited F' (e.inv.app X x) hin
    · let G := H.inv
      let φ : G.obj (H.obj X) ≅ X := H.asEquivalence.unitIso.symm.app X
      have : Mono (G.map i ≫ φ.hom) := inferInstance
      have hGZ : IsInitial (G.obj Z) → False := by
        obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty F' Z).mp hZ
        let ψ : H.obj (G.obj Z) ≅ Z := H.asEquivalence.counitIso.app Z
        exact not_initial_of_inhabited F (e.hom.app _ (F'.map ψ.inv z))
      have := hX.noTrivialComponent (G.obj Z) (G.map i ≫ φ.hom) hGZ
      have : IsIso (G.map i) := IsIso.of_isIso_comp_right (G.map i) φ.hom
      exact isIso_of_reflects_iso i G

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.6.4 and V.6.5: the homomorphism induced by `H` is trivial iff `H` sends every object to a
completely decomposed object. -/
theorem autWhiskerLeft_eq_one_iff :
    autWhiskerLeft H e = 1 ↔ ∀ X : C, IsCompletelyDecomposed (H.obj X) := by
  simp_rw [isCompletelyDecomposed_iff F']
  constructor
  · intro h X σ y
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app X)).injective
    rw [← autWhiskerLeft_smul_hom, h]
    rfl
  · intro h
    ext σ X x
    change autWhiskerLeft H e σ • x = x
    rw [autWhiskerLeft_smul]
    let x' : F'.obj (H.obj X) := e.inv.app X x
    change e.hom.app X (σ • x') = x
    rw [h]
    exact FintypeCat.inv_hom_id_apply (e.app X) x


include e in
/-- A functor of Galois categories compatible with the fibre functors sends completely decomposed
objects to completely decomposed objects. With `autWhiskerLeft_eq_one_iff`, this shows that
`K ⋙ H` has trivial induced homomorphism when it factors through a Galois category all of whose
objects are completely decomposed (in X.1.4: through the étale coverings of a geometric point). -/
theorem isCompletelyDecomposed_obj {X : C} (hX : IsCompletelyDecomposed X) :
    IsCompletelyDecomposed (H.obj X) := by
  rw [isCompletelyDecomposed_iff F']
  rw [isCompletelyDecomposed_iff F] at hX
  intro σ y
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app X)).injective
  rw [← autWhiskerLeft_smul_hom, hX]

variable {H e} (K : D ⥤ E) (e' : K ⋙ F'' ≅ F')

omit [GaloisCategory C] [FiberFunctor F] [GaloisCategory D] [FiberFunctor F'] in
/-- V.6.11, first assertion: for functors `C ⥤ D ⥤ E` of Galois categories, the composite
`Aut F'' → Aut F' → Aut F` is trivial iff `K (H X)` is completely decomposed for every `X`. -/
theorem autWhiskerLeft_comp_autWhiskerLeft_eq_one_iff :
    (autWhiskerLeft H e).comp (autWhiskerLeft K e') = 1 ↔
      ∀ X : C, IsCompletelyDecomposed (K.obj (H.obj X)) := by
  rw [← autWhiskerLeft_comp]
  exact autWhiskerLeft_eq_one_iff (H ⋙ K) _

omit [GaloisCategory C] [FiberFunctor F] [GaloisCategory D] [FiberFunctor F'] in
/-- Elements of the kernel of `autWhiskerLeft H e` act trivially on the fibres of the objects
`H X`. -/
lemma smul_eq_of_mem_ker {t : Aut F'} (ht : t ∈ (autWhiskerLeft H e).ker) {X : C}
    (y : F'.obj (H.obj X)) : t • y = y := by
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app X)).injective
  rw [← autWhiskerLeft_smul_hom, (MonoidHom.mem_ker).mp ht]
  rfl

omit [GaloisCategory C] [FiberFunctor F] in
/-- The key step of V.6.11: if every connected `Y : D` such that `K Y` has a section receives a
morphism from a connected component of some `H X`, then every element of the kernel of `Aut F' →
Aut F` moves each point of a Galois object inside its orbit under the image of `Aut F''`. -/
lemma exists_mem_range_smul_eq
    (h : ∀ Y : D, IsConnected Y → Nonempty (⊤_ E ⟶ K.obj Y) →
      ∃ (X : C) (Z : D) (i : Z ⟶ H.obj X) (_ : Mono i) (_ : Z ⟶ Y), Nonempty (F'.obj Z))
    {t : Aut F'} (ht : t ∈ (autWhiskerLeft H e).ker) (A : D) [IsGalois A] (a : F'.obj A) :
    ∃ r ∈ (autWhiskerLeft K e').range, r • a = t • a := by
  set R := (autWhiskerLeft K e').range
  let V := MulAction.stabilizer (Aut F') a
  have hVn : V.Normal := stabilizer_normal_of_isGalois F' A a
  let U : OpenSubgroup (Aut F') :=
    ⟨R ⊔ V, Subgroup.isOpen_mono le_sup_right (stabilizer_isOpen (Aut F') a)⟩
  obtain ⟨Y, y₀, hY, hU⟩ := exists_isConnected_stabilizer_eq F' U
  -- `R` fixes `y₀`, so `K Y` has a section
  have hRfix (r : Aut F') (hr : r ∈ R) : r • y₀ = y₀ := by
    rw [← MulAction.mem_stabilizer_iff, hU]
    exact Subgroup.mem_sup_left hr
  have hsec : Nonempty (⊤_ E ⟶ K.obj Y) := by
    obtain ⟨s, -⟩ := (exists_section_iff_forall_smul_eq F'' (K.obj Y) (e'.inv.app Y y₀)).mpr
      fun σ ↦ by
        change σ.hom.app (K.obj Y) (e'.inv.app Y y₀) = _
        rw [autWhiskerLeft_smul_inv, hRfix _ ⟨σ, rfl⟩]
    exact ⟨s⟩
  obtain ⟨X, Z, i, _, g, ⟨z⟩⟩ := h Y hY hsec
  -- every element of the kernel fixes `F'.map g z`
  have hker (n : Aut F') (hn : n ∈ (autWhiskerLeft H e).ker) :
      n • F'.map g z = F'.map g z := by
    have hinj : Function.Injective (F'.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F'.map i)
    have : n • z = z := hinj (by rw [← mulAction_naturality, smul_eq_of_mem_ker hn])
    rw [mulAction_naturality, this]
  -- hence, the kernel being normal, `t` fixes `y₀`
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut F') (F'.map g z) y₀
  have htfix : t • y₀ = y₀ := by
    have hconj : τ⁻¹ * t * τ ∈ (autWhiskerLeft H e).ker := by
      simpa using (autWhiskerLeft H e).normal_ker.conj_mem t ht τ⁻¹
    rw [← hτ, ← mul_smul, (by simp [mul_assoc] : t * τ = τ * (τ⁻¹ * t * τ)), mul_smul,
      hker _ hconj]
  have htU : t ∈ (U : Subgroup (Aut F')) := by
    rw [← hU]
    exact htfix
  obtain ⟨r, hr, v, hv, rfl⟩ : t ∈ (R : Set (Aut F')) * (V : Set (Aut F')) := by
    rw [← Subgroup.mul_normal R V]
    exact htU
  exact ⟨r, hr, by rw [mul_smul, show v • a = a from hv]⟩

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.6.11, second assertion (sufficiency): if every connected `Y : D` such that `K Y` admits a
section receives a morphism from a connected component of some `H X` (here: a subobject `Z` of
`H X` with nonempty fibre), then `Ker (Aut F' → Aut F) ⊆ Im (Aut F'' → Aut F')`. -/
theorem ker_autWhiskerLeft_le_range_autWhiskerLeft
    (h : ∀ Y : D, IsConnected Y → Nonempty (⊤_ E ⟶ K.obj Y) →
      ∃ (X : C) (Z : D) (i : Z ⟶ H.obj X) (_ : Mono i) (_ : Z ⟶ Y), Nonempty (F'.obj Z)) :
    (autWhiskerLeft H e).ker ≤ (autWhiskerLeft K e').range := by
  intro t ht
  have hRc : IsClosed ((autWhiskerLeft K e').range : Set (Aut F')) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_autWhiskerLeft K e')).isClosed
  rw [← SetLike.mem_coe, ← hRc.closure_eq, mem_closure_iff_nhds]
  intro N hN
  have : (t * ·) ⁻¹' N ∈ nhds (1 : Aut F') := by
    apply (continuous_const_mul t).continuousAt.preimage_mem_nhds
    simpa using hN
  obtain ⟨⟨A, a, _⟩, -, hsub⟩ := (nhds_one_has_basis_stabilizers F').mem_iff.mp this
  obtain ⟨r, hr, hra⟩ := exists_mem_range_smul_eq K e' h ht A a
  refine ⟨r, ?_, hr⟩
  have : t⁻¹ * r ∈ MulAction.stabilizer (Aut F') a := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hra, inv_smul_smul]
  simpa using hsub this

/-- X.1.4 (formal part), from V.6.9 and V.6.11. Let `C ⥤ D ⥤ E` be functors of Galois categories
(in X.1.4: étale coverings of `Y`, of `X` and of the geometric fibre `X̄_y`, with the
inverse-image functors) compatible with the fibre functors. Assume
* `H` sends connected objects to connected objects (IX.3.4 in SGA),
* `K (H X)` is completely decomposed for every `X` (the composite factors through a geometric
  point), and
* a connected `Y : D` such that `K Y` has a section is isomorphic to some `H X` (X.1.3).

Then `Aut F'' → Aut F' → Aut F → 1` is exact. -/
theorem surjective_and_range_eq_ker
    (hconn : ∀ X : C, IsConnected X → IsConnected (H.obj X))
    (htriv : ∀ X : C, IsCompletelyDecomposed (K.obj (H.obj X)))
    (hdesc : ∀ Y : D, IsConnected Y → Nonempty (⊤_ E ⟶ K.obj Y) →
      ∃ X : C, Nonempty (Y ≅ H.obj X)) :
    Function.Surjective (autWhiskerLeft H e) ∧
      (autWhiskerLeft K e').range = (autWhiskerLeft H e).ker := by
  refine ⟨autWhiskerLeft_surjective_of_isConnected H e hconn, le_antisymm ?_ ?_⟩
  · rintro _ ⟨σ, rfl⟩
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (autWhiskerLeft_comp_autWhiskerLeft_eq_one_iff K e').mpr htriv, MonoidHom.one_apply]
  · refine ker_autWhiskerLeft_le_range_autWhiskerLeft K e' fun Y hY hs ↦ ?_
    obtain ⟨X, ⟨ψ⟩⟩ := hdesc Y hY hs
    obtain ⟨y⟩ := nonempty_fiber_of_isConnected F' Y
    exact ⟨X, H.obj X, 𝟙 _, inferInstance, ψ.inv, ⟨F'.map ψ.hom y⟩⟩

/-- V.6.11, second assertion (necessity, via V.6.6 when `Aut F' → Aut F` is surjective): if
`Aut F' → Aut F` is surjective with kernel contained in the image of `Aut F'' → Aut F'`, every
connected `Y : D` such that `K Y` admits a section is isomorphic to some `H X`. -/
theorem exists_iso_obj_of_ker_le_range
    (hsurj : Function.Surjective (autWhiskerLeft H e))
    (hker : (autWhiskerLeft H e).ker ≤ (autWhiskerLeft K e').range)
    (Y : D) [IsConnected Y] (hs : Nonempty (⊤_ E ⟶ K.obj Y)) :
    ∃ X : C, Nonempty (Y ≅ H.obj X) := by
  obtain ⟨s⟩ := hs
  obtain ⟨p⟩ := nonempty_fiber_terminal F''
  let z : F''.obj (K.obj Y) := F''.map s p
  let y₀ : F'.obj Y := e'.hom.app Y z
  have hz (σ : Aut F'') : σ • z = z := smul_eq_of_mem_range_section F'' s ⟨p, rfl⟩ σ
  let V := MulAction.stabilizer (Aut F') y₀
  have hNV : (autWhiskerLeft H e).ker ≤ V := by
    refine hker.trans ?_
    rintro _ ⟨σ, rfl⟩
    rw [MulAction.mem_stabilizer_iff, autWhiskerLeft_smul_hom, hz]
  have hq : Topology.IsQuotientMap (autWhiskerLeft H e) :=
    (continuous_autWhiskerLeft H e).isClosedMap.isQuotientMap (continuous_autWhiskerLeft H e)
      hsurj
  have hcomap : (V.map (autWhiskerLeft H e)).comap (autWhiskerLeft H e) = V := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hNV]
  have hUopen : IsOpen ((V.map (autWhiskerLeft H e) : Subgroup (Aut F)) : Set (Aut F)) := by
    rw [← hq.isCoinducing.isOpen_preimage, ← Subgroup.coe_comap, hcomap]
    exact stabilizer_isOpen _ _
  obtain ⟨X, x₀, hX, hx₀⟩ :=
    exists_isConnected_stabilizer_eq F ⟨V.map (autWhiskerLeft H e), hUopen⟩
  have : IsConnected (H.obj X) := isConnected_obj_of_autWhiskerLeft_surjective H e hsurj X
  let x₀' : F'.obj (H.obj X) := e.inv.app X x₀
  have hx₀' : e.hom.app X x₀' = x₀ := FintypeCat.inv_hom_id_apply (e.app X) x₀
  have hstab : MulAction.stabilizer (Aut F') x₀' = V := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, ← hcomap, Subgroup.mem_comap]
    change _ ↔
      autWhiskerLeft H e σ ∈ (⟨V.map (autWhiskerLeft H e), hUopen⟩ : OpenSubgroup (Aut F))
    rw [← SetLike.mem_coe, ← OpenSubgroup.coe_toSubgroup, ← hx₀, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff, ← hx₀', autWhiskerLeft_smul_hom]
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app X)).injective.eq_iff.symm
  exact ⟨X, nonempty_iso_of_stabilizer_eq F' y₀ x₀' hstab.symm⟩

/-- V.6.11, second assertion, for `Aut F' → Aut F` surjective (with V.6.7): the kernel of
`Aut F' → Aut F` is contained in the image of `Aut F'' → Aut F'` iff every connected `Y : D`
such that `K Y` has a section is isomorphic to an object `H X`. -/
theorem ker_autWhiskerLeft_le_range_autWhiskerLeft_iff
    (hsurj : Function.Surjective (autWhiskerLeft H e)) :
    (autWhiskerLeft H e).ker ≤ (autWhiskerLeft K e').range ↔
      ∀ Y : D, IsConnected Y → Nonempty (⊤_ E ⟶ K.obj Y) → ∃ X : C, Nonempty (Y ≅ H.obj X) := by
  refine ⟨fun h Y _ hs ↦ exists_iso_obj_of_ker_le_range K e' hsurj h Y hs, fun h ↦ ?_⟩
  refine ker_autWhiskerLeft_le_range_autWhiskerLeft K e' fun Y hY hs ↦ ?_
  obtain ⟨X, ⟨ψ⟩⟩ := h Y hY hs
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected F' Y
  exact ⟨X, H.obj X, 𝟙 _, inferInstance, ψ.inv, ⟨F'.map ψ.hom y⟩⟩

/-- X.1.3 ⇔ X.1.4 (the "equivalent form" of X.1.4, via V.6.9 and V.6.11): if `H` preserves
connected objects and every `K (H X)` is completely decomposed, the sequence
`Aut F'' → Aut F' → Aut F → 1` is exact iff every connected `Y : D` such that `K Y` has a
section is isomorphic to an object `H X`. -/
theorem range_eq_ker_iff (hconn : ∀ X : C, IsConnected X → IsConnected (H.obj X))
    (htriv : ∀ X : C, IsCompletelyDecomposed (K.obj (H.obj X))) :
    (autWhiskerLeft K e').range = (autWhiskerLeft H e).ker ↔
      ∀ Y : D, IsConnected Y → Nonempty (⊤_ E ⟶ K.obj Y) → ∃ X : C, Nonempty (Y ≅ H.obj X) := by
  have hsurj := autWhiskerLeft_surjective_of_isConnected H e hconn
  rw [← ker_autWhiskerLeft_le_range_autWhiskerLeft_iff K e' hsurj]
  refine ⟨fun h ↦ h.ge, fun h ↦ le_antisymm ?_ h⟩
  rintro _ ⟨σ, rfl⟩
  rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
    (autWhiskerLeft_comp_autWhiskerLeft_eq_one_iff K e').mpr htriv, MonoidHom.one_apply]

end Galois

end SGA.SGA1.ExposeX
