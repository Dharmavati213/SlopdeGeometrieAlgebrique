/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Order.Zorn

/-!
# Essential extensions and actual injective envelopes of modules

Essentiality is the usual nonzero-intersection condition, expressed by
nonzero scalar multiples. The injective-envelope construction below uses
enough injectives and Zorn's lemma, not an assumed envelope.
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- `S` is essential in `H`: every nonzero cyclic submodule of `H` meets `S`. -/
def EssentialIn {M : Type u} [AddCommGroup M] [Module R M]
    (S H : Submodule R M) : Prop :=
  S ≤ H ∧ ∀ x ∈ H, x ≠ 0 → ∃ r : R, r • x ∈ S ∧ r • x ≠ 0

theorem EssentialIn.refl {M : Type u} [AddCommGroup M] [Module R M]
    (S : Submodule R M) : EssentialIn S S :=
  ⟨le_rfl, fun x hx hx0 => ⟨1, by simpa using hx, by simpa using hx0⟩⟩

theorem EssentialIn.trans {M : Type u} [AddCommGroup M] [Module R M]
    {S H K : Submodule R M} (hSH : EssentialIn S H) (hHK : EssentialIn H K) :
    EssentialIn S K := by
  refine ⟨hSH.1.trans hHK.1, ?_⟩
  intro x hx hx0
  obtain ⟨r, hr, hr0⟩ := hHK.2 x hx hx0
  obtain ⟨s, hs, hs0⟩ := hSH.2 (r • x) hr hr0
  exact ⟨s * r, by simpa [mul_smul] using hs, by simpa [mul_smul] using hs0⟩

theorem EssentialIn.mono_left {M : Type u} [AddCommGroup M] [Module R M]
    {S T H : Submodule R M} (h : EssentialIn S H) (hST : S ≤ T) (hTH : T ≤ H) :
    EssentialIn T H :=
  ⟨hTH, fun x hx hx0 => by
    obtain ⟨r, hr, hr0⟩ := h.2 x hx hx0
    exact ⟨r, hST hr, hr0⟩⟩

/-- Equivalent to the customary formulation using intersections with submodules. -/
theorem essentialIn_iff_disjoint {M : Type u} [AddCommGroup M] [Module R M]
    (S H : Submodule R M) :
    EssentialIn S H ↔ S ≤ H ∧
      ∀ P : Submodule R M, P ≤ H → Disjoint S P → P = ⊥ := by
  constructor
  · rintro ⟨hle, h⟩
    refine ⟨hle, fun P hP hd => ?_⟩
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    obtain ⟨r, hr, hr0⟩ := h x (hP hx) hx0
    exact hr0 (Submodule.disjoint_def.mp hd _ hr (P.smul_mem r hx))
  · rintro ⟨hle, h⟩
    refine ⟨hle, fun x hx hx0 => ?_⟩
    by_contra hn
    have hd : Disjoint S (Submodule.span R {x}) := by
      rw [Submodule.disjoint_def]
      intro y hy hyP
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hyP
      by_contra hy0
      exact hn ⟨r, hy, hy0⟩
    have hP : Submodule.span R {x} ≤ H := Submodule.span_le.mpr (by simpa using hx)
    have := h _ hP hd
    exact hx0 (by simpa [this] using Submodule.mem_span_singleton_self (R := R) x)

/-- A genuine essential module embedding. -/
def EssentialModuleMap {M N : ModuleCat.{u} R} (f : M ⟶ N) : Prop :=
  Function.Injective f.hom ∧ EssentialIn (LinearMap.range f.hom) ⊤

theorem EssentialModuleMap.mono {M N : ModuleCat.{u} R} {f : M ⟶ N}
    (hf : EssentialModuleMap f) : Mono f :=
  (ModuleCat.mono_iff_injective f).mpr hf.1

/-- A map injective on an essential submodule is injective everywhere. -/
theorem EssentialIn.injective_of_comp {M N : ModuleCat.{u} R}
    {S : Submodule R M} (hS : EssentialIn S ⊤) (f : M ⟶ N)
    (hf : Function.Injective (f.hom.comp S.subtype)) : Function.Injective f.hom := by
  apply (injective_iff_map_eq_zero f.hom).mpr
  intro x hx
  by_contra hx0
  obtain ⟨r, hr, hr0⟩ := hS.2 x (by trivial) hx0
  have heq : f.hom.comp S.subtype ⟨r • x, hr⟩ = f.hom.comp S.subtype 0 := by
    simp [hx]
  exact hr0 (congrArg Subtype.val (hf heq))

theorem EssentialModuleMap.injective_of_comp {L M N : ModuleCat.{u} R}
    {i : L ⟶ M} (hi : EssentialModuleMap i) (f : M ⟶ N)
    (hf : Function.Injective (i ≫ f).hom) : Function.Injective f.hom := by
  apply hi.2.injective_of_comp f
  intro x y hxy
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  apply Subtype.ext
  rw [← ha, ← hb]
  apply congrArg i.hom
  apply hf
  simpa [ModuleCat.hom_comp, ha, hb] using hxy

/-- Maximal essential extensions inside a fixed ambient module exist. -/
theorem exists_maximal_essentialIn {M : Type u} [AddCommGroup M] [Module R M]
    (S : Submodule R M) : ∃ H, Maximal (EssentialIn S) H := by
  apply zorn_le₀ {H | EssentialIn S H}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨S, EssentialIn.refl S, by simp⟩
  · refine ⟨sSup c, ⟨?_, ?_⟩, fun P hP => le_sSup hP⟩
    · obtain ⟨P, hP⟩ := hne
      exact (hc hP).1.trans (le_sSup hP)
    · intro x hx hx0
      obtain ⟨P, hP, hxP⟩ := (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hx
      exact (hc hP).2 x hxP hx0

/-- A maximal submodule disjoint from any prescribed submodule exists. -/
theorem exists_maximal_disjoint {M : Type u} [AddCommGroup M] [Module R M]
    (H : Submodule R M) : ∃ N, Maximal (fun N => Disjoint H N) N := by
  apply zorn_le₀ {N | Disjoint H N}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊥, disjoint_bot_right, by simp⟩
  · refine ⟨sSup c, ?_, fun P hP => le_sSup hP⟩
    change Disjoint H (sSup c)
    rw [Submodule.disjoint_def]
    intro x hxH hx
    obtain ⟨P, hP, hxP⟩ := (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hx
    exact Submodule.disjoint_def.mp (hc hP) x hxH hxP

/-- Quotienting by a maximal disjoint submodule makes the given image essential. -/
theorem essentialIn_map_mkQ_of_maximal_disjoint
    {M : Type u} [AddCommGroup M] [Module R M]
    (H N : Submodule R M) (hN : Maximal (fun N => Disjoint H N) N) :
    EssentialIn (H.map N.mkQ) ⊤ := by
  refine ⟨le_top, ?_⟩
  intro x _ hx0
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  have hy : y ∉ N := fun hy => hx0 ((Submodule.Quotient.mk_eq_zero N).mpr hy)
  have hn : ¬ Disjoint H (N ⊔ Submodule.span R {y}) := by
    intro hd
    have heq := hN.eq_of_le hd le_sup_left
    apply hy
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  rw [Submodule.disjoint_def] at hn
  push Not at hn
  obtain ⟨z, hzH, hz, hz0⟩ := hn
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have ha0 : N.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ha
  have heq : r • N.mkQ y = N.mkQ z := by
    rw [← hab, map_add, ha0, zero_add, map_smul]
  refine ⟨r, heq ▸ ?_, heq ▸ ?_⟩
  · exact Submodule.mem_map.mpr ⟨z, hzH, rfl⟩
  · intro hzq
    exact hz0 (Submodule.disjoint_def.mp hN.prop z hzH
      ((Submodule.Quotient.mk_eq_zero N).mp hzq))

/-- Retracts of injective modules are injective. -/
theorem module_injective_of_retraction {H E : ModuleCat.{u} R} [Injective E]
    (i : H ⟶ E) (p : E ⟶ H) (hip : i ≫ p = 𝟙 H) : Injective H where
  factors g f _ := by
    obtain ⟨a, ha⟩ := Injective.factors (g ≫ i) f
    refine ⟨a ≫ p, ?_⟩
    rw [← Category.assoc, ha, Category.assoc, hip, Category.comp_id]

/-- An injective essential submodule is the whole module. -/
theorem EssentialIn.eq_top_of_injective {M : ModuleCat.{u} R} (S : Submodule R M)
    [Injective (ModuleCat.of R S)] (hS : EssentialIn S ⊤) : S = ⊤ := by
  let i : ModuleCat.of R S ⟶ M := ModuleCat.ofHom S.subtype
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr Subtype.val_injective
  obtain ⟨p, hp⟩ := Injective.factors (𝟙 (ModuleCat.of R S)) i
  have hpInj : Function.Injective p.hom := hS.injective_of_comp p (by
    change Function.Injective (i ≫ p).hom
    rw [hp]
    exact Function.injective_id)
  apply top_unique
  intro x _
  have heq : (p.hom x).val = x := by
    apply hpInj
    exact congrArg (fun f : ModuleCat.of R S ⟶ ModuleCat.of R S => f.hom (p.hom x)) hp
  exact heq ▸ (p.hom x).property

/-- A maximal essential extension inside an injective module is injective. -/
theorem injective_of_maximal_essentialIn {E : ModuleCat.{u} R} [Injective E]
    (S H : Submodule R E) (hH : Maximal (EssentialIn S) H) :
    Injective (ModuleCat.of R H) := by
  obtain ⟨N, hN⟩ := exists_maximal_disjoint H
  let j : ModuleCat.of R H ⟶ ModuleCat.of R (E ⧸ N) :=
    ModuleCat.ofHom (N.mkQ.comp H.subtype)
  have hj : Function.Injective j.hom := by
    apply (injective_iff_map_eq_zero j.hom).mpr
    intro x hx
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hN.prop x x.property
      ((Submodule.Quotient.mk_eq_zero N).mp hx)
  have : Mono j := (ModuleCat.mono_iff_injective j).mpr hj
  let i : ModuleCat.of R H ⟶ E := ModuleCat.ofHom H.subtype
  obtain ⟨φ, hφ⟩ := Injective.factors i j
  have hφx (x : H) : φ.hom (N.mkQ x.val) = x.val := by
    exact congrArg (fun f : ModuleCat.of R H ⟶ E => f.hom x) hφ
  have hess : EssentialModuleMap j := by
    refine ⟨hj, ?_⟩
    convert essentialIn_map_mkQ_of_maximal_disjoint H N hN using 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hφinj : Function.Injective φ.hom := hess.injective_of_comp φ (by
    rw [hφ]
    exact Subtype.val_injective)
  have hrange : EssentialIn H (LinearMap.range φ.hom) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact ⟨N.mkQ x, hφx ⟨x, hx⟩⟩
    · intro x hx hx0
      obtain ⟨y, rfl⟩ := hx
      have hy0 : y ≠ 0 := fun h => hx0 (by simp [h])
      obtain ⟨r, hr, hr0⟩ := hess.2.2 y (by trivial) hy0
      obtain ⟨z, hz⟩ := hr
      have heq : r • φ.hom y = z.val := by
        rw [← map_smul, ← hz]
        exact hφx z
      refine ⟨r, heq ▸ z.property, ?_⟩
      intro hrφ
      apply hr0
      apply hφinj
      simpa using hrφ
  have heq : LinearMap.range φ.hom = H :=
    (hH.eq_of_le (hH.prop.trans hrange) hrange.1).symm
  let p : E ⟶ ModuleCat.of R H := ModuleCat.ofHom
    ((φ.hom.comp N.mkQ).codRestrict H (fun x => heq ▸ ⟨N.mkQ x, rfl⟩))
  apply module_injective_of_retraction i p
  ext x
  exact hφx x

/-- An injective envelope consists of an actual injective essential embedding. -/
structure ModuleInjectiveEnvelope (M : ModuleCat.{u} R) where
  obj : ModuleCat.{u} R
  ι : M ⟶ obj
  injective : Injective obj
  essential : EssentialModuleMap ι

attribute [instance] ModuleInjectiveEnvelope.injective

/-- Every module has a genuine injective envelope, constructed using two Zorn arguments. -/
theorem nonempty_moduleInjectiveEnvelope (M : ModuleCat.{u} R) :
    Nonempty (ModuleInjectiveEnvelope M) := by
  let E := Injective.under M
  let f : M ⟶ E := Injective.ι M
  let S := LinearMap.range f.hom
  obtain ⟨H, hH⟩ := exists_maximal_essentialIn S
  let g : M ⟶ ModuleCat.of R H := ModuleCat.ofHom
    (f.hom.codRestrict H (fun x => hH.prop.1 ⟨x, rfl⟩))
  refine ⟨⟨ModuleCat.of R H, g, injective_of_maximal_essentialIn S H hH, ?_⟩⟩
  refine ⟨?_, le_top, ?_⟩
  · intro x y hxy
    apply (ModuleCat.mono_iff_injective f).mp inferInstance
    exact congrArg Subtype.val hxy
  · intro x _ hx0
    have hx0' : x.val ≠ 0 := fun heq => hx0 (Subtype.ext heq)
    obtain ⟨r, hr, hr0⟩ := hH.prop.2 x.val x.property hx0'
    obtain ⟨y, hy⟩ := hr
    exact ⟨r, ⟨y, Subtype.ext hy⟩, fun heq => hr0 (congrArg Subtype.val heq)⟩

/-- Injective envelopes are isomorphic by an isomorphism respecting their embeddings. -/
theorem ModuleInjectiveEnvelope.exists_iso {M : ModuleCat.{u} R}
    (E F : ModuleInjectiveEnvelope M) : ∃ e : E.obj ≅ F.obj, E.ι ≫ e.hom = F.ι := by
  have : Mono E.ι := E.essential.mono
  obtain ⟨f, hf⟩ := Injective.factors F.ι E.ι
  have hfInj : Function.Injective f.hom := E.essential.injective_of_comp f (by
    rw [hf]
    exact F.essential.1)
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr hfInj
  obtain ⟨p, hp⟩ := Injective.factors (𝟙 E.obj) f
  have hιp : F.ι ≫ p = E.ι := by
    rw [← hf, Category.assoc, hp, Category.comp_id]
  have hpInj : Function.Injective p.hom := F.essential.injective_of_comp p (by
    rw [hιp]
    exact E.essential.1)
  refine ⟨⟨f, p, hp, ?_⟩, hf⟩
  ext x
  apply hpInj
  exact congrArg (fun g : E.obj ⟶ E.obj => g.hom (p.hom x)) hp

/-- A choice of the genuine injective envelope. -/
def moduleInjectiveEnvelope (M : ModuleCat.{u} R) : ModuleInjectiveEnvelope M :=
  (nonempty_moduleInjectiveEnvelope M).some

end SGA.SGA2.ExposeIV
