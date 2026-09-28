/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.SpecSections

/-!
# Gluing sections of modules along local isomorphisms

For a local isomorphism `π : T ⟶ X` of schemes and an `𝒪_X`-module `P`, we show that the inverse
image of sections along `π` is injective over opens contained in the image of `π`, that global
sections of `π^* P` compatible on "overlaps" (pairs `a₁, a₂ : Y ⟶ T` with `a₁ ≫ π = a₂ ≫ π`)
come from sections of `P` over the image (`exists_pullbackAppTop_eq_of_isLocalIso`), and that a
morphism of modules is an isomorphism if it becomes one after inverse image along an open cover
(`isIso_of_isIso_pullback`). These are the Zariski descent statements for sections of modules
(Stacks, Tag 00AK and Tag 01AI).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {T X Y : Scheme.{u}}

/-- A section vanishing after inverse image along open immersions covering an open `U` is
zero. -/
lemma eq_zero_of_pullbackApp_eq_zero_of_le {ι : Type*} {W : ι → Scheme.{u}} (h : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (h i)] (M : X.Modules) (U : X.Opens)
    (hcov : ∀ y ∈ U, ∃ i, y ∈ Set.range (h i)) (s : Γ(M, U))
    (hs : ∀ i, pullbackApp (h i) M U s = 0) : s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun i ↦ h i ''ᵁ (h i ⁻¹ᵁ U)) U
    (fun i ↦ homOfLE ((h i).image_preimage_le U)) (fun y hy ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, w, rfl⟩ := hcov y hy
    exact Opens.mem_iSup.mpr ⟨i, w, hy, rfl⟩
  · rw [map_zero]
    exact (pullbackApp_eq_zero_iff_of_isOpenImmersion (h i) M U s).mp (hs i)

/-- Along a local isomorphism, the inverse image of sections over an open contained in the
image is injective. -/
lemma pullbackApp_injective_of_isLocalIso_of_le (π : T ⟶ X) [IsLocalIso π] (M : X.Modules)
    (U : X.Opens) (hU : (U : Set X) ⊆ Set.range π) : Function.Injective (pullbackApp π M U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  choose W hW hW' using fun x : T ↦ IsLocalIso.exists_isOpenImmersion (f := π) x
  refine eq_zero_of_pullbackApp_eq_zero_of_le (fun x : T ↦ (W x).ι ≫ π) M U (fun y hy ↦ ?_) s
    fun x ↦ ?_
  · obtain ⟨x, rfl⟩ := hU hy
    exact ⟨x, ⟨x, hW x⟩, rfl⟩
  · rw [pullbackApp_comp, hs, map_zero, map_zero]; rfl

/-- Local lifting along a local isomorphism. -/
lemma exists_lift_of_isLocalIso (π : T ⟶ X) [IsLocalIso π] (f : Y ⟶ X) (y : Y)
    (hy : f y ∈ Set.range π) :
    ∃ (O : Y.Opens) (a : O.toScheme ⟶ T), y ∈ O ∧ a ≫ π = O.ι ≫ f := by
  obtain ⟨t, ht⟩ := hy
  obtain ⟨W, htW, hW⟩ := IsLocalIso.exists_isOpenImmersion (f := π) t
  let k := W.ι ≫ π
  refine ⟨f ⁻¹ᵁ k.opensRange, IsOpenImmersion.lift k ((f ⁻¹ᵁ k.opensRange).ι ≫ f) ?_ ≫ W.ι,
    ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact z.2
  · change f y ∈ Set.range k
    exact ⟨⟨t, htW⟩, ht⟩
  · rw [Category.assoc]
    exact IsOpenImmersion.lift_fac _ _ _


/-- A morphism of modules is bijective on sections over opens contained in the image of an open
immersion along which its inverse image is an isomorphism. -/
lemma bijective_app_of_isIso_pullback (k : Y ⟶ X) [IsOpenImmersion k] {P Q : X.Modules}
    (φ : P ⟶ Q) [IsIso ((Scheme.Modules.pullback k).map φ)] (U : X.Opens)
    (hU : U ≤ k.opensRange) : Function.Bijective (φ.app U) := by
  have hP := pullbackApp_bijective_of_isOpenImmersion k P U hU
  have hQ := pullbackApp_bijective_of_isOpenImmersion k Q U hU
  have hk := ConcreteCategory.bijective_of_isIso (((Scheme.Modules.pullback k).map φ).app (k ⁻¹ᵁ U))
  have e : ⇑(pullbackApp k Q U) ∘ ⇑(φ.app U) =
      ⇑(((Scheme.Modules.pullback k).map φ).app (k ⁻¹ᵁ U)) ∘ ⇑(pullbackApp k P U) := by
    ext s
    exact pullbackApp_naturality k φ U s
  have h₂ : Function.Bijective (⇑(pullbackApp k Q U) ∘ ⇑(φ.app U)) := e ▸ hk.comp hP
  exact ⟨fun a b hab ↦ h₂.1 (by simp only [Function.comp_apply, hab]),
    fun y ↦ by
      obtain ⟨x, hx⟩ := h₂.2 (pullbackApp k Q U y)
      exact ⟨x, hQ.1 hx⟩⟩

/-- A morphism of modules which becomes an isomorphism after inverse image along a family of
open immersions covering `X` is an isomorphism. -/
lemma isIso_of_isIso_pullback {ι : Type*} {W : ι → Scheme.{u}} (k : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (k i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (k i)) {P Q : X.Modules}
    (φ : P ⟶ Q) [∀ i, IsIso ((Scheme.Modules.pullback (k i)).map φ)] : IsIso φ := by
  let B : (Σ i, {U : X.Opens // U ≤ (k i).opensRange}) → X.Opens := fun p ↦ p.2.1
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨U ⊓ (k i).opensRange, ⟨⟨i, _, inf_le_right⟩, rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  let P' : TopCat.Sheaf Ab X := ⟨P.presheaf, P.isSheaf⟩
  let Q' : TopCat.Sheaf Ab X := ⟨Q.presheaf, Q.isSheaf⟩
  let φ' : P' ⟶ Q' := ObjectProperty.homMk φ.mapPresheaf
  have : IsIso φ' :=
    TopCat.Sheaf.isIso_iff_isIso_basis hB fun p ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_app_of_isIso_pullback (k p.1) φ p.2.1 p.2.2)
  have h₁ : IsIso ((sheafToPresheaf _ _).map φ') := Functor.map_isIso _ φ'
  have : IsIso ((toPresheaf X).map φ) := h₁
  exact isIso_of_reflects_iso φ (toPresheaf X)


lemma presheaf_map_map_eq {X : Scheme.{u}} (P : X.Modules) {U₁ U₂ U₃ U₂' : X.Opens}
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₂') (d : U₂' ⟶ U₃) (x : Γ(P, U₃)) :
    P.presheaf.map a.op (P.presheaf.map b.op x) = P.presheaf.map c.op (P.presheaf.map d.op x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, Subsingleton.elim (a ≫ b) (c ≫ d)]

lemma pullbackCompIso'_hom_app_pullbackApp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (hf : f ≫ g = q) (M : Z.Modules) (W : Z.Opens) (hle : q ⁻¹ᵁ W ≤ f ⁻¹ᵁ g ⁻¹ᵁ W)
    (x : Γ(M, W)) :
    (pullbackCompIso' f g q hf M).hom.app (q ⁻¹ᵁ W) (pullbackApp q M W x) =
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).presheaf.map
        (homOfLE hle).op (pullbackApp f _ (g ⁻¹ᵁ W) (pullbackApp g M W x)) := by
  subst hf
  have e : homOfLE hle = 𝟙 ((f ≫ g) ⁻¹ᵁ W) := Subsingleton.elim _ _
  erw [e, op_id, CategoryTheory.Functor.map_id]
  rw [pullbackApp_comp]
  change ((pullbackComp f g).inv.app M).app _ (((pullbackComp f g).hom.app M).app _ _) = _
  exact natIso_inv_app_hom_app (pullbackComp f g) M _ _

lemma presheaf_map_map_eq' {X : Scheme.{u}} (P : X.Modules) {U₁ U₂ U₃ : X.Opens}
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₃) (x : Γ(P, U₃)) :
    P.presheaf.map a.op (P.presheaf.map b.op x) = P.presheaf.map c.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (a ≫ b) c]

lemma pullbackAppTop_map (w : Y ⟶ X) (P : X.Modules) {U₁ U₂ : X.Opens} (i : U₁ ⟶ U₂)
    (h₁ : ⊤ ≤ w ⁻¹ᵁ U₁) (h₂ : ⊤ ≤ w ⁻¹ᵁ U₂) (s : Γ(P, U₂)) :
    pullbackAppTop w P U₁ h₁ (P.presheaf.map i.op s) = pullbackAppTop w P U₂ h₂ s := by
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [pullbackApp_map]
  exact presheaf_map_map_eq' _ _ _ _ _

lemma pullbackAppTop_bijective_of_isOpenImmersion (k : Y ⟶ X) [IsOpenImmersion k]
    (P : X.Modules) (U : X.Opens) (hU : U ≤ k.opensRange) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    Function.Bijective (pullbackAppTop k P U h) := by
  have e : ⇑(pullbackAppTop k P U h) = ⇑(((Scheme.Modules.pullback k).obj P).presheaf.map
      (homOfLE h).op) ∘ ⇑(pullbackApp k P U) := by
    ext x
    exact ConcreteCategory.comp_apply _ _ x
  rw [e]
  exact (((Scheme.Modules.pullback k).obj P).presheaf.map_bijective_of_eq (homOfLE h)
    (top_le_iff.mp h).symm).comp (pullbackApp_bijective_of_isOpenImmersion k P U hU)

/-- Two global sections of `π^* P` agreeing after inverse image along the inclusions of an open
cover of `T` are equal. -/
lemma eq_of_pullbackTop_eq {ι : Type*} {W : ι → T.Opens} (hcov : ∀ t, ∃ i, t ∈ W i) (π : T ⟶ X)
    (P : X.Modules) (z z' : Γ((Scheme.Modules.pullback π).obj P, ⊤))
    (h : ∀ i, pullbackTop (W i).ι π ((W i).ι ≫ π) rfl P z =
      pullbackTop (W i).ι π ((W i).ι ≫ π) rfl P z') : z = z' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_pullbackApp_eq_zero_of_le (fun i ↦ (W i).ι) _ ⊤
    (fun t _ ↦ (hcov t).imp fun i hi ↦ ⟨⟨t, hi⟩, rfl⟩) _ fun i ↦ ?_
  have := h i
  rw [pullbackTop_apply, pullbackTop_apply] at this
  have e := (ConcreteCategory.bijective_of_isIso
    ((pullbackCompIso' (W i).ι π ((W i).ι ≫ π) rfl P).inv.app ⊤)).1 this
  rw [map_sub, e, sub_self]

/-- Sections of a module over the image `U` of a local isomorphism `π : T ⟶ X` descend: a global
section `n` of `π^* P` whose inverse images along any `a₁, a₂ : Y ⟶ T` with `a₁ ≫ π = a₂ ≫ π`
agree is the inverse image of a section of `P` over `U`. -/
theorem exists_pullbackAppTop_eq_of_isLocalIso (π : T ⟶ X) [IsLocalIso π] (P : X.Modules)
    (U : X.Opens) (hU : (U : Set X) = Set.range π) (hπ : ⊤ ≤ π ⁻¹ᵁ U)
    (n : Γ((Scheme.Modules.pullback π).obj P, ⊤))
    (hn : ∀ ⦃Y : Scheme.{u}⦄ (a₁ a₂ : Y ⟶ T) (e : a₁ ≫ π = a₂ ≫ π),
      pullbackTop a₁ π (a₁ ≫ π) rfl P n = pullbackTop a₂ π (a₁ ≫ π) e.symm P n) :
    ∃ x : Γ(P, U), pullbackAppTop π P U hπ x = n := by
  have hn' : ∀ ⦃Y : Scheme.{u}⦄ (a₁ a₂ : Y ⟶ T) (w : Y ⟶ X) (e₁ : a₁ ≫ π = w)
      (e₂ : a₂ ≫ π = w), pullbackTop a₁ π w e₁ P n = pullbackTop a₂ π w e₂ P n := by
    intro Y a₁ a₂ w e₁ e₂
    subst e₁
    exact hn a₁ a₂ e₂.symm
  choose W hW hW' using fun t : T ↦ IsLocalIso.exists_isOpenImmersion (f := π) t
  let k : ∀ t, (W t).toScheme ⟶ X := fun t ↦ (W t).ι ≫ π
  let R : T → X.Opens := fun t ↦ (k t).opensRange
  have hRU (t : T) : R t ≤ U := by
    rintro _ ⟨z, rfl⟩
    change π ((W t).ι z) ∈ (U : Set X)
    rw [hU]; exact ⟨_, rfl⟩
  have hkR (t : T) : ⊤ ≤ k t ⁻¹ᵁ R t := fun z _ ↦ ⟨z, rfl⟩
  choose x hx using fun t ↦ (pullbackAppTop_bijective_of_isOpenImmersion (k t) P (R t) le_rfl
    (hkR t)).2 (pullbackTop (W t).ι π (k t) rfl P n)
  -- compatibility on overlaps
  have hcompat : TopCat.Presheaf.IsCompatible P.presheaf R x := by
    intro t t'
    let O := R t ⊓ R t'
    have hOt : Set.range O.ι ⊆ Set.range (k t) := by
      rw [O.range_ι]; exact fun z hz ↦ hz.1
    have hOt' : Set.range O.ι ⊆ Set.range (k t') := by
      rw [O.range_ι]; exact fun z hz ↦ hz.2
    let l := IsOpenImmersion.lift (k t) O.ι hOt
    let l' := IsOpenImmersion.lift (k t') O.ι hOt'
    have hl : l ≫ k t = O.ι := IsOpenImmersion.lift_fac _ _ _
    have hl' : l' ≫ k t' = O.ι := IsOpenImmersion.lift_fac _ _ _
    have hO : ⊤ ≤ O.ι ⁻¹ᵁ O := by rw [Scheme.Opens.ι_preimage_self]
    apply (pullbackAppTop_bijective_of_isOpenImmersion O.ι P O (by rw [Scheme.Opens.opensRange_ι])
      hO).1
    have key (s : T) (i : O ⟶ R s) (ls : O.toScheme ⟶ (W s).toScheme) (hls : ls ≫ k s = O.ι) :
        pullbackAppTop O.ι P O hO (P.presheaf.map i.op (x s)) =
          pullbackTop (ls ≫ (W s).ι) π O.ι (by rw [Category.assoc]; exact hls) P n := by
      rw [pullbackAppTop_map O.ι P i hO (by rw [← hls]; exact fun z _ ↦ ⟨ls z, rfl⟩)]
      rw [← pullbackTop_pullbackAppTop ls (k s) O.ι hls P (R s) (hkR s), hx s,
        pullbackTop_comp]
    rw [key t _ l hl, key t' _ l' hl']
    exact hn' _ _ _ _ _
  have hcover : U ≤ iSup R := fun z hz ↦ by
    have : z ∈ Set.range π := hU ▸ hz
    obtain ⟨t, rfl⟩ := this
    exact Opens.mem_iSup.mpr ⟨t, ⟨t, hW t⟩, rfl⟩
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨P.presheaf, P.isSheaf⟩ R U
    (fun t ↦ homOfLE (hRU t)) hcover x hcompat
  refine ⟨y, eq_of_pullbackTop_eq (fun t ↦ ⟨t, hW t⟩) π P _ _ fun t ↦ ?_⟩
  rw [pullbackTop_pullbackAppTop (W t).ι π _ rfl P U hπ (fun z _ ↦ hRU t ⟨z, rfl⟩),
    ← hx t, ← hy t, pullbackAppTop_map _ _ _ _ (fun z _ ↦ hRU t ⟨z, rfl⟩)]

end AlgebraicGeometry.Scheme.Modules
