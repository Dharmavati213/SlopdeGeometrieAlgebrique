/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.QuasiCoherent.DescentChart

/-!
# Zariski descent of modules

Let `g : S' ⟶ S` be a local isomorphism of schemes (for instance `∐ Uᵢ ⟶ S` for an open cover
`(Uᵢ)` of `S`), and `E` a module on `S'` with a descent datum `D` relative to `g` (gluing data).
Then the counit `g^* M ⟶ E` of the descended module `M = descentModule D` is an isomorphism
(`isIso_descentCounit_of_isLocalIso`), so `D` is isomorphic to the descent datum of `g^* M`
(`descentIsoOfIsLocalIso`); if `g` is surjective and `E` is quasi-coherent, so is `M`
(`isQuasicoherent_descentModule_of_isLocalIso`). This is the gluing of sheaves of modules
(EGA 0_I, 3.3), in the language of descent data.

The key point is local: for an open `O ⊆ S'` mapped isomorphically onto its image by `g`, a
section of `E` over `O` extends uniquely to a section over `g⁻¹(g(O))` compatible with the
descent datum (`exists_isDescentSection_map_eq`, `eq_zero_of_isDescentSection_of_map_eq_zero`),
via the retraction `retr g O : g⁻¹(g(O)) ⟶ O`. We also record the converse of
`IsDescentSection.app_top` (`isDescentSection_of_app_top`).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- A section is compatible with the descent datum if the descent condition holds on global
sections for all pairs of maps into the inverse image of the open. -/
lemma isDescentSection_of_app_top (W : S.Opens) (x : Γ(descentObj D, g ⁻¹ᵁ W))
    (hx : ∀ ⦃Y : Scheme.{u}⦄ (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g)
      (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ g ⁻¹ᵁ W) (h₂ : ⊤ ≤ f₂ ⁻¹ᵁ g ⁻¹ᵁ W),
      (descentHom D f₁ f₂ h).app ⊤ (pullbackAppTop f₁ (descentObj D) (g ⁻¹ᵁ W) h₁ x) =
        pullbackAppTop f₂ (descentObj D) (g ⁻¹ᵁ W) h₂ x) :
    IsDescentSection D W x := by
  intro Y f₁ f₂ hf
  set O := f₁ ⁻¹ᵁ g ⁻¹ᵁ W
  have hO₂ : O ≤ f₂ ⁻¹ᵁ g ⁻¹ᵁ W := preimage_le_of_comp_eq hf _
  set ι := O.ι
  have hO : ⊤ ≤ ι ⁻¹ᵁ O := fun z _ ↦ z.2
  have hO' : ⊤ ≤ ι ⁻¹ᵁ (f₂ ⁻¹ᵁ g ⁻¹ᵁ W) := hO.trans (fun z hz ↦ hO₂ hz)
  have hq₁ : ⊤ ≤ (ι ≫ f₁) ⁻¹ᵁ g ⁻¹ᵁ W := hO
  have hq₂ : ⊤ ≤ (ι ≫ f₂) ⁻¹ᵁ g ⁻¹ᵁ W := hO'
  apply (pullbackAppTop_bijective_of_isOpenImmersion ι
    ((Scheme.Modules.pullback f₂).obj (descentObj D)) O (by rw [Scheme.Opens.opensRange_ι]) hO).1
  apply (ConcreteCategory.bijective_of_isIso
    ((pullbackCompIso' ι f₂ (ι ≫ f₂) rfl (descentObj D)).inv.app ⊤)).1
  rw [← pullbackAppTop_naturality, ← pullbackCompIso'_hom_app_pullbackAppTop ι f₁ (ι ≫ f₁) rfl
    _ _ hq₁ hO, pullbackAppTop_map _ _ _ hO hO',
    pullbackCompIso'_inv_app_pullbackAppTop ι f₂ (ι ≫ f₂) rfl _ _ hq₂ hO']
  have key := congr(Hom.app $(descentHom_pull D ι f₁ f₂ hf
    (by rw [Category.assoc, hf, Category.assoc])) ⊤
    (pullbackAppTop (ι ≫ f₁) (descentObj D) (g ⁻¹ᵁ W) hq₁ x))
  rw [Hom.comp_app_apply, Hom.comp_app_apply] at key
  rw [key]
  exact hx _ _ _ hq₁ hq₂

section LocalIso

variable (g) (O : S'.Opens) [IsOpenImmersion (O.ι ≫ g)]

lemma le_preimage_opensRange : O ≤ g ⁻¹ᵁ (O.ι ≫ g).opensRange :=
  fun o ho ↦ ⟨⟨o, ho⟩, rfl⟩

lemma range_ι_comp_subset :
    Set.range ((g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι ≫ g) ⊆ Set.range (O.ι ≫ g) := by
  rintro _ ⟨z, rfl⟩
  exact z.2

/-- The retraction `g⁻¹(g(O)) ⟶ O`, for `O` mapped isomorphically onto its image by `g`. -/
noncomputable def retr : (g ⁻¹ᵁ (O.ι ≫ g).opensRange).toScheme ⟶ O.toScheme :=
  IsOpenImmersion.lift (O.ι ≫ g) ((g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι ≫ g) (range_ι_comp_subset g O)

lemma retr_comp : (retr g O ≫ O.ι) ≫ g = (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι ≫ g := by
  rw [Category.assoc]
  exact IsOpenImmersion.lift_fac _ _ _

lemma eq_of_comp_eq {Y : Scheme.{u}} {b₁ b₂ : Y ⟶ O.toScheme} (h : b₁ ≫ O.ι ≫ g = b₂ ≫ O.ι ≫ g) :
    b₁ = b₂ :=
  (cancel_mono (O.ι ≫ g)).1 h

lemma homOfLE_retr :
    S'.homOfLE (le_preimage_opensRange g O) ≫ retr g O = 𝟙 _ := by
  apply eq_of_comp_eq g O
  rw [Category.assoc, ← Category.assoc (retr g O), retr_comp, Scheme.homOfLE_ι_assoc,
    Category.id_comp]

lemma top_le_retr_comp : ⊤ ≤ (retr g O ≫ O.ι) ⁻¹ᵁ O := fun z _ ↦ (retr g O z).2

lemma top_le_retr_comp' : ⊤ ≤ (retr g O ≫ O.ι) ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange :=
  fun z _ ↦ le_preimage_opensRange g O (retr g O z).2

lemma top_le_ι_preimage : ⊤ ≤ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange :=
  fun z _ ↦ z.2

lemma le_opensRange_ι : g ⁻¹ᵁ (O.ι ≫ g).opensRange ≤ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι]

/-- A section compatible with the descent datum over `g(O)` vanishing on `O` vanishes. -/
lemma eq_zero_of_isDescentSection_of_map_eq_zero
    (y : Γ(descentObj D, g ⁻¹ᵁ (O.ι ≫ g).opensRange))
    (hy : IsDescentSection D (O.ι ≫ g).opensRange y)
    (h0 : (descentObj D).presheaf.map (homOfLE (le_preimage_opensRange g O)).op y = 0) :
    y = 0 := by
  have hO : ⊤ ≤ O.ι ⁻¹ᵁ O := fun z _ ↦ z.2
  have hOV : ⊤ ≤ O.ι ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange := fun z _ ↦ le_preimage_opensRange g O z.2
  have key := hy.app_top D (retr g O ≫ O.ι) _ (retr_comp g O)
    (top_le_retr_comp' g O) (top_le_ι_preimage g O)
  rw [← pullbackTop_pullbackAppTop (retr g O) O.ι (retr g O ≫ O.ι) rfl _ _ hOV,
    ← pullbackAppTop_map O.ι _ (homOfLE (le_preimage_opensRange g O)) hO hOV, h0, map_zero,
    map_zero, map_zero] at key
  exact (pullbackAppTop_bijective_of_isOpenImmersion _ _ _ (le_opensRange_ι g O)
    (top_le_ι_preimage g O)).1 (key.symm.trans (map_zero _).symm)

/-- A section of `E` over `O` extends to a section over `g⁻¹(g(O))` compatible with the descent
datum. -/
lemma exists_isDescentSection_map_eq (t : Γ(descentObj D, O)) :
    ∃ y : Γ(descentObj D, g ⁻¹ᵁ (O.ι ≫ g).opensRange),
      IsDescentSection D (O.ι ≫ g).opensRange y ∧
      (descentObj D).presheaf.map (homOfLE (le_preimage_opensRange g O)).op y = t := by
  obtain ⟨y, hy⟩ := (pullbackAppTop_bijective_of_isOpenImmersion
    (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι (descentObj D) (g ⁻¹ᵁ (O.ι ≫ g).opensRange)
    (le_opensRange_ι g O) (top_le_ι_preimage g O)).2
    ((descentHom D (retr g O ≫ O.ι) (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι (retr_comp g O)).app ⊤
      (pullbackAppTop (retr g O ≫ O.ι) (descentObj D) O (top_le_retr_comp g O) t))
  have hO : ⊤ ≤ O.ι ⁻¹ᵁ O := fun z _ ↦ z.2
  have hOV : ⊤ ≤ O.ι ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange :=
    fun z _ ↦ le_preimage_opensRange g O z.2
  have hu : S'.homOfLE (le_preimage_opensRange g O) ≫ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι = O.ι :=
    Scheme.homOfLE_ι _ _
  have hu' : S'.homOfLE (le_preimage_opensRange g O) ≫ retr g O ≫ O.ι = O.ι := by
    rw [← Category.assoc, homOfLE_retr, Category.id_comp]
  refine ⟨y, isDescentSection_of_app_top D _ y fun Y a₁ a₂ ha h₁ h₂ ↦ ?_, ?_⟩
  · have hb (a : Y ⟶ S') (ha' : ⊤ ≤ a ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange) :
        ∃ b : Y ⟶ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).toScheme,
          b ≫ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι = a := by
      refine ⟨IsOpenImmersion.lift (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι a ?_,
        IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ha' trivial
    obtain ⟨b₁, hb₁⟩ := hb a₁ h₁
    obtain ⟨b₂, hb₂⟩ := hb a₂ h₂
    have hr : b₂ ≫ retr g O = b₁ ≫ retr g O := by
      apply eq_of_comp_eq g O
      have e₁ : (b₁ ≫ retr g O) ≫ O.ι ≫ g = a₁ ≫ g := by
        rw [Category.assoc, ← Category.assoc (retr g O), retr_comp, ← Category.assoc, hb₁]
      have e₂ : (b₂ ≫ retr g O) ≫ O.ι ≫ g = a₂ ≫ g := by
        rw [Category.assoc, ← Category.assoc (retr g O), retr_comp, ← Category.assoc, hb₂]
      rw [e₁, e₂, ha]
    have hexpr (a : Y ⟶ S') (b : Y ⟶ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).toScheme)
        (hb : b ≫ (g ⁻¹ᵁ (O.ι ≫ g).opensRange).ι = a)
        (ha' : ⊤ ≤ a ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange)
        (hc : b ≫ retr g O ≫ O.ι = b₁ ≫ retr g O ≫ O.ι) :
        pullbackAppTop a (descentObj D) _ ha' y =
          (descentHom D (b₁ ≫ retr g O ≫ O.ι) a (by
            rw [← hc, Category.assoc, retr_comp, ← Category.assoc, hb])).app ⊤
          (pullbackAppTop (b₁ ≫ retr g O ≫ O.ι) (descentObj D) O
            (fun z _ ↦ top_le_retr_comp g O (Set.mem_univ (b₁ z))) t) := by
      rw [← pullbackTop_pullbackAppTop b _ a hb _ _ (top_le_ι_preimage g O) ha', hy,
        descentHom_pullbackTop D b (retr g O ≫ O.ι) _ (retr_comp g O) (b₁ ≫ retr g O ≫ O.ι) a
          hc hb (by rw [← hc, Category.assoc, retr_comp, ← Category.assoc, hb]),
        pullbackTop_pullbackAppTop b (retr g O ≫ O.ι) (b₁ ≫ retr g O ≫ O.ι) hc _ O
          (top_le_retr_comp g O) (fun z _ ↦ top_le_retr_comp g O (Set.mem_univ (b₁ z)))]
    have hc₂ : b₂ ≫ retr g O ≫ O.ι = b₁ ≫ retr g O ≫ O.ι := by
      rw [← Category.assoc, hr, Category.assoc]
    rw [hexpr a₁ b₁ hb₁ h₁ rfl, hexpr a₂ b₂ hb₂ h₂ hc₂, ← Hom.comp_app_apply, descentHom_comp]
  · apply (pullbackAppTop_bijective_of_isOpenImmersion O.ι (descentObj D) O
      (by rw [Scheme.Opens.opensRange_ι]) hO).1
    rw [pullbackAppTop_map O.ι _ _ hO hOV,
      ← pullbackTop_pullbackAppTop _ _ O.ι hu _ _ (top_le_ι_preimage g O) hOV, hy,
      descentHom_pullbackTop D _ (retr g O ≫ O.ι) _ (retr_comp g O) O.ι O.ι hu' hu rfl,
      descentHom_self,
      pullbackTop_pullbackAppTop _ (retr g O ≫ O.ι) O.ι hu' _ O (top_le_retr_comp g O) hO]
    rfl

/-- Over an open `O` mapped isomorphically onto its image by `g`, the counit of the descended
module is bijective on sections. -/
lemma bijective_descentCounit_app : Function.Bijective ((descentCounit D).app O) := by
  have hO : ⊤ ≤ O.ι ⁻¹ᵁ O := fun z _ ↦ z.2
  have hOV : ⊤ ≤ O.ι ⁻¹ᵁ g ⁻¹ᵁ (O.ι ≫ g).opensRange :=
    fun z _ ↦ le_preimage_opensRange g O z.2
  have hk : ⊤ ≤ (O.ι ≫ g) ⁻¹ᵁ (O.ι ≫ g).opensRange := fun z _ ↦ ⟨z, rfl⟩
  let M := descentModule D
  let r : Γ(M, (O.ι ≫ g).opensRange) → Γ((Scheme.Modules.pullback g).obj M, O) := fun m ↦
    ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE (le_preimage_opensRange g O)).op
      (pullbackApp g M _ m)
  have hr : Function.Bijective r := by
    have hf := pullbackAppTop_bijective_of_isOpenImmersion O.ι ((Scheme.Modules.pullback g).obj M)
      O (by rw [Scheme.Opens.opensRange_ι]) hO
    rw [← Function.Bijective.of_comp_iff' hf]
    have e : ⇑(pullbackAppTop O.ι ((Scheme.Modules.pullback g).obj M) O hO) ∘ r =
        ⇑((pullbackCompIso' O.ι g (O.ι ≫ g) rfl M).hom.app ⊤) ∘
          ⇑(pullbackAppTop (O.ι ≫ g) M _ hk) := by
      funext m
      simp only [Function.comp_apply, r]
      rw [pullbackAppTop_map O.ι _ _ hO hOV,
        pullbackCompIso'_hom_app_pullbackAppTop O.ι g (O.ι ≫ g) rfl M _ hk hOV]
    rw [e]
    exact (ConcreteCategory.bijective_of_isIso _).comp
      (pullbackAppTop_bijective_of_isOpenImmersion _ M _ le_rfl hk)
  let ρ := (descentModuleι D).app (O.ι ≫ g).opensRange ≫
    (descentObj D).presheaf.map (homOfLE (le_preimage_opensRange g O)).op
  have hρ : Function.Bijective ρ := by
    refine ⟨(injective_iff_map_eq_zero ρ.hom).2 fun m hm ↦ ?_, fun t ↦ ?_⟩
    · apply Subtype.ext
      exact eq_zero_of_isDescentSection_of_map_eq_zero g D O m.1 m.2 hm
    · obtain ⟨y, hy, hyt⟩ := exists_isDescentSection_map_eq g D O t
      exact ⟨⟨y, hy⟩, hyt⟩
  have e : ⇑((descentCounit D).app O) ∘ r = ⇑ρ := by
    funext m
    simp only [Function.comp_apply, r]
    rw [Hom.app_map, descentCounit_app_pullbackApp]
    rfl
  rw [← Function.Bijective.of_comp_iff _ hr, e]
  exact hρ

end LocalIso

set_option backward.isDefEq.respectTransparency.types false in
/-- Zariski descent: along a local isomorphism `g` (for instance `∐ Uᵢ ⟶ S` for an open cover),
the counit `g^* M ⟶ E` of the descended module is an isomorphism, for every module `E` with a
descent datum. -/
theorem isIso_descentCounit_of_isLocalIso [IsLocalIso g] : IsIso (descentCounit D) := by
  let B : {O : S'.Opens // IsOpenImmersion (O.ι ≫ g)} → S'.Opens := fun O ↦ O.1
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨W, hxW, hW⟩ := IsLocalIso.exists_isOpenImmersion (f := g) x
    have : IsOpenImmersion ((W ⊓ U).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι S' (inf_le_left : W ⊓ U ≤ W), Category.assoc]
      infer_instance
    exact ⟨W ⊓ U, ⟨⟨W ⊓ U, this⟩, rfl⟩, ⟨hxW, hx⟩, inf_le_right⟩
  let P' : TopCat.Sheaf Ab S' :=
    ⟨((Scheme.Modules.pullback g).obj (descentModule D)).presheaf,
      ((Scheme.Modules.pullback g).obj (descentModule D)).isSheaf⟩
  let Q' : TopCat.Sheaf Ab S' := ⟨(descentObj D).presheaf, (descentObj D).isSheaf⟩
  let φ' : P' ⟶ Q' := ObjectProperty.homMk (descentCounit D).mapPresheaf
  have : IsIso φ' :=
    TopCat.Sheaf.isIso_iff_isIso_basis hB fun O ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      (by have := O.2; exact bijective_descentCounit_app g D O.1)
  have h₁ : IsIso ((sheafToPresheaf _ _).map φ') := Functor.map_isIso _ φ'
  have : IsIso ((toPresheaf S').map (descentCounit D)) := h₁
  exact isIso_of_reflects_iso (descentCounit D) (toPresheaf S')

set_option backward.isDefEq.respectTransparency.types false in
/-- Zariski descent: along a surjective local isomorphism, the module obtained by descent of a
quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_descentModule_of_isLocalIso [IsLocalIso g] [Surjective g]
    [(descentObj D).IsQuasicoherent] : (descentModule D).IsQuasicoherent := by
  have := isIso_descentCounit_of_isLocalIso D
  have hk : ∀ O : {O : S'.Opens // IsOpenImmersion (O.ι ≫ g)},
      IsOpenImmersion ((fun O : {O : S'.Opens // IsOpenImmersion (O.ι ≫ g)} ↦ O.1.ι ≫ g) O) :=
    fun O ↦ O.2
  refine isQuasicoherent_of_forall_pullback
    (fun O : {O : S'.Opens // IsOpenImmersion (O.ι ≫ g)} ↦ O.1.ι ≫ g) (fun x ↦ ?_) fun O ↦ ?_
  · obtain ⟨y, rfl⟩ := g.surjective x
    obtain ⟨W, hyW, hW⟩ := IsLocalIso.exists_isOpenImmersion (f := g) y
    exact ⟨⟨W, hW⟩, ⟨⟨y, hyW⟩, rfl⟩⟩
  · let e : (Scheme.Modules.pullback (O.1.ι ≫ g)).obj (descentModule D) ≅
        (Scheme.Modules.pullback O.1.ι).obj (descentObj D) :=
      ((pullbackComp O.1.ι g).app (descentModule D)).symm ≪≫
        (Scheme.Modules.pullback O.1.ι).mapIso (asIso (descentCounit D))
    exact (SheafOfModules.isQuasicoherent (O.1 : Scheme.{u}).ringCatSheaf).prop_of_iso e.symm
      inferInstance

/-- Zariski descent: along a local isomorphism, every descent datum is isomorphic to the descent
datum of the inverse image of the descended module. -/
noncomputable def descentIsoOfIsLocalIso [IsLocalIso g] :
    (pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj (descentModule D) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun _ ↦ @asIso _ _ _ _ (descentCounit D) (isIso_descentCounit_of_isLocalIso D))
    (fun _ q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ descentCounit_comm'' D q i₁ i₂ f₁ f₂ hf₁ hf₂)

end AlgebraicGeometry.Scheme.Modules
