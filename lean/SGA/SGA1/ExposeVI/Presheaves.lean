/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Bifibered
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# SGA 1, Exposé VI, VI.11 b): presheaves on variable spaces

A functor `Φ : E ⥤ Cat` defines a co-split cofibered category over `E`: the Grothendieck
construction `Grothendieck Φ`, whose arrows `(S, x) ⟶ (T, y)` are pairs `(f, u : f_* x ⟶ y)`,
with cocartesian transports `(f, 𝟙)`. If every `Φ(f)` has a right adjoint `f^*`, the category is
also fibered (SGA deduces this from VI.10; we prove prefiberedness directly and conclude with
VI.10.1).

Applied to `X ↦ (Presheaf C X)ᵒᵖ`, `f ↦ (f_*)ᵒᵖ` this is SGA's cofibered category of presheaves
on variable spaces; when `C` has colimits the inverse images of presheaves exist, so it is
bifibered.
-/

universe w v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

/-- In a category over `E` in which every arrow of `E` has strongly cocartesian lifts, every
cocartesian arrow is strongly cocartesian (dual of mathlib's
`IsFibered.isStronglyCartesian_of_exists_isCartesian`). -/
theorem isStronglyCocartesian_of_exists_isStronglyCocartesian {E : Type u} [Category.{v} E]
    {C : Type u₁} [Category.{v₁} C] (p : C ⥤ E)
    (h : ∀ (a : C) (S : E) (f : p.obj a ⟶ S), ∃ (b : C) (φ : a ⟶ b),
      IsStronglyCocartesian p f φ)
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCocartesian p f φ] :
    IsStronglyCocartesian p f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ
  obtain ⟨b', ψ, hψ⟩ := h _ _ (p.map φ)
  let τ' := IsStronglyCocartesian.map p (p.map φ) ψ (f' := p.map φ ≫ g) rfl φ'
  let e := IsCocartesian.codomainUniqueUpToIso p (p.map φ) φ ψ
  have : IsHomLift p (𝟙 _) e.hom :=
    IsCocartesian.map_isHomLift p (p.map φ) φ ψ
  refine ⟨e.hom ≫ τ', ⟨inferInstance, ?_⟩, ?_⟩
  · simp [τ', e, IsCocartesian.codomainUniqueUpToIso]
  · rintro π ⟨hπ, hπ_comp⟩
    rw [← Iso.inv_comp_eq]
    have : IsHomLift p (𝟙 _) e.inv :=
      IsCocartesian.map_isHomLift p (p.map φ) ψ φ
    apply IsStronglyCocartesian.map_uniq p (p.map φ) ψ rfl φ'
    have h₁ : ψ ≫ e.inv = φ := IsCocartesian.fac p (p.map φ) ψ φ
    rw [reassoc_of% h₁, hπ_comp]

/-- A category over `E` in which every arrow has strongly cocartesian lifts is cofibered. -/
theorem isCofibered_of_exists_isStronglyCocartesian {E : Type u} [Category.{v} E]
    {C : Type u₁} [Category.{v₁} C] (p : C ⥤ E)
    (h : ∀ (a : C) (S : E) (f : p.obj a ⟶ S), ∃ (b : C) (φ : a ⟶ b),
      IsStronglyCocartesian p f φ) : IsCofibered p := by
  have : IsPreCofibered p := ⟨fun {a S} f ↦ by
    obtain ⟨b, φ, hφ⟩ := h a S f
    exact ⟨b, φ, inferInstance⟩⟩
  refine (isCofibered_iff_comp p).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
  have := isStronglyCocartesian_of_exists_isStronglyCocartesian p h f φ
  have := isStronglyCocartesian_of_exists_isStronglyCocartesian p h g ψ
  infer_instance

section Grothendieck

variable {E : Type u} [Category.{v} E] (Φ : E ⥤ Cat.{v₂, u₂})

/-- VI.11 b): the transport `(f, 𝟙) : (S, x) ⟶ (T, f_* x)` of the Grothendieck construction. -/
def grothendieckTransport (X : Grothendieck Φ) {T : E} (f : X.base ⟶ T) :
    X ⟶ (⟨T, (Φ.map f).toFunctor.obj X.fiber⟩ : Grothendieck Φ) :=
  ⟨f, 𝟙 _⟩

private theorem map_comp_obj {A B D : E} (f : A ⟶ B) (g : B ⟶ D)
    (x : Φ.obj A) : (Φ.map g).toFunctor.obj ((Φ.map f).toFunctor.obj x) =
      (Φ.map (f ≫ g)).toFunctor.obj x := by
  rw [Φ.map_comp]
  rfl

/-- VI.11 b): the transports `(f, 𝟙)` are strongly cocartesian. -/
theorem grothendieckTransport_isStronglyCocartesian (X : Grothendieck Φ) {T : E}
    (f : X.base ⟶ T) :
    IsStronglyCocartesian (Grothendieck.forget Φ) f (grothendieckTransport Φ X f) where
  toIsHomLift := CategoryTheory.IsHomLift.map (Grothendieck.forget Φ) (grothendieckTransport Φ X f)
  universal_property' {b'} g ψ hψ := by
    change T ⟶ b'.base at g
    have hbase : ψ.base = f ≫ g :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget Φ) X b' (f ≫ g) ψ hψ).symm
    obtain ⟨ψb, ψf⟩ := ψ
    change ψb = f ≫ g at hbase
    subst hbase
    let χ : (⟨T, (Φ.map f).toFunctor.obj X.fiber⟩ : Grothendieck Φ) ⟶ b' :=
      ⟨g, eqToHom (map_comp_obj Φ f g X.fiber) ≫ ψf⟩
    refine ⟨χ, ⟨CategoryTheory.IsHomLift.map (Grothendieck.forget Φ) χ, ?_⟩, ?_⟩
    · refine Grothendieck.ext _ _ rfl ?_
      dsimp only [grothendieckTransport, χ, Grothendieck.comp_fiber]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans_assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rfl
    · rintro ⟨χb, χf⟩ ⟨hχ', hfac⟩
      have hχ'base : χb = g :=
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget Φ)
          ⟨T, (Φ.map f).toFunctor.obj X.fiber⟩ b' g _ hχ').symm
      subst hχ'base
      have := Grothendieck.congr hfac
      dsimp only [Grothendieck.comp_fiber, grothendieckTransport] at this
      erw [CategoryTheory.Functor.map_id, Category.id_comp] at this
      refine Grothendieck.ext _ _ rfl ?_
      dsimp only [χ]
      rw [(eqToHom_comp_iff _ _ _).mp this]
      erw [eqToHom_trans_assoc, eqToHom_trans_assoc]

/-- VI.11 b): a functor `Φ : E ⥤ Cat` defines a (co-split) cofibered category over `E`. -/
instance grothendieck_isCofibered : IsCofibered (Grothendieck.forget Φ) :=
  isCofibered_of_exists_isStronglyCocartesian _ fun X _ f ↦
    ⟨_, grothendieckTransport Φ X f, grothendieckTransport_isStronglyCocartesian Φ X f⟩

/-- VI.11 b): if `Φ(f)` has a right adjoint `f^*`, the arrow `(f, ε) : (S, f^* y) ⟶ (T, y)`
given by the counit is cartesian. -/
theorem grothendieck_isCartesian_counit {S T : E} (f : S ⟶ T) {G : Φ.obj T ⥤ Φ.obj S}
    (adj : (Φ.map f).toFunctor ⊣ G) (y : Φ.obj T) :
    IsCartesian (Grothendieck.forget Φ) f
      (⟨f, adj.counit.app y⟩ : (⟨S, G.obj y⟩ : Grothendieck Φ) ⟶ ⟨T, y⟩) := by
  have : IsHomLift (Grothendieck.forget Φ) f
      (⟨f, adj.counit.app y⟩ : (⟨S, G.obj y⟩ : Grothendieck Φ) ⟶ ⟨T, y⟩) :=
    CategoryTheory.IsHomLift.map (Grothendieck.forget Φ)
      (⟨f, adj.counit.app y⟩ : (⟨S, G.obj y⟩ : Grothendieck Φ) ⟶ ⟨T, y⟩)
  refine ⟨fun {a'} φ hφ ↦ ?_⟩
  obtain ⟨S', x⟩ := a'
  have hS : S' = S := IsHomLift.domain_eq (Grothendieck.forget Φ) f φ
  subst hS
  have hφb : φ.base = f :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget Φ) ⟨S', x⟩ ⟨T, y⟩ f φ hφ).symm
  obtain ⟨φb, φf⟩ := φ
  change S' ⟶ T at φb
  change (Φ.map φb).toFunctor.obj x ⟶ y at φf
  change φb = f at hφb
  subst hφb
  have hid : (Φ.map (𝟙 S')).toFunctor.obj x = x := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  let χ : (⟨S', x⟩ : Grothendieck Φ) ⟶ ⟨S', G.obj y⟩ :=
    ⟨𝟙 S', eqToHom hid ≫ adj.homEquiv _ _ φf⟩
  have key : (Φ.map φb).toFunctor.map (adj.homEquiv _ _ φf) ≫ adj.counit.app y = φf :=
    (Adjunction.homEquiv_counit adj x y _).symm.trans (Equiv.symm_apply_apply _ _)
  refine ⟨χ, ⟨CategoryTheory.IsHomLift.map (Grothendieck.forget Φ) χ, ?_⟩, ?_⟩
  · refine Grothendieck.ext _ _ (Category.id_comp _) ?_
    dsimp only [χ, Grothendieck.comp_fiber]
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc, key]
    erw [eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · rintro ⟨χb, χf⟩ ⟨hχ, hfac⟩
    change S' ⟶ S' at χb
    change (Φ.map χb).toFunctor.obj x ⟶ G.obj y at χf
    have hχb : χb = 𝟙 S' := (@IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget Φ)
      ⟨S', x⟩ ⟨S', G.obj y⟩ (𝟙 S') _ hχ).symm
    subst hχb
    have h₁ := Grothendieck.congr hfac
    dsimp only [Grothendieck.comp_fiber] at h₁
    have h₂ : (Φ.map φb).toFunctor.map (eqToHom hid.symm ≫ χf) ≫ adj.counit.app y = φf := by
      rw [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc,
        (eqToHom_comp_iff _ _ _).mp h₁]
      erw [eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have h₃ : eqToHom hid.symm ≫ χf = adj.homEquiv x y φf := by
      rw [← h₂, ← Adjunction.homEquiv_counit adj x y, Equiv.apply_symm_apply]
    refine Grothendieck.ext _ _ rfl ?_
    dsimp only [χ]
    rw [← h₃]
    simp

/-- VI.11 b), VI.10: if every `Φ(f)` has a right adjoint, the category `Grothendieck Φ` is also
fibered (the inverse images are the right adjoints), hence bifibered. -/
theorem grothendieck_isFibered_of_isLeftAdjoint
    (h : ∀ {S T : E} (f : S ⟶ T), (Φ.map f).toFunctor.IsLeftAdjoint) :
    IsFibered (Grothendieck.forget Φ) := by
  have : IsPreFibered (Grothendieck.forget Φ) := ⟨fun {a R} f ↦ by
    have := h f
    exact ⟨⟨R, ((Φ.map f).toFunctor.rightAdjoint).obj a.fiber⟩,
      ⟨f, (Adjunction.ofIsLeftAdjoint (Φ.map f).toFunctor).counit.app a.fiber⟩,
      grothendieck_isCartesian_counit Φ f (Adjunction.ofIsLeftAdjoint _) a.fiber⟩⟩
  exact (isFibered_iff_isCofibered _).mpr inferInstance

end Grothendieck

/-! ### Presheaves on variable spaces -/

section Presheaves

open TopCat

variable (C : Type u) [Category.{v} C]

/-- VI.11 b): `X ↦ (Presheaf C X)ᵒᵖ`, `f ↦ (f_*)ᵒᵖ`, a functor `TopCat ⥤ Cat` (direct images of
presheaves compose strictly). -/
def presheafFunctor : TopCat.{w} ⥤ Cat where
  obj X := Cat.of (X.Presheaf C)ᵒᵖ
  map f := (Presheaf.pushforward C f).op.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- VI.11 b): the cofibered category of presheaves with values in `C` on variable spaces. -/
abbrev PresheafCat := Grothendieck (presheafFunctor.{w} C)

/-- VI.11 b): presheaves on variable spaces form a (co-split) cofibered category over the
category of topological spaces. -/
instance presheafCat_isCofibered : IsCofibered (Grothendieck.forget (presheafFunctor.{w} C)) :=
  inferInstance

/-- VI.11 b): when `C` has colimits, inverse images of presheaves exist, so the cofibered
category of presheaves is also fibered (bifibered). -/
theorem presheafCat_isFibered [Limits.HasColimits C] :
    IsFibered (Grothendieck.forget (presheafFunctor.{v} C)) :=
  grothendieck_isFibered_of_isLeftAdjoint _ fun f ↦
    ⟨_, ⟨(Presheaf.pullbackPushforwardAdjunction C f).op⟩⟩

end Presheaves

end SGA.SGA1.ExposeVI
