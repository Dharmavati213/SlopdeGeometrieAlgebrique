/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Presheaves
import SGA.SGA1.ExposeVI.Products
import SGA.SGA1.ExposeVI.Split
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# SGA 1, Exposé VI, VI.11 b): sheaves on variable spaces and `Cat_{//𝒞}`

* Sheaves: `X ↦ Sh(X, 𝒞)ᵒᵖ`, `f ↦ (f_*)ᵒᵖ` is a functor `Top ⥤ Cat` (direct images of sheaves
  compose strictly), hence defines a co-split cofibered category `SheafCat 𝒞` over `Top`
  (`presheafCat_isCofibered` is the presheaf version), with a `Top`-functor
  `sheafCatInclusion : SheafCat 𝒞 ⥤ PresheafCat 𝒞` induced by the inclusion of sheaves into
  presheaves; it is fully faithful and sends cocartesian arrows to cocartesian arrows
  (`sheafCatInclusion_isCocartesian`: sheaves form a cofibered subcategory of presheaves; in
  general, `Grothendieck.map α` preserves cocartesian arrows, `grothendieckMap_isCocartesian`).
  That it is not a fibered subcategory (the inverse image of a sheaf as a presheaf is in general
  not a sheaf) is not formalized.
* Direct images in split categories (VI.10): if `f^* = Φ(f)` has a left adjoint `f_!`, the arrow
  `(f, η) : (T, b) ⟶ (S, f_! b)` is cocartesian (`SplitFibered.isCocartesian_unit`), so a split
  category whose inverse images have left adjoints is cofibered
  (`SplitFibered.isCofibered_of_isRightAdjoint`).
* `Cat_{//𝒞}`: `𝒰 ↦ Hom(𝒰, 𝒞)`, contravariant in `𝒰`, defines a split fibered category
  `CatOverOver 𝒞` over `Cat`, whose objects are pairs `(𝒰, p : 𝒰 ⥤ 𝒞)` and whose arrows
  `(𝒰, p) ⟶ (𝒱, q)` are pairs `(f, u : p ⟶ f ⋙ q)` (`CatOverOver.homEquiv`); its fiber at `𝒰` is
  `Hom(𝒰, 𝒞)`. When `𝒞` has inductive limits it is also cofibered (`catOverOver_isCofibered`),
  the direct image of `p` by `f` being the left Kan extension of `p` along `f`. The deduction of
  the category of presheaves by the change of base `Topᵒᵖ ⥤ Cat` is not formalized.
-/

universe w v u v₁ u₁ v₂ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

/-! ### Functoriality of the Grothendieck construction -/

section GrothendieckMap

theorem eq_of_eqToHom_comp_eq {D : Type*} [Category D] {a b c : D} (h h' : a = b) (x y : b ⟶ c)
    (H : eqToHom h ≫ x = eqToHom h' ≫ y) : x = y := by
  subst h
  simpa using H

theorem eqToHom_comp_eqToHom_comp_eqToHom_comp {D : Type*} [Category D] {a b c d : D}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = a) (x : a ⟶ d) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ ≫ x = x := by
  subst h₁ h₂
  simp

variable {E : Type u₁} [Category.{v₁} E] {F G : E ⥤ Cat.{v₂, u₂}} (α : F ⟶ G)

/-- The functor between Grothendieck constructions induced by a natural transformation with
faithful components is faithful. -/
theorem grothendieckMap_faithful [∀ X, (α.app X).toFunctor.Faithful] :
    (Grothendieck.map α).Faithful where
  map_injective {X Y} {f g} h := by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    have hb : fb = gb := congrArg Grothendieck.Hom.base h
    subst hb
    have h' : (⟨fb, (eqToHom (α.naturality fb).symm).toNatTrans.app X.fiber ≫
        (α.app Y.base).toFunctor.map ff⟩ :
          Grothendieck.Hom ((Grothendieck.map α).obj X) ((Grothendieck.map α).obj Y)) =
        ⟨fb, (eqToHom (α.naturality fb).symm).toNatTrans.app X.fiber ≫
          (α.app Y.base).toFunctor.map gf⟩ := h
    have h₂ := eq_of_heq (Grothendieck.Hom.mk.inj h').2
    rw [Cat.eqToHom_app] at h₂
    obtain rfl := (α.app Y.base).toFunctor.map_injective (eq_of_eqToHom_comp_eq _ _ _ _ h₂)
    rfl

/-- The functor between Grothendieck constructions induced by a natural transformation with
full components is full. -/
theorem grothendieckMap_full [∀ X, (α.app X).toFunctor.Full] : (Grothendieck.map α).Full where
  map_surjective {X Y} m := by
    have e : (α.app Y.base).toFunctor.obj ((F.map m.base).toFunctor.obj X.fiber) =
        (G.map m.base).toFunctor.obj ((α.app X.base).toFunctor.obj X.fiber) :=
      Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality m.base)) X.fiber
    refine ⟨⟨m.base, (α.app Y.base).toFunctor.preimage (eqToHom e ≫ m.fiber)⟩, ?_⟩
    refine Grothendieck.ext _ _ rfl ?_
    change eqToHom _ ≫ (eqToHom (α.naturality m.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map ((α.app Y.base).toFunctor.preimage (eqToHom e ≫ m.fiber)) = _
    erw [Functor.map_preimage, Cat.eqToHom_app]
    exact eqToHom_comp_eqToHom_comp_eqToHom_comp _ _ _ _

/-- A functor over `E` from a category over `E` in which every arrow has, at every object, a
cocartesian lift sent to a cocartesian arrow, sends all cocartesian arrows to cocartesian arrows. -/
theorem isCocartesian_map_of_forall_exists {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u}
    [Category.{v} 𝒴] {q : 𝒴 ⥤ E} (Φ : 𝒳 ⥤ 𝒴)
    (h : ∀ (a : 𝒳) {S : E} (f : (Φ ⋙ q).obj a ⟶ S), ∃ (b : 𝒳) (ψ : a ⟶ b),
      IsCocartesian (Φ ⋙ q) f ψ ∧ IsCocartesian q f (Φ.map ψ))
    {R S : E} (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [IsCocartesian (Φ ⋙ q) f φ] :
    IsCocartesian q f (Φ.map φ) := by
  obtain rfl := IsHomLift.domain_eq (Φ ⋙ q) f φ
  obtain rfl := IsHomLift.codomain_eq (Φ ⋙ q) f φ
  obtain ⟨b', ψ, hψ, hΦψ⟩ := h a f
  let e := IsCocartesian.codomainUniqueUpToIso (Φ ⋙ q) f ψ φ
  have : IsHomLift (Φ ⋙ q) (𝟙 _) e.hom := IsCocartesian.map_isHomLift (Φ ⋙ q) f ψ φ
  have hfac : ψ ≫ e.hom = φ := IsCocartesian.fac (Φ ⋙ q) f ψ φ
  have : IsHomLift q (𝟙 ((Φ ⋙ q).obj b)) (Φ.mapIso e).hom :=
    (isHomLift_comp_iff Φ q (𝟙 _) e.hom).mp inferInstance
  rw [← hfac, Φ.map_comp]
  exact IsCocartesian.of_comp_iso q f (Φ.map ψ) (Φ.mapIso e)

/-- `Grothendieck.map α` sends the transport `(f, 𝟙)` to the transport `(f, 𝟙)` (up to the
identification `α_T f_* = f_* α_S`). -/
theorem grothendieckMap_map_transport (X : Grothendieck F) {T : E} (f : X.base ⟶ T) :
    (Grothendieck.map α).map (grothendieckTransport F X f) =
      grothendieckTransport G ((Grothendieck.map α).obj X) f ≫
        eqToHom (congrArg (fun y ↦ (⟨T, y⟩ : Grothendieck G))
          (Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality f)) X.fiber).symm) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [grothendieckTransport, Grothendieck.comp_base, Grothendieck.base_eqToHom,
      eqToHom_refl]
    exact (Category.comp_id f).symm
  · simp only [Cat.Hom.comp_toFunctor, comp_obj, grothendieckTransport, Grothendieck.comp_base,
      Grothendieck.map_map_fiber, map_id, Category.comp_id, Grothendieck.comp_fiber,
      Grothendieck.fiber_eqToHom, Category.id_comp]
    exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm

/-- VI.11 b): `Grothendieck.map α` sends cocartesian arrows to cocartesian arrows. -/
theorem grothendieckMap_isCocartesian {R S : E} (f : R ⟶ S) {a b : Grothendieck F} (φ : a ⟶ b)
    [IsCocartesian (Grothendieck.forget F) f φ] :
    IsCocartesian (Grothendieck.forget G) f ((Grothendieck.map α).map φ) := by
  have : IsCocartesian (Grothendieck.map α ⋙ Grothendieck.forget G) f φ :=
    ‹IsCocartesian (Grothendieck.forget F) f φ›
  refine isCocartesian_map_of_forall_exists (Grothendieck.map α) (fun X T g ↦ ?_) f φ
  change X.base ⟶ T at g
  have := grothendieckTransport_isStronglyCocartesian F X g
  have : IsStronglyCocartesian (Grothendieck.forget G) (R := X.base) g
      (grothendieckTransport G ((Grothendieck.map α).obj X) g) :=
    grothendieckTransport_isStronglyCocartesian G ((Grothendieck.map α).obj X) g
  have hobj : (⟨T, (G.map g).toFunctor.obj ((Grothendieck.map α).obj X).fiber⟩ :
      Grothendieck G) = ⟨T, (α.app T).toFunctor.obj ((F.map g).toFunctor.obj X.fiber)⟩ :=
    congrArg (fun y ↦ (⟨T, y⟩ : Grothendieck G))
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor (α.naturality g)) X.fiber).symm
  have hlift : IsHomLift (Grothendieck.forget G) (𝟙 T) (eqToIso hobj).hom :=
    IsHomLift.eqToHom_domain_lift_id hobj rfl
  refine ⟨_, grothendieckTransport F X g,
    (inferInstance : IsCocartesian (Grothendieck.forget F) g _), ?_⟩
  rw [grothendieckMap_map_transport, ← eqToIso.hom]
  exact @Functor.IsCocartesian.of_comp_iso _ _ _ _ (Grothendieck.forget G) _ _ _ _ g
    (grothendieckTransport G ((Grothendieck.map α).obj X) g) inferInstance _ (eqToIso hobj) hlift

end GrothendieckMap

/-! ### Sheaves on variable spaces -/

section Sheaves

open TopCat

variable (C : Type u) [Category.{v} C]

/-- VI.11 b): `X ↦ (Sh(X, 𝒞))ᵒᵖ`, `f ↦ (f_*)ᵒᵖ`, a functor `Top ⥤ Cat`. -/
noncomputable def sheafFunctor : TopCat.{w} ⥤ Cat where
  obj X := Cat.of (X.Sheaf C)ᵒᵖ
  map f := (Sheaf.pushforward C f).op.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- VI.11 b): the cofibered category of sheaves with values in `𝒞` on variable spaces. -/
abbrev SheafCat := Grothendieck (sheafFunctor.{w} C)

/-- VI.11 b): sheaves on variable spaces form a (co-split) cofibered category over `Top`. -/
instance sheafCat_isCofibered : IsCofibered (Grothendieck.forget (sheafFunctor.{w} C)) :=
  inferInstance

/-- The inclusion of sheaves into presheaves, compatibly with direct images. -/
noncomputable def sheafToPresheafNatTrans : sheafFunctor.{w} C ⟶ presheafFunctor.{w} C where
  app X := (Sheaf.forget C X).op.toCatHom
  naturality _ _ _ := rfl

/-- VI.11 b): the inclusion of the cofibered category of sheaves into that of presheaves, a
functor over `Top`. -/
noncomputable def sheafCatInclusion : SheafCat.{w} C ⥤ PresheafCat.{w} C :=
  Grothendieck.map (sheafToPresheafNatTrans C)

theorem sheafCatInclusion_comp_forget :
    sheafCatInclusion.{w} C ⋙ Grothendieck.forget _ = Grothendieck.forget _ :=
  Grothendieck.functor_comp_forget

instance (X : TopCat.{w}) : ((sheafToPresheafNatTrans C).app X).toFunctor.Faithful :=
  inferInstanceAs (Sheaf.forget C X).op.Faithful

instance (X : TopCat.{w}) : ((sheafToPresheafNatTrans C).app X).toFunctor.Full :=
  inferInstanceAs (Sheaf.forget C X).op.Full

/-- VI.11 b): the inclusion of sheaves into presheaves on variable spaces is faithful. -/
instance : (sheafCatInclusion.{w} C).Faithful := grothendieckMap_faithful _

/-- VI.11 b): the inclusion of sheaves into presheaves on variable spaces is full (so, with the
previous instance, fully faithful). -/
instance : (sheafCatInclusion.{w} C).Full := grothendieckMap_full _

/-- VI.11 b): the inclusion of sheaves into presheaves sends cocartesian arrows to cocartesian
arrows: sheaves on variable spaces form a cofibered subcategory of presheaves. -/
theorem sheafCatInclusion_isCocartesian {R S : TopCat.{w}} (f : R ⟶ S) {a b : SheafCat.{w} C}
    (φ : a ⟶ b) [IsCocartesian (Grothendieck.forget (sheafFunctor.{w} C)) f φ] :
    IsCocartesian (Grothendieck.forget (presheafFunctor.{w} C)) f
      ((sheafCatInclusion.{w} C).map φ) :=
  grothendieckMap_isCocartesian _ f φ

end Sheaves

/-! ### Direct images in a split category -/

section SplitDirectImage

open Pseudofunctor

variable {E : Type u₁} [Category.{v₁} E] (Φ : Eᵒᵖ ⥤ Cat.{v₂, u₂})

theorem eqToHom_comp_eqToHom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (h : F = G) (y : C) {z : D} (p : z = F.obj y) (q : z = G.obj y) :
    eqToHom p ≫ (eqToHom h).app y = eqToHom q := by
  subst h
  simp

theorem comp_map_comp_eqToHom {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {b : D}
    {a y y' : C} (u : b ⟶ G.obj a) (v : a ⟶ y) (e : y = y') {w : D} (X : G.obj y' ⟶ w)
    (Y : G.obj y ⟶ w) (hXY : eqToHom (congrArg G.obj e) ≫ X = Y) :
    u ≫ G.map (v ≫ eqToHom e) ≫ X = (u ≫ G.map v) ≫ Y := by
  subst e hXY
  simp

theorem self_eq_comp_eqToHom_comp_eqToHom_comp_eqToHom {C : Type*} [Category C] {X Y Z W : C}
    (f : X ⟶ Y) (h₁ : Y = Z) (h₂ : Z = W) (h₃ : W = Y) :
    f = ((f ≫ eqToHom h₁) ≫ eqToHom h₂) ≫ eqToHom h₃ := by
  subst h₁ h₂
  simp

theorem SplitFibered.obj_map_id {S : E} (y : Φ.obj (op S)) :
    y = (Φ.map (𝟙 S).op).toFunctor.obj y := by
  rw [op_id, Φ.map_id]
  rfl

/-- The vertical arrow `(𝟙, v) : (S, a) ⟶ (S, y)` of a split category defined by `v : a ⟶ y`. -/
def SplitFibered.vert {S : E} {a y : Φ.obj (op S)} (v : a ⟶ y) :
    (⟨S, a⟩ : SplitFibered Φ) ⟶ ⟨S, y⟩ :=
  ⟨𝟙 S, v ≫ eqToHom (SplitFibered.obj_map_id Φ y)⟩

theorem SplitFibered.comp_vert {T S : E} (f : T ⟶ S) {b : Φ.obj (op T)} {a y : Φ.obj (op S)}
    (u : b ⟶ (Φ.map f.op).toFunctor.obj a) (v : a ⟶ y) :
    (⟨f, u⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, a⟩) ≫ SplitFibered.vert Φ v =
      ⟨f, u ≫ (Φ.map f.op).toFunctor.map v⟩ := by
  refine CoGrothendieck.Hom.ext _ _ (Category.comp_id f) ?_
  simp only [CoGrothendieck.categoryStruct_comp_fiber, SplitFibered.vert,
    Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans]
  exact comp_map_comp_eqToHom _ u v _ _ _ (eqToHom_comp_eqToHom_app
    (F := (Φ.toPseudofunctor'.map (𝟙 S).op.toLoc ≫ Φ.toPseudofunctor'.map f.op.toLoc).toFunctor)
    _ _ _ _)

/-- VI.10: in the split category defined by `Φ : Eᵒᵖ ⥤ Cat`, if the inverse image functor
`f^* = Φ(f)` has a left adjoint `f_!`, then `(f, η_b) : (T, b) ⟶ (S, f_! b)` (with `η` the unit)
is cocartesian: `f_!` is a direct image functor. -/
theorem SplitFibered.isCocartesian_unit {T S : E} (f : T ⟶ S) {L : Φ.obj (op T) ⥤ Φ.obj (op S)}
    (adj : L ⊣ (Φ.map f.op).toFunctor) (b : Φ.obj (op T)) :
    IsCocartesian (SplitFibered.forget Φ) f
      (⟨f, adj.unit.app b⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, L.obj b⟩) := by
  have : IsHomLift (SplitFibered.forget Φ) f
      (⟨f, adj.unit.app b⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, L.obj b⟩) :=
    CategoryTheory.IsHomLift.map (SplitFibered.forget Φ)
      (⟨f, adj.unit.app b⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, L.obj b⟩)
  refine ⟨fun {b'} φ' hφ' ↦ ?_⟩
  obtain ⟨S', y⟩ := b'
  obtain rfl : S = S' := (IsHomLift.codomain_eq (SplitFibered.forget Φ) f φ').symm
  obtain ⟨φb, w⟩ := φ'
  obtain rfl : f = φb := @IsHomLift.eq_of_isHomLift _ _ _ _ (SplitFibered.forget Φ) ⟨T, b⟩
    ⟨S, y⟩ f ⟨φb, w⟩ hφ'
  change b ⟶ (Φ.map f.op).toFunctor.obj y at w
  have hvert : ∀ v : L.obj b ⟶ y,
      (⟨f, adj.unit.app b⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, L.obj b⟩) ≫
        SplitFibered.vert Φ v = ⟨f, adj.homEquiv b y v⟩ := fun v ↦
    (SplitFibered.comp_vert Φ f (adj.unit.app b) v).trans
      (congrArg (fun u ↦ (⟨f, u⟩ : (⟨T, b⟩ : SplitFibered Φ) ⟶ ⟨S, y⟩))
        (adj.homEquiv_unit b y v).symm)
  refine ⟨SplitFibered.vert Φ ((adj.homEquiv b y).symm w),
    ⟨CategoryTheory.IsHomLift.map (SplitFibered.forget Φ)
      (SplitFibered.vert Φ ((adj.homEquiv b y).symm w)), ?_⟩, ?_⟩
  · rw [hvert, Equiv.apply_symm_apply]
  · rintro ⟨χb, χf⟩ ⟨hχ', hfac⟩
    obtain rfl : χb = 𝟙 S := (@IsHomLift.eq_of_isHomLift _ _ _ _ (SplitFibered.forget Φ)
      ⟨S, L.obj b⟩ ⟨S, y⟩ (𝟙 S) ⟨χb, χf⟩ hχ').symm
    change L.obj b ⟶ (Φ.map (𝟙 S).op).toFunctor.obj y at χf
    have hχ : (⟨𝟙 S, χf⟩ : (⟨S, L.obj b⟩ : SplitFibered Φ) ⟶ ⟨S, y⟩) =
        SplitFibered.vert Φ (χf ≫ eqToHom (SplitFibered.obj_map_id Φ y).symm) := by
      refine CoGrothendieck.Hom.ext _ _ rfl ?_
      exact self_eq_comp_eqToHom_comp_eqToHom_comp_eqToHom _ _ _ _
    rw [hχ] at hfac ⊢
    rw [hvert] at hfac
    have hv := CoGrothendieck.Hom.congr hfac
    simp only [eqToHom_refl] at hv
    exact congrArg (SplitFibered.vert Φ)
      ((Equiv.eq_symm_apply _).mpr (hv.trans (Category.comp_id w)))

/-- VI.10: a split category whose inverse image functors `f^*` all have left adjoints is also
cofibered (VI.10.1), the direct images being the left adjoints. -/
theorem SplitFibered.isCofibered_of_isRightAdjoint
    (h : ∀ {T S : E} (f : T ⟶ S), (Φ.map f.op).toFunctor.IsRightAdjoint) :
    IsCofibered (SplitFibered.forget Φ) := by
  have : IsPreCofibered (SplitFibered.forget Φ) := ⟨fun {a} S f ↦ by
    have := h f
    exact ⟨_, _, SplitFibered.isCocartesian_unit Φ f
      (Adjunction.ofIsRightAdjoint (Φ.map f.op).toFunctor) a.fiber⟩⟩
  exact (isFibered_iff_isCofibered _).mp inferInstance

end SplitDirectImage

/-! ### `Cat_{//𝒞}` -/

section CatOverOver

variable (D : Type u₂) [Category.{v₂} D]

/-- VI.11 b): `𝒰 ↦ Hom(𝒰, 𝒞)`, a contravariant functor from `Cat` to `Cat` (by composition). -/
def functorCategoryFunctor : Cat.{v, u}ᵒᵖ ⥤ Cat.{max u v₂, max u v v₂ u₂} where
  obj U := Cat.of (U.unop ⥤ D)
  map f := ((Functor.whiskeringLeft _ _ D).obj f.unop.toFunctor).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

-- intended to be used with explicit universe parameters, like `Cat`
set_option linter.checkUnivs false in
/-- VI.11 b): SGA's `Cat_{//𝒞}`, the split fibered category over `Cat` defined by
`𝒰 ↦ Hom(𝒰, 𝒞)`; its objects are the pairs `(𝒰, p : 𝒰 ⥤ 𝒞)`. -/
abbrev CatOverOver := SplitFibered (functorCategoryFunctor.{v, u} D)

/-- VI.11 b): `Cat_{//𝒞}` is (split) fibered over `Cat`. -/
instance catOverOver_isFibered :
    IsFibered (SplitFibered.forget (functorCategoryFunctor.{v, u} D)) :=
  inferInstance

/-- VI.11 b): when inductive limits exist in `𝒞`, `Cat_{//𝒞}` is also cofibered over `Cat`: the
direct image of `p : 𝒰 ⥤ 𝒞` by `f : 𝒰 ⥤ 𝒱` is the left Kan extension of `p` along `f`. -/
instance catOverOver_isCofibered [Limits.HasColimitsOfSize.{v, max u v} D] :
    IsCofibered (SplitFibered.forget (functorCategoryFunctor.{v, u} D)) :=
  SplitFibered.isCofibered_of_isRightAdjoint _ fun {U V} f ↦
    (⟨_, ⟨f.toFunctor.lanAdjunction D⟩⟩ :
      ((Functor.whiskeringLeft U V D).obj f.toFunctor).IsRightAdjoint)

namespace CatOverOver

variable {D}

/-- An object `(𝒰, p)` of `Cat_{//𝒞}`. -/
abbrev mk (U : Cat.{v, u}) (P : U ⥤ D) : CatOverOver.{v, u} D := ⟨U, P⟩

/-- VI.11 b): an arrow `(𝒰, p) ⟶ (𝒱, q)` of `Cat_{//𝒞}` is a pair `(f, u)` of a functor
`f : 𝒰 ⥤ 𝒱` and a homomorphism of functors `u : p ⟶ f ⋙ q`. -/
def homEquiv {U V : Cat.{v, u}} (P : U ⥤ D) (Q : V ⥤ D) :
    (mk U P ⟶ mk V Q) ≃ Σ f : U ⟶ V, (P ⟶ f.toFunctor ⋙ Q) where
  toFun φ := ⟨φ.base, φ.fiber⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- VI.11 b): the fiber of `Cat_{//𝒞}` at `𝒰` is equivalent to `Hom(𝒰, 𝒞)`. -/
noncomputable def fiberEquiv (U : Cat.{v, u}) :
    (U ⥤ D) ≌ Fiber (SplitFibered.forget (functorCategoryFunctor.{v, u} D)) U :=
  SplitFibered.fiberEquiv (functorCategoryFunctor.{v, u} D) U

end CatOverOver

end CatOverOver

end SGA.SGA1.ExposeVI
