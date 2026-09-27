/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.PseudofunctorOfCleavage

/-!
# SGA 1, Exposé VI, VI.8 3)–6): the cleavage of the category defined by a pseudofunctor

For a (normalized, possibly non-invertible) pseudofunctor `F : Eᵒᵖ → Cat`, i.e. a strictly
unitary lax functor, the category `LaxCoGrothendieck F` of VI.8 satisfies:

* 3) `h_f(η̄, ξ̄) = Hom(η, f^* ξ) ≃ Hom_f(η̄, ξ̄)` (`LaxCoGrothendieck.homOverEquiv`, for any lax
  functor);
* 4) `i_S : F(S) ⥤ (∫ F)_S` is an isomorphism of categories (`LaxCoGrothendieck.fiberFunctor`);
* 5) the transports `α_f(ξ) = (f, 𝟙) : (T, f^* ξ) ⟶ (S, ξ)` are cartesian and form a normalized
  cleavage (`LaxCoGrothendieck.cleavage`), with `f^*_{∫ F} ∘ i_S = i_T ∘ f^*`;
* 6) its comparisons `c_{f,g}` are the images by `i_U` of those of `F`.

Finally, for a normalized cloven category `𝒳`, the isomorphism `∫ F_𝒳 ≅ 𝒳` of
`PseudofunctorOfCleavage.lean` sends this cleavage to the given one
(`Cleavage.isClovenFunctor_fromLaxCoGrothendieckBased`).
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite Bicategory

variable {E : Type u₁} [Category.{v₁} E]

theorem comp_eqToHom_eqToHom_eqToHom_self {C : Type*} [Category C] {X Y Z W : C} (f : X ⟶ Y)
    (h₁ : Y = Z) (h₂ : Z = W) (h₃ : W = Y) : (f ≫ eqToHom h₁ ≫ eqToHom h₂) ≫ eqToHom h₃ = f := by
  subst h₁ h₂
  simp

/-- `IsCartesian.ext` with explicit hypotheses. -/
theorem isCartesian_ext' {C : Type*} [Category C] {p : C ⥤ E} {R S : E} {f : R ⟶ S} {a b : C}
    (φ : a ⟶ b) (hφ : IsCartesian p f φ) {a' : C} (ψ ψ' : a' ⟶ a) (h₁ : IsHomLift p (𝟙 R) ψ)
    (h₂ : IsHomLift p (𝟙 R) ψ') (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  IsCartesian.ext p f φ ψ ψ' h

namespace LaxCoGrothendieck

section Lax

variable {F : LaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}}

/-- VI.8 3): for `f : T ⟶ S`, `h_f(η̄, ξ̄) = Hom_{F(T)}(η, f^* ξ)` is in bijection with the
`f`-arrows `η̄ ⟶ ξ̄` of the category defined by `F`. -/
def homOverEquiv {T S : E} (f : T ⟶ S) (η : F.obj ⟨op T⟩) (ξ : F.obj ⟨op S⟩) :
    (η ⟶ (laxPullback F f).obj ξ) ≃
      HomOver (forget F) f (⟨T, η⟩ : LaxCoGrothendieck F) ⟨S, ξ⟩ where
  toFun u := ⟨⟨f, u⟩, IsHomLift.map (forget F) (⟨f, u⟩ : (⟨T, η⟩ : LaxCoGrothendieck F) ⟶ ⟨S, ξ⟩)⟩
  invFun φ := φ.val.fiber ≫ eqToHom (by
    have h : φ.val.base = f :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (forget F) ⟨T, η⟩ ⟨S, ξ⟩ f φ.val φ.property).symm
    rw [h])
  left_inv u := by simp
  right_inv φ := by
    have h : φ.val.base = f :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (forget F) ⟨T, η⟩ ⟨S, ξ⟩ f φ.val φ.property).symm
    exact Subtype.ext (Hom.ext _ _ h.symm (by simp))

end Lax

variable {F : StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}}

theorem laxPullback_id_obj {S : E} (ξ : F.obj ⟨op S⟩) :
    (laxPullback F.toLaxFunctor (𝟙 S)).obj ξ = ξ :=
  congrArg (fun G ↦ G.toFunctor.obj ξ) (F.map_id ⟨op S⟩)

theorem laxPullback_id {S : E} : laxPullback F.toLaxFunctor (𝟙 S) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (F.map_id ⟨op S⟩)

theorem laxPullback_id_map {S : E} {ξ ξ' : F.obj ⟨op S⟩} (v : ξ ⟶ ξ') :
    (laxPullback F.toLaxFunctor (𝟙 S)).map v =
      eqToHom (laxPullback_id_obj ξ) ≫ v ≫ eqToHom (laxPullback_id_obj ξ').symm := by
  have := Functor.congr_hom (laxPullback_id (F := F) (S := S)) v
  simpa using this

theorem laxUnit_app {S : E} (ξ : F.obj ⟨op S⟩) :
    (laxUnit F.toLaxFunctor S).app ξ = eqToHom (laxPullback_id_obj ξ).symm := by
  change (F.mapId ⟨op S⟩).toNatTrans.app ξ = _
  rw [F.mapId_eq_eqToHom, Cat.eqToHom_app]
  rfl

/-- For a strictly unitary `F`, `c_{f,𝟙}` is an identification. -/
theorem laxComparison_id_right_app {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (laxComparison F.toLaxFunctor f (𝟙 T)).app ξ = eqToHom (by simp [laxPullback_id_obj]) := by
  have := laxUnit_comparison' F.toLaxFunctor f ξ
  rw [laxUnit_app, eqToHom_comp_iff] at this
  rw [this]
  simp

/-- For a strictly unitary `F`, `c_{𝟙,f}` is an identification. -/
theorem laxComparison_id_left_app {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (laxComparison F.toLaxFunctor (𝟙 S) f).app ξ = eqToHom (by simp [laxPullback_id_obj]) := by
  have := laxUnit_comparison F.toLaxFunctor f ξ
  rw [laxUnit_app, eqToHom_map, eqToHom_comp_iff] at this
  rw [this]
  simp

@[simp] theorem eqToHom_base {X Y : LaxCoGrothendieck F.toLaxFunctor} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg LaxCoGrothendieck.base h) := by
  subst h
  rfl

/-! ### 4): the fibers -/

variable (F) in
/-- VI.8 4): the functor `F(S) ⥤ ∫ F`, `ξ ↦ (S, ξ)`, `u ↦ (𝟙, u)`. -/
abbrev ι (S : E) : F.obj ⟨op S⟩ ⥤ LaxCoGrothendieck F.toLaxFunctor where
  obj ξ := ⟨S, ξ⟩
  map {ξ ξ'} u := ⟨𝟙 S, u ≫ eqToHom (laxPullback_id_obj ξ').symm⟩
  map_id ξ := by
    refine Hom.ext _ _ rfl ?_
    change 𝟙 ξ ≫ eqToHom _ = (laxUnit F.toLaxFunctor S).app ξ ≫ eqToHom rfl
    simp [laxUnit_app]
  map_comp {ξ ξ' ξ''} u v := by
    refine Hom.ext _ _ (Category.id_comp _).symm ?_
    simp only [categoryStruct_comp_fiber]
    rw [laxComparison_id_left_app, Functor.map_comp, laxPullback_id_map]
    simp [eqToHom_map]

@[simp] theorem ι_obj (S : E) (ξ : F.obj ⟨op S⟩) : (ι F S).obj ξ = ⟨S, ξ⟩ := rfl

@[simp] theorem ι_map_base (S : E) {ξ ξ' : F.obj ⟨op S⟩} (u : ξ ⟶ ξ') :
    ((ι F S).map u).base = 𝟙 S := rfl

@[simp] theorem ι_map_fiber (S : E) {ξ ξ' : F.obj ⟨op S⟩} (u : ξ ⟶ ξ') :
    ((ι F S).map u).fiber = u ≫ eqToHom (laxPullback_id_obj ξ').symm := rfl

theorem ι_comp_forget (S : E) :
    ι F S ⋙ forget F.toLaxFunctor = (Functor.const (F.obj ⟨op S⟩)).obj S :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by simp

variable (F) in
/-- VI.8 4): the functor `i_S : F(S) ⥤ (∫ F)_S`. -/
def fiberFunctor (S : E) : F.obj ⟨op S⟩ ⥤ Fiber (forget F.toLaxFunctor) S :=
  Fiber.inducedFunctor (ι_comp_forget S)

@[simp] theorem fiberFunctor_obj_val (S : E) (ξ : F.obj ⟨op S⟩) :
    ((fiberFunctor F S).obj ξ).val = ⟨S, ξ⟩ := rfl

@[simp] theorem fiberFunctor_map_val (S : E) {ξ ξ' : F.obj ⟨op S⟩} (u : ξ ⟶ ξ') :
    ((fiberFunctor F S).map u).val = (ι F S).map u := rfl

theorem Hom.congr_fiber {X Y : LaxCoGrothendieck F.toLaxFunctor} {φ ψ : X ⟶ Y} (h : φ = ψ) :
    φ.fiber = ψ.fiber ≫ eqToHom (by rw [h]) := by
  subst h
  simp

instance (S : E) : (fiberFunctor F S).IsIso where
  faithful := ⟨fun {ξ ξ'} {u v} h ↦ by
    have := Hom.congr_fiber (congrArg Subtype.val h)
    change u ≫ eqToHom _ = (v ≫ eqToHom _) ≫ eqToHom _ at this
    erw [Category.assoc, eqToHom_trans] at this
    exact (cancel_mono _).mp this⟩
  full := ⟨fun {ξ ξ'} φ ↦ by
    have hb : φ.val.base = 𝟙 S :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (forget F.toLaxFunctor) ⟨S, ξ⟩ ⟨S, ξ'⟩ (𝟙 S) φ.val
        φ.property).symm
    refine ⟨φ.val.fiber ≫ eqToHom (by rw [hb]; exact laxPullback_id_obj ξ'), ?_⟩
    apply Subtype.ext
    refine Hom.ext _ _ hb.symm ?_
    change (φ.val.fiber ≫ eqToHom _) ≫ eqToHom _ = _
    erw [Category.assoc, eqToHom_trans]
    rfl⟩
  bijective_obj := by
    constructor
    · intro ξ ξ' h
      obtain ⟨-, h₂⟩ := LaxCoGrothendieck.mk.inj (congrArg Subtype.val h)
      exact eq_of_heq h₂
    · rintro ⟨⟨B, y⟩, h⟩
      change B = S at h
      subst h
      exact ⟨y, rfl⟩

/-- VI.8 4): `i_S : F(S) ≅ (∫ F)_S`, an isomorphism of categories. -/
noncomputable def fiberIso (S : E) : IsoCat (F.obj ⟨op S⟩) (Fiber (forget F.toLaxFunctor) S) :=
  (fiberFunctor F S).asIsomorphism

/-! ### 5), 6): the cleavage -/

theorem eqToHom_fiber {X Y : LaxCoGrothendieck F.toLaxFunctor} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; exact (laxPullback_id_obj _).symm) := by
  subst h
  exact laxUnit_app _

variable (F) in
/-- VI.8 5): the transport `α_f(ξ) = (f, 𝟙) : (T, f^* ξ) ⟶ (S, ξ)`. -/
def transport {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (⟨T, (laxPullback F.toLaxFunctor f).obj ξ⟩ : LaxCoGrothendieck F.toLaxFunctor) ⟶ ⟨S, ξ⟩ :=
  ⟨f, 𝟙 _⟩

instance {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    IsHomLift (forget F.toLaxFunctor) f (transport F f ξ) :=
  IsHomLift.map (forget F.toLaxFunctor) (transport F f ξ)

theorem id_comp_transport {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) {η : F.obj ⟨op T⟩}
    (a : η ⟶ (laxPullback F.toLaxFunctor (𝟙 T)).obj ((laxPullback F.toLaxFunctor f).obj ξ)) :
    (⟨𝟙 T, a⟩ : (⟨T, η⟩ : LaxCoGrothendieck F.toLaxFunctor) ⟶
      ⟨T, (laxPullback F.toLaxFunctor f).obj ξ⟩) ≫ transport F f ξ =
      ⟨f, a ≫ eqToHom (laxPullback_id_obj _)⟩ := by
  refine Hom.ext _ _ (Category.id_comp f) ?_
  simp only [categoryStruct_comp_fiber, transport, CategoryTheory.Functor.map_id,
    laxComparison_id_right_app, Category.id_comp, Category.assoc]
  erw [eqToHom_trans]

/-- VI.8 5): the transports `(f, 𝟙)` are cartesian. -/
instance isCartesian_transport {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    IsCartesian (forget F.toLaxFunctor) f (transport F f ξ) := by
  constructor
  rintro ⟨T', η⟩ ψ hψ
  have hT : T' = T := IsHomLift.domain_eq (forget F.toLaxFunctor) f ψ
  subst hT
  obtain ⟨ψb, ψf⟩ := ψ
  have hb : f = ψb :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (forget F.toLaxFunctor) ⟨T', η⟩ ⟨S, ξ⟩ f _ hψ
  subst hb
  let χ : (⟨T', η⟩ : LaxCoGrothendieck F.toLaxFunctor) ⟶
      ⟨T', (laxPullback F.toLaxFunctor f).obj ξ⟩ :=
    ⟨𝟙 T', ψf ≫ eqToHom (laxPullback_id_obj _).symm⟩
  have hχ : IsHomLift (forget F.toLaxFunctor) (𝟙 T') χ := IsHomLift.map (forget F.toLaxFunctor) χ
  refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
  · rw [id_comp_transport]
    simp
  · rintro ⟨χb, χf⟩ ⟨hχ', hfac⟩
    have hb : 𝟙 T' = χb := IsHomLift.eq_of_isHomLift (p := forget F.toLaxFunctor) (𝟙 T')
      (⟨χb, χf⟩ : (⟨T', η⟩ : LaxCoGrothendieck F.toLaxFunctor) ⟶
        ⟨T', (laxPullback F.toLaxFunctor f).obj ξ⟩)
    subst hb
    rw [id_comp_transport] at hfac
    obtain ⟨-, h₂⟩ := Hom.mk.inj hfac
    have h₃ : χf = ψf ≫ eqToHom (laxPullback_id_obj _).symm := by
      rw [← eq_of_heq h₂]
      simp
    rw [h₃]

/-- Transport of an object of `F(B)` along `B = S`. -/
def fiberCast {B S : E} (h : B = S) (x : F.obj ⟨op B⟩) : F.obj ⟨op S⟩ := h ▸ x

theorem mk_fiberCast {B S : E} (h : B = S) (x : F.obj ⟨op B⟩) :
    (⟨S, fiberCast h x⟩ : LaxCoGrothendieck F.toLaxFunctor) = ⟨B, x⟩ := by
  subst h
  rfl

variable (F) in
/-- VI.8 5): the cleavage of `∫ F` whose transports are the `(f, 𝟙)`. -/
noncomputable def cleavage : Cleavage (forget F.toLaxFunctor) :=
  Cleavage.ofLifts
    (fun {R S} f ξ ↦ (fiberFunctor F R).obj
      ((laxPullback F.toLaxFunctor f).obj (fiberCast ξ.property ξ.val.fiber)))
    (fun f ξ ↦ transport F f (fiberCast ξ.property ξ.val.fiber) ≫
      eqToHom (mk_fiberCast ξ.property ξ.val.fiber))
    (fun {R S} f ξ ↦ by
      have : IsHomLift (forget F.toLaxFunctor) (𝟙 S)
          (eqToIso (mk_fiberCast ξ.property ξ.val.fiber)).hom :=
        IsHomLift.eqToHom_domain_lift_id (mk_fiberCast ξ.property ξ.val.fiber) rfl
      exact IsCartesian.of_comp_iso _ f (transport F f (fiberCast ξ.property ξ.val.fiber))
        (eqToIso (mk_fiberCast ξ.property ξ.val.fiber)))

theorem cleavage_pullback_obj {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    ((cleavage F).pullback f).obj ((fiberFunctor F S).obj ξ) =
      (fiberFunctor F T).obj ((laxPullback F.toLaxFunctor f).obj ξ) := rfl

theorem cleavage_transport {T S : E} (f : T ⟶ S) (ξ : F.obj ⟨op S⟩) :
    (cleavage F).transport f ((fiberFunctor F S).obj ξ) = transport F f ξ := by
  change transport F f ξ ≫ eqToHom _ = transport F f ξ
  simp

theorem transport_id (S : E) (x : F.obj ⟨op S⟩) :
    transport F (𝟙 S) x = eqToHom (by rw [laxPullback_id_obj]) := by
  refine Hom.ext _ _ ?_ ?_
  · rw [eqToHom_base]
    rfl
  · rw [eqToHom_fiber]
    simp only [transport]
    erw [eqToHom_trans, eqToHom_refl]

/-- VI.8 5): the cleavage of `∫ F` is normalized. -/
theorem cleavage_isNormalized : (cleavage F).IsNormalized := by
  rintro S ⟨⟨B, x⟩, h⟩
  change B = S at h
  subst h
  change ∃ h, (cleavage F).transport (𝟙 B) ((fiberFunctor F B).obj x) = eqToHom h
  rw [cleavage_transport, transport_id]
  exact ⟨_, rfl⟩

theorem transport_comp_ι {T S : E} (f : T ⟶ S) {ξ ξ' : F.obj ⟨op S⟩} (u : ξ' ⟶ ξ) :
    transport F f ξ' ≫ (ι F S).map u = (ι F T).map ((laxPullback F.toLaxFunctor f).map u) ≫
      transport F f ξ := by
  erw [id_comp_transport]
  refine Hom.ext _ _ (Category.comp_id f) ?_
  simp only [categoryStruct_comp_fiber, transport, Functor.map_comp,
    eqToHom_map, laxComparison_id_left_app, Category.id_comp, Category.assoc]
  erw [eqToHom_trans, eqToHom_trans, eqToHom_trans]

/-- VI.8 5): `f^*_{∫ F} ∘ i_S = i_T ∘ f^*`. -/
theorem fiberFunctor_comp_pullback {T S : E} (f : T ⟶ S) :
    fiberFunctor F S ⋙ (cleavage F).pullback f =
      laxPullback F.toLaxFunctor f ⋙ fiberFunctor F T := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun ξ' ξ u ↦ ?_
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Subtype.ext
  change (((cleavage F).pullback f).map ((fiberFunctor F S).map u)).val =
    (ι F T).map ((laxPullback F.toLaxFunctor f).map u)
  refine isCartesian_ext' _ ((cleavage F).transport_isCartesian f ((fiberFunctor F S).obj ξ))
    _ _ (((cleavage F).pullback f).map ((fiberFunctor F S).map u)).property
    (IsHomLift.map (forget F.toLaxFunctor) ((ι F T).map ((laxPullback F.toLaxFunctor f).map u)))
    ?_
  have e₁ : (cleavage F).transport f ((fiberFunctor F S).obj ξ) = transport F f ξ :=
    cleavage_transport f ξ
  have e₂ : (cleavage F).transport f ((fiberFunctor F S).obj ξ') = transport F f ξ' :=
    cleavage_transport f ξ'
  rw [Cleavage.transport_naturality, e₁, e₂]
  exact transport_comp_ι f u

/-- VI.8 6): the comparisons `c_{f,g}` of the cleavage of `∫ F` are the images by `i_U` of those of
`F`. -/
theorem cleavage_comparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : F.obj ⟨op S⟩) :
    (cleavage F).comparison f g ((fiberFunctor F S).obj ξ) =
      (fiberFunctor F U).map ((laxComparison F.toLaxFunctor f g).app ξ) := by
  have : IsHomLift (forget F.toLaxFunctor) (𝟙 U)
      ((fiberFunctor F U).map ((laxComparison F.toLaxFunctor f g).app ξ)).val :=
    ((fiberFunctor F U).map ((laxComparison F.toLaxFunctor f g).app ξ)).property
  have e₁ : (cleavage F).transport g (((cleavage F).pullback f).obj ((fiberFunctor F S).obj ξ)) =
      transport F g ((laxPullback F.toLaxFunctor f).obj ξ) :=
    cleavage_transport g _
  have key : ((cleavage F).comparison f g ((fiberFunctor F S).obj ξ)).val ≫
      (cleavage F).transport (g ≫ f) ((fiberFunctor F S).obj ξ) =
      ((fiberFunctor F U).map ((laxComparison F.toLaxFunctor f g).app ξ)).val ≫
        (cleavage F).transport (g ≫ f) ((fiberFunctor F S).obj ξ) := by
    rw [Cleavage.comparison_fac, e₁, cleavage_transport, cleavage_transport, fiberFunctor_map_val]
    erw [id_comp_transport]
    refine Hom.ext _ _ rfl ?_
    change 𝟙 _ ≫ (laxPullback F.toLaxFunctor g).map (𝟙 _) ≫
      (laxComparison F.toLaxFunctor f g).app ξ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
    exact (comp_eqToHom_eqToHom_eqToHom_self ((laxComparison F.toLaxFunctor f g).app ξ) _ _ _).symm
  exact Subtype.ext (isCartesian_ext' ((cleavage F).transport (g ≫ f) ((fiberFunctor F S).obj ξ))
    ((cleavage F).transport_isCartesian (g ≫ f) _) _ _
    ((cleavage F).comparison f g ((fiberFunctor F S).obj ξ)).property this key)

end LaxCoGrothendieck

/-! ### Compatibility with the given cleavage -/

namespace Cleavage

variable {C : Type u₂} [Category.{v₂} C] {p : C ⥤ E} {K : Cleavage p}

/-- End of VI.8: for a normalized cloven category `𝒳`, the isomorphism `∫ F_𝒳 ≅ 𝒳` sends the
transports `(f, 𝟙)` of `∫ F_𝒳` to the transports `α_f` of `𝒳`: it is an isomorphism of cloven
categories. -/
theorem IsNormalized.isClovenFunctor_fromLaxCoGrothendieckBased (hK : K.IsNormalized) :
    IsClovenFunctor (LaxCoGrothendieck.cleavage hK.strictlyUnitaryLaxFunctor) K
      K.fromLaxCoGrothendieckBased := by
  rintro R S f ⟨⟨B, x⟩, h⟩
  change B = S at h
  subst h
  change Fiber p B at x
  refine ⟨rfl, ?_⟩
  change K.fromLaxCoGrothendieck.map ((LaxCoGrothendieck.cleavage
    hK.strictlyUnitaryLaxFunctor).transport f
      ((LaxCoGrothendieck.fiberFunctor hK.strictlyUnitaryLaxFunctor B).obj x)) = _
  rw [LaxCoGrothendieck.cleavage_transport]
  change Subtype.val (𝟙 ((K.pullback f).obj x)) ≫ K.transport f x =
    eqToHom rfl ≫ K.transport f x
  simp

end Cleavage

end SGA.SGA1.ExposeVI
