/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import SGA.Foundations.QuasiCoherent.Glue

/-!
# Descent of modules along morphisms of schemes

Let `g : S' ⟶ S` be a morphism of schemes and `D` a descent datum for modules relative to `g`
(for the pseudofunctor `X ↦ X.Modules` of inverse images), with underlying module `E` on `S'`.
We construct the descended module `descentModule D` on `S`: its sections over `W` are the
sections `s` of `E` over `g⁻¹ W` compatible with the descent datum, i.e. such that for all
`f₁, f₂ : Y ⟶ S'` with `f₁ ≫ g = f₂ ≫ g` the descent isomorphism `f₁^* E ≅ f₂^* E` maps
`f₁^* s` to `f₂^* s` (`IsDescentSection`). It comes with a morphism of descent data
`descentCounitHom D : g^* (descentModule D) ⟶ D` (Stacks, Tag 023T and its proof).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The pseudofunctor `X ↦ X.Modules` with the inverse image functors, to `Cat`. -/
noncomputable abbrev pseudofunctorCat : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

set_option backward.isDefEq.respectTransparency false in
lemma pseudofunctorCat_mapComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (h : f ≫ g = q) (N : Z.Modules) :
    (pseudofunctorCat.mapComp' g.op.toLoc f.op.toLoc q.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app N = (pullbackCompIso' f g q h N).hom := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackCompIso']
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma pseudofunctorCat_mapComp'_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (h : f ≫ g = q) (N : Z.Modules) :
    (pseudofunctorCat.mapComp' g.op.toLoc f.op.toLoc q.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app N = (pullbackCompIso' f g q h N).inv := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackCompIso']
  rfl

lemma iso_hom_app_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (y : Γ(N, U)) : e.hom.app U (e.inv.app U y) = y :=
  iso_inv_app_hom_app e.symm U y

section Descent

variable {S S' : Scheme.{u}} {g : S' ⟶ S}
  (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- The module underlying a descent datum relative to `g : S' ⟶ S`. -/
noncomputable def descentObj : S'.Modules := D.obj ()

/-- The morphism `f₁^* E ⟶ f₂^* E` of a descent datum `E` relative to `g`, for
`f₁ ≫ g = f₂ ≫ g`. -/
noncomputable def descentHom {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    (Scheme.Modules.pullback f₁).obj (descentObj D) ⟶
      (Scheme.Modules.pullback f₂).obj (descentObj D) :=
  D.hom (f₁ ≫ g) (i₁ := ()) (i₂ := ()) f₁ f₂ rfl h.symm

lemma hom_eq_descentHom {Y : Scheme.{u}} (q : Y ⟶ S) (f₁ f₂ : Y ⟶ S') (h₁ : f₁ ≫ g = q)
    (h₂ : f₂ ≫ g = q) :
    D.hom q (i₁ := ()) (i₂ := ()) f₁ f₂ h₁ h₂ = descentHom D f₁ f₂ (h₁.trans h₂.symm) := by
  subst h₁; rfl

lemma descentHom_self {Y : Scheme.{u}} (f : Y ⟶ S') : descentHom D f f rfl = 𝟙 _ :=
  D.hom_self _ _ rfl

lemma descentHom_comp {Y : Scheme.{u}} (f₁ f₂ f₃ : Y ⟶ S') (h₁₂ : f₁ ≫ g = f₂ ≫ g)
    (h₂₃ : f₂ ≫ g = f₃ ≫ g) :
    descentHom D f₁ f₂ h₁₂ ≫ descentHom D f₂ f₃ h₂₃ = descentHom D f₁ f₃ (h₁₂.trans h₂₃) := by
  have := D.hom_comp (f₁ ≫ g) (i₁ := ()) (i₂ := ()) (i₃ := ()) f₁ f₂ f₃ rfl h₁₂.symm
    (h₁₂.trans h₂₃).symm
  rw [hom_eq_descentHom D (f₁ ≫ g) f₂ f₃ h₁₂.symm (h₁₂.trans h₂₃).symm] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
lemma descentHom_pull {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) (f₁ f₂ : Y ⟶ S')
    (h : f₁ ≫ g = f₂ ≫ g) (h' : (u ≫ f₁) ≫ g = (u ≫ f₂) ≫ g) :
    (pullbackCompIso' u f₁ (u ≫ f₁) rfl (descentObj D)).hom ≫
      (Scheme.Modules.pullback u).map (descentHom D f₁ f₂ h) ≫
      (pullbackCompIso' u f₂ (u ≫ f₂) rfl (descentObj D)).inv =
      descentHom D (u ≫ f₁) (u ≫ f₂) h' := by
  have := D.pullHom_hom u (f₁ ≫ g) (u ≫ f₁ ≫ g) rfl (i₁ := ()) (i₂ := ()) f₁ f₂ rfl h.symm
    (u ≫ f₁) (u ≫ f₂) rfl rfl
  rw [hom_eq_descentHom D (u ≫ f₁ ≫ g) (u ≫ f₁) (u ≫ f₂) (Category.assoc _ _ _)] at this
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at this
  rw [pseudofunctorCat_mapComp'_hom_app u f₁ (u ≫ f₁) rfl,
    pseudofunctorCat_mapComp'_inv_app u f₂ (u ≫ f₂) rfl] at this
  exact this


lemma descentHom_pullbackTop {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) (f₁ f₂ : Y ⟶ S')
    (h : f₁ ≫ g = f₂ ≫ g) (w₁ w₂ : Y' ⟶ S') (hw₁ : u ≫ f₁ = w₁) (hw₂ : u ≫ f₂ = w₂)
    (h' : w₁ ≫ g = w₂ ≫ g) (z : Γ((Scheme.Modules.pullback f₁).obj (descentObj D), ⊤)) :
    pullbackTop u f₂ w₂ hw₂ _ ((descentHom D f₁ f₂ h).app ⊤ z) =
      (descentHom D w₁ w₂ h').app ⊤ (pullbackTop u f₁ w₁ hw₁ _ z) := by
  subst hw₁ hw₂
  have e : pullbackApp u _ ⊤ ((descentHom D f₁ f₂ h).app ⊤ z) =
      ((Scheme.Modules.pullback u).map (descentHom D f₁ f₂ h)).app ⊤ (pullbackApp u _ ⊤ z) :=
    pullbackApp_naturality u (descentHom D f₁ f₂ h) ⊤ z
  have e' := congr(Hom.app $(descentHom_pull D u f₁ f₂ h h') ⊤
    ((pullbackCompIso' u f₁ (u ≫ f₁) rfl (descentObj D)).inv.app ⊤ (pullbackApp u _ ⊤ z)))
  have e3 : (pullbackCompIso' u f₁ (u ≫ f₁) rfl (descentObj D)).hom.app ⊤
      ((pullbackCompIso' u f₁ (u ≫ f₁) rfl (descentObj D)).inv.app ⊤ (pullbackApp u _ ⊤ z)) =
      pullbackApp u _ ⊤ z := iso_hom_app_inv_app _ ⊤ _
  rw [Hom.comp_app_apply, Hom.comp_app_apply, e3] at e'
  rw [pullbackTop_apply, pullbackTop_apply, e]
  exact e'


lemma preimage_le_of_comp_eq {Y : Scheme.{u}} {f₁ f₂ : Y ⟶ S'} (h : f₁ ≫ g = f₂ ≫ g)
    (W : S.Opens) : f₁ ⁻¹ᵁ g ⁻¹ᵁ W ≤ f₂ ⁻¹ᵁ g ⁻¹ᵁ W := by
  change (f₁ ≫ g) ⁻¹ᵁ W ≤ (f₂ ≫ g) ⁻¹ᵁ W
  rw [h]

/-- A section `s` of `E` over `g⁻¹ W` is compatible with the descent datum if for all
`f₁, f₂ : Y ⟶ S'` with `f₁ ≫ g = f₂ ≫ g`, the descent isomorphism maps `f₁^* s` to `f₂^* s`. -/
def IsDescentSection (W : S.Opens) (s : Γ(descentObj D, g ⁻¹ᵁ W)) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g),
    (descentHom D f₁ f₂ h).app (f₁ ⁻¹ᵁ g ⁻¹ᵁ W) (pullbackApp f₁ (descentObj D) (g ⁻¹ᵁ W) s) =
      ((Scheme.Modules.pullback f₂).obj (descentObj D)).presheaf.map
        (homOfLE (preimage_le_of_comp_eq h W)).op (pullbackApp f₂ (descentObj D) (g ⁻¹ᵁ W) s)

lemma isDescentSection_zero (W : S.Opens) : IsDescentSection D W 0 := by
  intro Y f₁ f₂ h
  simp only [map_zero]

lemma isDescentSection_add (W : S.Opens) {s t : Γ(descentObj D, g ⁻¹ᵁ W)}
    (hs : IsDescentSection D W s) (ht : IsDescentSection D W t) :
    IsDescentSection D W (s + t) := by
  intro Y f₁ f₂ h
  simp only [map_add, hs f₁ f₂ h, ht f₁ f₂ h]

lemma app_eq_map_app_of_eq {Y : Scheme.{u}} {q q' : Y ⟶ S} (e : q = q') (W : S.Opens)
    (hle : q ⁻¹ᵁ W ≤ q' ⁻¹ᵁ W) (r : Γ(S, W)) :
    q.app W r = Y.presheaf.map (homOfLE hle).op (q'.app W r) := by
  subst e
  rw [show homOfLE hle = 𝟙 _ from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma isDescentSection_smul (W : S.Opens) (r : Γ(S, W)) {s : Γ(descentObj D, g ⁻¹ᵁ W)}
    (hs : IsDescentSection D W s) : IsDescentSection D W (g.app W r • s) := by
  intro Y f₁ f₂ h
  rw [pullbackApp_smul, pullbackApp_smul, Hom.app_smul, hs f₁ f₂ h, map_smul]
  congr 1
  have e₁ : f₁.app (g ⁻¹ᵁ W) (g.app W r) = (f₁ ≫ g).app W r := by
    rw [Scheme.Hom.comp_app]; rfl
  have e₂ : f₂.app (g ⁻¹ᵁ W) (g.app W r) = (f₂ ≫ g).app W r := by
    rw [Scheme.Hom.comp_app]; rfl
  rw [e₁, e₂]
  exact app_eq_map_app_of_eq h W _ r


lemma isDescentSection_map {W W' : S.Opens} (i : W' ⟶ W) {s : Γ(descentObj D, g ⁻¹ᵁ W)}
    (hs : IsDescentSection D W s) :
    IsDescentSection D W'
      ((descentObj D).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op s) := by
  intro Y f₁ f₂ h
  rw [pullbackApp_map, pullbackApp_map, Hom.app_map, hs f₁ f₂ h]
  exact presheaf_map_map_eq _ _ _ _ _ _


lemma isDescentSection_of_local (W : S.Opens) (s : Γ(descentObj D, g ⁻¹ᵁ W))
    (hloc : ∀ x ∈ W, ∃ (W' : S.Opens) (i : W' ⟶ W), x ∈ W' ∧
      IsDescentSection D W' ((descentObj D).presheaf.map
        ((TopologicalSpace.Opens.map g.base).map i).op s)) :
    IsDescentSection D W s := by
  intro Y f₁ f₂ h
  choose W' i hxW' hW' using hloc
  let ι := {x : S // x ∈ W}
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨_, ((Scheme.Modules.pullback f₂).obj (descentObj D)).isSheaf⟩
    (fun x : ι ↦ f₁ ⁻¹ᵁ g ⁻¹ᵁ W' x.1 x.2) (f₁ ⁻¹ᵁ g ⁻¹ᵁ W)
    (fun x ↦ (TopologicalSpace.Opens.map f₁.base).map ((TopologicalSpace.Opens.map g.base).map
      (i x.1 x.2))) (fun y hy ↦ ?_) _ _ fun x ↦ ?_
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, hy⟩, hxW' _ hy⟩
  · have e := hW' x.1 x.2 f₁ f₂ h
    rw [pullbackApp_map, Hom.app_map] at e
    change ((Scheme.Modules.pullback f₂).obj (descentObj D)).presheaf.map _ _ =
      ((Scheme.Modules.pullback f₂).obj (descentObj D)).presheaf.map _ _
    rw [e, pullbackApp_map]
    exact presheaf_map_map_eq _ _ _ _ _ _


/-- The descended module of a descent datum as a submodule of `g_* E`: the sections of `E` over
`g⁻¹ W` compatible with the descent datum. -/
noncomputable def descentSubmodule :
    SheafOfModules.Submodule ((Scheme.Modules.pushforward g).obj (descentObj D)) where
  obj W :=
    { carrier := {s | IsDescentSection D W.unop s}
      add_mem' := isDescentSection_add D _
      zero_mem' := isDescentSection_zero D _
      smul_mem' r _ hs := isDescentSection_smul D _ r hs }
  map i _ hs := isDescentSection_map D i.unop hs
  isSheaf W s hs := isDescentSection_of_local D W.unop s fun x hx ↦ by
    obtain ⟨V, f, hf, hxV⟩ := hs x hx
    exact ⟨V, f, hxV, hf⟩


/-- The descended module of a descent datum relative to `g`. -/
noncomputable def descentModule : S.Modules := (descentSubmodule D).toSheafOfModules

/-- The inclusion of the descended module into `g_* E`. -/
noncomputable def descentModuleι :
    descentModule D ⟶ (Scheme.Modules.pushforward g).obj (descentObj D) :=
  (descentSubmodule D).ι

lemma descentModuleι_app (W : S.Opens) (x : Γ(descentModule D, W)) :
    (descentModuleι D).app W x = x.1 := rfl

lemma isDescentSection_coe (W : S.Opens) (x : Γ(descentModule D, W)) :
    IsDescentSection D W x.1 := x.2

/-- The counit `g^* M ⟶ E` of the descended module. -/
noncomputable def descentCounit :
    (Scheme.Modules.pullback g).obj (descentModule D) ⟶ descentObj D :=
  ((pullbackPushforwardAdjunction g).homEquiv _ _).symm (descentModuleι D)

lemma descentCounit_app_pullbackApp (W : S.Opens) (x : Γ(descentModule D, W)) :
    (descentCounit D).app (g ⁻¹ᵁ W) (pullbackApp g _ W x) = x.1 := by
  have e : (pullbackPushforwardAdjunction g).unit.app _ ≫
      (Scheme.Modules.pushforward g).map (descentCounit D) = descentModuleι D :=
    ((pullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have := congr(Hom.app $e W x)
  rw [Hom.comp_app_apply, pushforward_map_app] at this
  exact this


lemma descentCounit_comm {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    (Scheme.Modules.pullback f₁).map (descentCounit D) ≫ descentHom D f₁ f₂ h =
      ((pullbackCompIso' f₁ g (f₁ ≫ g) rfl _).inv ≫
        (pullbackCompIso' f₂ g (f₁ ≫ g) h.symm _).hom) ≫
        (Scheme.Modules.pullback f₂).map (descentCounit D) := by
  rw [← cancel_epi (pullbackCompIso' f₁ g (f₁ ≫ g) rfl (descentModule D)).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply ((pullbackPushforwardAdjunction (f₁ ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext W x
  rw [Hom.comp_app_apply, Hom.comp_app_apply, pushforward_map_app, pushforward_map_app]
  change ((pullbackCompIso' f₁ g (f₁ ≫ g) rfl (descentModule D)).hom ≫
      (Scheme.Modules.pullback f₁).map (descentCounit D) ≫ descentHom D f₁ f₂ h).app
        ((f₁ ≫ g) ⁻¹ᵁ W) (pullbackApp (f₁ ≫ g) (descentModule D) W x) =
    ((pullbackCompIso' f₂ g (f₁ ≫ g) h.symm (descentModule D)).hom ≫
      (Scheme.Modules.pullback f₂).map (descentCounit D)).app
        ((f₁ ≫ g) ⁻¹ᵁ W) (pullbackApp (f₁ ≫ g) (descentModule D) W x)
  have h₁ := pullbackCompIso'_hom_app_pullbackApp f₁ g (f₁ ≫ g) rfl (descentModule D) W
    (Scheme.Hom.comp_preimage f₁ g W).le x
  have h₂ := pullbackCompIso'_hom_app_pullbackApp f₂ g (f₁ ≫ g) h.symm (descentModule D) W
    (preimage_le_of_comp_eq h W) x
  rw [Hom.comp_app_apply, Hom.comp_app_apply, h₁, Hom.comp_app_apply, h₂, Hom.app_map,
    Hom.app_map, Hom.app_map, ← pullbackApp_naturality, ← pullbackApp_naturality,
    descentCounit_app_pullbackApp, isDescentSection_coe D W x f₁ f₂ h]
  exact presheaf_map_map_eq' _ _ _ _ _


set_option backward.isDefEq.respectTransparency false in
lemma descentCounit_comm' {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (hf₂ : f₂ ≫ g = f₁ ≫ g) :
    (pseudofunctorCat.map f₁.op.toLoc).toFunctor.map (descentCounit D) ≫
      D.hom (f₁ ≫ g) (i₁ := ()) (i₂ := ()) f₁ f₂ rfl hf₂ =
    ((pseudofunctorCat.mapComp' g.op.toLoc f₁.op.toLoc (f₁ ≫ g).op.toLoc
        rfl).inv.toNatTrans.app (descentModule D) ≫
      (pseudofunctorCat.mapComp' g.op.toLoc f₂.op.toLoc (f₁ ≫ g).op.toLoc
        (by rw [← hf₂]; rfl)).hom.toNatTrans.app (descentModule D)) ≫
      (pseudofunctorCat.map f₂.op.toLoc).toFunctor.map (descentCounit D) := by
  rw [pseudofunctorCat_mapComp'_inv_app f₁ g (f₁ ≫ g) rfl,
    pseudofunctorCat_mapComp'_hom_app f₂ g (f₁ ≫ g) hf₂,
    hom_eq_descentHom D (f₁ ≫ g) f₁ f₂ rfl hf₂]
  exact descentCounit_comm D f₁ f₂ hf₂.symm

lemma descentCounit_comm'' {Y : Scheme.{u}} (q : Y ⟶ S) (i₁ i₂ : Unit) (f₁ f₂ : Y ⟶ S')
    (hf₁ : f₁ ≫ g = q) (hf₂ : f₂ ≫ g = q) :
    (pseudofunctorCat.map f₁.op.toLoc).toFunctor.map ((fun _ ↦ descentCounit D) i₁) ≫
      D.hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
    ((pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj (descentModule D)).hom q
      (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
      (pseudofunctorCat.map f₂.op.toLoc).toFunctor.map ((fun _ ↦ descentCounit D) i₂) := by
  cases i₁; cases i₂
  subst hf₁
  exact descentCounit_comm' D f₁ f₂ hf₂

/-- The counit `g^* M ⟶ E` of the descended module, as a morphism of descent data. -/
noncomputable def descentCounitHom :
    (pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj (descentModule D) ⟶ D where
  hom _ := descentCounit D
  comm _ q i₁ i₂ f₁ f₂ hf₁ hf₂ := descentCounit_comm'' D q i₁ i₂ f₁ f₂ hf₁ hf₂

end Descent

end AlgebraicGeometry.Scheme.Modules
