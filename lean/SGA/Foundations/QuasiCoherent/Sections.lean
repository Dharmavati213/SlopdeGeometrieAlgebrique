/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import SGA.Foundations.QuasiCoherent.Tilde

/-!
# Inverse images of sections of `𝒪_X`-modules

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_Y`-module `M`, the unit of the adjunction
`f^* ⊣ f_*` gives maps `Γ(M, U) → Γ(f^* M, f⁻¹ U)` (`Scheme.Modules.pullbackApp`), the inverse
image of sections. We record their naturality, compatibility with restrictions, with scalars and
with composition, their description along open immersions, and their injectivity along
surjective local isomorphisms. On affine schemes, the inverse image of `m ∈ M` along
`Spec B ⟶ Spec A` is `1 ⊗ m ∈ B ⊗_A M` (`AlgebraicGeometry.pullbackApp_SpecMap_tilde`).
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The inverse image of sections `Γ(M, U) → Γ(f^* M, f⁻¹ U)`, the unit of the adjunction
`f^* ⊣ f_*` on sections. -/
noncomputable def pullbackApp (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) ⟶ Γ((pullback f).obj M, f ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction f).unit.app M).app U

lemma pullbackApp_naturality (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens)
    (s : Γ(M, U)) :
    pullbackApp f N U (φ.app U s) = ((pullback f).map φ).app (f ⁻¹ᵁ U) (pullbackApp f M U s) :=
  congr($((pullbackPushforwardAdjunction f).unit.naturality φ).app U s)

lemma pullbackApp_map (f : X ⟶ Y) (M : Y.Modules) {U V : Y.Opens} (i : U ⟶ V) (s : Γ(M, V)) :
    pullbackApp f M U (M.presheaf.map i.op s) =
      ((pullback f).obj M).presheaf.map ((Opens.map f.base).map i).op (pullbackApp f M V s) :=
  congr($((((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op)) s)

lemma pullbackApp_smul (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    pullbackApp f M U (r • s) = f.app U r • pullbackApp f M U s :=
  Hom.app_smul _ r s

lemma pullbackApp_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) :
    pullbackApp g M U ≫ pullbackApp f _ _ =
      pullbackApp (f ≫ g) M U ≫ ((pullbackComp f g).inv.app M).app _ := by
  have := congr(Hom.app $(unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)) (pullbackPushforwardAdjunction (f ≫ g))
    (pullbackComp f g).inv M) U)
  rw [conjugateEquiv_pullbackComp_inv] at this
  simp only [Adjunction.comp_unit_app, Hom.comp_app, pushforwardComp_hom_app_app,
    pushforward_map_app] at this
  erw [Category.comp_id] at this
  exact this

lemma pullbackApp_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    pullbackApp (f ≫ g) M U s =
      ((pullbackComp f g).hom.app M).app _ (pullbackApp f _ _ (pullbackApp g M U s)) := by
  have := ConcreteCategory.congr_hom (pullbackApp_comp_hom f g M U) s
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  erw [this]
  exact (congr($(((pullbackComp f g).inv_hom_id_app M)).app _ (pullbackApp (f ≫ g) M U s))).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Along an open immersion, the inverse image of sections is the restriction to the image. -/
lemma pullbackApp_eq_of_isOpenImmersion (h : X ⟶ Y) [IsOpenImmersion h] (M : Y.Modules)
    (U : Y.Opens) :
    pullbackApp h M U = M.presheaf.map (homOfLE (h.image_preimage_le U)).op ≫
      ((restrictFunctorIsoPullback h).hom.app M).app (h ⁻¹ᵁ U) := by
  have := congr(Hom.app $(Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction h)
    (pullbackPushforwardAdjunction h) M) U)
  simp only [Hom.comp_app, restrictAdjunction_unit_app_app, pushforward_map_app] at this
  exact this.symm

lemma pullbackApp_eq_zero_iff_of_isOpenImmersion (h : X ⟶ Y) [IsOpenImmersion h]
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    pullbackApp h M U s = 0 ↔ M.presheaf.map (homOfLE (h.image_preimage_le U)).op s = 0 := by
  rw [pullbackApp_eq_of_isOpenImmersion]
  erw [ConcreteCategory.comp_apply]
  exact (injective_iff_map_eq_zero' _).mp
    (ConcreteCategory.bijective_of_isIso (((restrictFunctorIsoPullback h).hom.app M).app _)).1 _

/-- Inverse images of sections along equal morphisms. -/
lemma pullbackApp_eq_zero_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M, U)) : pullbackApp f M U s = 0 ↔ pullbackApp f' M U s = 0 := by
  subst h; rfl

/-- A section with vanishing inverse image along `g` has vanishing inverse image along
`f ≫ g`. -/
lemma pullbackApp_comp_eq_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) (hs : pullbackApp g M U s = 0) :
    pullbackApp (f ≫ g) M U s = 0 := by
  rw [pullbackApp_comp, hs, map_zero, map_zero]; rfl

/-- A section with vanishing inverse image along `f ≫ g` has vanishing iterated inverse image. -/
lemma pullbackApp_eq_zero_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) (hs : pullbackApp (f ≫ g) M U s = 0) :
    pullbackApp f _ _ (pullbackApp g M U s) = 0 := by
  rw [pullbackApp_comp] at hs
  exact (injective_iff_map_eq_zero' _).mp
    (ConcreteCategory.bijective_of_isIso (((pullbackComp f g).hom.app M).app _)).1 _ |>.mp hs

/-- Restriction maps along an equality of open sets are injective. -/
lemma _root_.TopCat.Presheaf.map_injective_of_eq {X : TopCat.{u}} (F : TopCat.Presheaf Ab.{u} X)
    {U U' : TopologicalSpace.Opens X} (h : U ⟶ U') (e : U = U') :
    Function.Injective (F.map h.op) := by
  subst e
  obtain rfl : h = 𝟙 U := Subsingleton.elim _ _
  rw [op_id, F.map_id]
  exact fun _ _ h ↦ h

/-- A section whose inverse images along a jointly surjective family of open immersions vanish
is zero. -/
lemma eq_zero_of_pullbackApp_eq_zero {ι : Type*} {W : ι → Scheme.{u}} (h : ∀ i, W i ⟶ Y)
    [∀ i, IsOpenImmersion (h i)] (hcov : ∀ y : Y, ∃ i, y ∈ Set.range (h i)) (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M, U)) (hs : ∀ i, pullbackApp (h i) M U s = 0) : s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun i ↦ h i ''ᵁ (h i ⁻¹ᵁ U)) U
    (fun i ↦ homOfLE ((h i).image_preimage_le U)) (fun y hy ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, w, rfl⟩ := hcov y
    exact Opens.mem_iSup.mpr ⟨i, w, hy, rfl⟩
  · rw [map_zero]
    exact (pullbackApp_eq_zero_iff_of_isOpenImmersion (h i) M U s).mp (hs i)

/-- Along a surjective local isomorphism, the inverse image of sections is injective. -/
lemma pullbackApp_injective_of_isLocalIso (π : X ⟶ Y) [IsLocalIso π] [Surjective π]
    (M : Y.Modules) (U : Y.Opens) : Function.Injective (pullbackApp π M U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  choose W hW hW' using fun x : X ↦ IsLocalIso.exists_isOpenImmersion (f := π) x
  refine eq_zero_of_pullbackApp_eq_zero (fun x : X ↦ (W x).ι ≫ π) (fun y ↦ ?_) M U s fun x ↦ ?_
  · obtain ⟨x, rfl⟩ := π.surjective y
    exact ⟨x, ⟨x, hW x⟩, rfl⟩
  · rw [pullbackApp_comp, hs, map_zero, map_zero]; rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

variable {A B : CommRingCat.{u}}

/-- The inverse image of the section `m` of `M^~` along `Spec B ⟶ Spec A` is `1 ⊗ m`, under the
isomorphism `pullbackSpecMapTildeIso`. -/
lemma pullbackApp_SpecMap_tilde (φ : A ⟶ B) (M : ModuleCat.{u} A) (m : M) :
    ((pullbackSpecMapTildeIso φ M).hom.app _)
      (pullbackApp (Spec.map φ) (tilde M) ⊤ (tilde.toOpen M ⊤ m)) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ (toExtendScalars M φ m) := by
  have := congr($(Adjunction.unit_leftAdjointUniq_hom_app
    (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
      (pushforwardSpecMapCompModuleSpecΓFunctorIso φ).symm) M).hom m)
  exact this

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z T : Scheme.{u}}

/-- Morphisms of modules commute with restriction maps. -/
lemma Hom.app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) := by
  have := congr($(φ.mapPresheaf.naturality i.op) x)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

/-- The inverse image of a section over `W` along a morphism `w` mapping into `W`, as a global
section. -/
noncomputable def pullbackAppTop (w : T ⟶ X) (P : X.Modules) (W : X.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ W) :
    Γ(P, W) ⟶ Γ((pullback w).obj P, ⊤) :=
  pullbackApp w P W ≫ ((pullback w).obj P).presheaf.map (homOfLE hw).op

/-- Inverse images of sections are natural in the module. -/
lemma pullbackAppTop_naturality (w : T ⟶ X) {P Q : X.Modules} (ψ : P ⟶ Q) (W : X.Opens)
    (hw : ⊤ ≤ w ⁻¹ᵁ W) (z : Γ(P, W)) :
    ((pullback w).map ψ).app ⊤ (pullbackAppTop w P W hw z) =
      pullbackAppTop w Q W hw (ψ.app W z) := by
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [pullbackApp_naturality, Hom.app_map]

/-- Inverse images of sections along a composite. -/
lemma pullbackAppTop_comp (v : T ⟶ Y) (w : Y ⟶ X) (P : X.Modules) (W : X.Opens)
    (h : ⊤ ≤ (v ≫ w) ⁻¹ᵁ W) (x : Γ(P, W)) :
    pullbackAppTop (v ≫ w) P W h x = ((pullbackComp v w).hom.app P).app ⊤
      (pullbackAppTop v ((pullback w).obj P) (w ⁻¹ᵁ W) h (pullbackApp w P W x)) := by
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [pullbackApp_comp]
  exact (Hom.app_map ((pullbackComp v w).hom.app P) (homOfLE h) _).symm

/-- Inverse images of global sections along a composite. -/
lemma pullbackAppTop_comp' (v : T ⟶ Y) (w : Y ⟶ X) (P : X.Modules) (W : X.Opens)
    (hw : ⊤ ≤ w ⁻¹ᵁ W) (h : ⊤ ≤ (v ≫ w) ⁻¹ᵁ W) (x : Γ(P, W)) :
    pullbackAppTop (v ≫ w) P W h x = ((pullbackComp v w).hom.app P).app ⊤
      (pullbackApp v ((pullback w).obj P) ⊤ (pullbackAppTop w P W hw x)) := by
  rw [pullbackAppTop_comp]
  congr 1
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [pullbackApp_map]
  erw [← ConcreteCategory.comp_apply]

/-- Inverse images of sections along equal morphisms. -/
lemma pullbackAppTop_congr {q q' : T ⟶ X} (e : q = q') (P : X.Modules) (W : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ W) (h' : ⊤ ≤ q' ⁻¹ᵁ W) (x : Γ(P, W)) :
    ((pullbackCongr e).hom.app P).app ⊤ (pullbackAppTop q P W h x) =
      pullbackAppTop q' P W h' x := by
  subst e
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {C C' : CommRingCat.{u}}

/-- Morphisms of modules on `Spec C` are `C`-linear on sections. -/
lemma Hom.app_smul_Spec {M N : (Spec C).Modules} (φ : M ⟶ N) (U : (Spec C).Opens) (c : C)
    (x : Γ(M, U)) : φ.app U (c • x) = c • φ.app U x := by
  rw [smul_Spec_def, Hom.app_smul, ← smul_Spec_def]

/-- The inverse image of global sections along `Spec C' ⟶ Spec C` is semilinear. -/
lemma pullbackApp_SpecMap_smul (β : C ⟶ C') (E : (Spec C).Modules) (c : C) (z : Γ(E, ⊤)) :
    pullbackApp (Spec.map β) E ⊤ (c • z) = β c • pullbackApp (Spec.map β) E ⊤ z := by
  rw [smul_Spec_def, pullbackApp_smul, smul_Spec_def]
  congr 1
  have h₁ : (⊤ : (Spec C).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
  have h₂ : ((Spec.map β) ⁻¹ᵁ ⊤ : (Spec C').Opens).leTop = 𝟙 (⊤ : (Spec C').Opens) :=
    Subsingleton.elim _ _
  erw [h₁, h₂, op_id, op_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact congr($(Scheme.ΓSpecIso_inv_naturality β).hom c).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Opposite

/-- `q^* N ≅ f^* g^* N` for `f ≫ g = q`. -/
noncomputable def pullbackCompIso' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) (N : Z.Modules) :
    (Scheme.Modules.pullback q).obj N ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) :=
  (Scheme.Modules.pullbackCongr h.symm).app N ≪≫ ((Scheme.Modules.pullbackComp f g).app N).symm

lemma Hom.comp_app_apply {X : Scheme.{u}} {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K)
    (U : X.Opens) (x : Γ(M, U)) : (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := by
  rw [Hom.comp_app]
  exact ConcreteCategory.comp_apply _ _ x

lemma iso_inv_app_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (y : Γ(M, U)) : e.inv.app U (e.hom.app U y) = y := by
  have := congr(Hom.app $(e.hom_inv_id) U y)
  erw [Hom.comp_app, ConcreteCategory.comp_apply] at this
  exact this

lemma natIso_inv_app_hom_app {X Y : Scheme.{u}} {F G : X.Modules ⥤ Y.Modules} (e : F ≅ G)
    (M : X.Modules) (U : Y.Opens) (y : Γ(F.obj M, U)) :
    (e.inv.app M).app U ((e.hom.app M).app U y) = y :=
  iso_inv_app_hom_app (e.app M) U y

lemma pullbackAppTop_eq_pullbackApp_map {T Y : Scheme.{u}} (v : T ⟶ Y) (P : Y.Modules)
    (W : Y.Opens) (hW : ⊤ ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (y : Γ(P, W)) :
    pullbackAppTop v P W h y = pullbackApp v P ⊤ (P.presheaf.map (homOfLE hW).op y) := by
  rw [pullbackApp_map]
  simp only [pullbackAppTop]
  erw [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]

lemma pullbackCompIso'_hom_app_pullbackAppTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (h : f ≫ g = q) (N : Z.Modules) (U : Z.Opens) (hq : ⊤ ≤ q ⁻¹ᵁ U)
    (hf : ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (x : Γ(N, U)) :
    ((pullbackCompIso' f g q h N).hom.app ⊤) (pullbackAppTop q N U hq x) =
      pullbackAppTop f ((Scheme.Modules.pullback g).obj N) _ hf (pullbackApp g N U x) := by
  subst h
  change ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackAppTop (f ≫ g) N U hq x) = _
  rw [pullbackAppTop_comp]
  exact natIso_inv_app_hom_app (Scheme.Modules.pullbackComp f g) N ⊤ _

lemma pullbackCompIso'_inv_app_pullbackAppTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (h : f ≫ g = q) (N : Z.Modules) (U : Z.Opens) (hq : ⊤ ≤ q ⁻¹ᵁ U)
    (hf : ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (x : Γ(N, U)) :
    ((pullbackCompIso' f g q h N).inv.app ⊤)
      (pullbackAppTop f ((Scheme.Modules.pullback g).obj N) _ hf (pullbackApp g N U x)) =
      pullbackAppTop q N U hq x := by
  rw [← pullbackCompIso'_hom_app_pullbackAppTop f g q h N U hq hf x]
  exact iso_inv_app_hom_app _ ⊤ _

/-- The additive equivalence on sections induced by an isomorphism of modules. -/
noncomputable def isoAppAddEquiv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃+ Γ(N, U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  left_inv := iso_inv_app_hom_app e U
  right_inv := iso_inv_app_hom_app e.symm U
  map_add' := map_add _

lemma _root_.TopCat.Presheaf.map_bijective_of_eq {X : TopCat.{u}} (F : TopCat.Presheaf Ab.{u} X)
    {U U' : TopologicalSpace.Opens X} (h : U ⟶ U') (e : U = U') :
    Function.Bijective (F.map h.op) := by
  subst e
  obtain rfl : h = 𝟙 U := Subsingleton.elim _ _
  rw [op_id, F.map_id]
  exact Function.bijective_id

lemma pullbackApp_bijective_of_isOpenImmersion {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    (M : Y.Modules) (U : Y.Opens) (hU : U ≤ h.opensRange) :
    Function.Bijective (pullbackApp h M U) := by
  have e : ⇑(pullbackApp h M U) = ⇑(((restrictFunctorIsoPullback h).hom.app M).app (h ⁻¹ᵁ U)) ∘
      ⇑(M.presheaf.map (homOfLE (h.image_preimage_le U)).op) := by
    ext x
    rw [pullbackApp_eq_of_isOpenImmersion]
    erw [ConcreteCategory.comp_apply]
    rfl
  rw [e]
  refine (ConcreteCategory.bijective_of_isIso _).comp (M.presheaf.map_bijective_of_eq _ ?_)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]

lemma pullbackCompIso'_inv_app_pullbackApp {T Y X : Scheme.{u}} (v : T ⟶ Y) (w : Y ⟶ X)
    (q : T ⟶ X) (h : v ≫ w = q) (P : X.Modules) (W : X.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ W)
    (hq : ⊤ ≤ q ⁻¹ᵁ W) (x : Γ(P, W)) :
    ((pullbackCompIso' v w q h P).inv.app ⊤)
      (pullbackApp v ((Scheme.Modules.pullback w).obj P) ⊤ (pullbackAppTop w P W hw x)) =
      pullbackAppTop q P W hq x := by
  have hv : ⊤ ≤ v ⁻¹ᵁ (w ⁻¹ᵁ W) := by rw [← h] at hq; exact hq
  have e : pullbackApp v ((Scheme.Modules.pullback w).obj P) ⊤ (pullbackAppTop w P W hw x) =
      pullbackAppTop v ((Scheme.Modules.pullback w).obj P) (w ⁻¹ᵁ W) hv (pullbackApp w P W x) :=
    (pullbackAppTop_eq_pullbackApp_map v _ _ hw hv _).symm
  rw [e]
  exact pullbackCompIso'_inv_app_pullbackAppTop v w q h P W hq hv x

/-- Inverse images of sections along `k = e ≫ π ≫ fst` (an isomorphism, a surjective local
isomorphism and an open immersion onto `W`) are injective on sections over `W`. -/
lemma pullbackAppTop_injective {T T₁ T₂ X : Scheme.{u}} (e : T ⟶ T₁) [IsIso e] (π : T₁ ⟶ T₂)
    [IsLocalIso π] [Surjective π] (f : T₂ ⟶ X) [IsOpenImmersion f] (P : X.Modules) (W : X.Opens)
    (hW : W ≤ f.opensRange) (h : ⊤ ≤ (e ≫ π ≫ f) ⁻¹ᵁ W) :
    Function.Injective (pullbackAppTop (e ≫ π ≫ f) P W h) := by
  have hf := (pullbackApp_bijective_of_isOpenImmersion f P W hW).1
  have hπ := pullbackApp_injective_of_isLocalIso π ((Scheme.Modules.pullback f).obj P) (f ⁻¹ᵁ W)
  have he := (pullbackApp_bijective_of_isOpenImmersion e
    ((Scheme.Modules.pullback (π ≫ f)).obj P) ((π ≫ f) ⁻¹ᵁ W)
    (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)).1
  have hπf : Function.Injective (pullbackApp (π ≫ f) P W) := fun a b hab ↦ by
    rw [pullbackApp_comp, pullbackApp_comp] at hab
    exact hf (hπ ((ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackComp π f).hom.app P).app _)).1 hab))
  have hall : Function.Injective (pullbackApp (e ≫ π ≫ f) P W) := fun a b hab ↦ by
    rw [pullbackApp_comp, pullbackApp_comp e (π ≫ f)] at hab
    exact hπf (he ((ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackComp e (π ≫ f)).hom.app P).app _)).1 hab))
  intro a b hab
  exact hall (((Scheme.Modules.pullback (e ≫ π ≫ f)).obj P).presheaf.map_injective_of_eq
    (homOfLE h) (top_le_iff.mp h).symm hab)

end AlgebraicGeometry.Scheme.Modules
