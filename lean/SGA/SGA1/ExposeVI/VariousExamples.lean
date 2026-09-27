/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Bifibered
import SGA.SGA1.ExposeVI.Splittings
import SGA.SGA1.ExposeVI.Subcategories
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# SGA 1, Exposé VI, §11: various examples

* a) the target functor `Arrow E ⥤ E`: its fiber at `S` is `E/S`, it is co-split cofibered
  (`f_*` is composition with `f`), a square is cartesian iff it is a pullback square, so it is
  prefibered iff `E` has fibered products, and then fibered (and bifibered, by VI.10.1);
* b) presheaves on variable spaces: see `Presheaves.lean` and `CatOverOver.lean`;
* c) over a groupoid `D` (e.g. `SingleObj G`, an object with operators) every section is
  cartesian, so sections of `𝒳 ×_E D` are the `E`-functors `D ⥤ 𝒳` over `D ⥤ E`;
* d) the triangle identity for the pair `(f^*, g^*)` along inverse arrows is
  `Cleavage.IsNormalized.comparison_triangle`; the converse and the autodualities are in
  `AdjointEquivalences.lean`;
* e) discrete bases: see `BaseExamples.lean`;
* f) over the walking arrow `T ⟶ S` (the ordered set `Fin 2`), prefibered and fibered agree,
  and the category is fibered (resp. cofibered) iff `Hom_f(η, ξ)` is representable in `η`
  (resp. corepresentable in `ξ`); the reconstruction from `(𝒳_S, 𝒳_T, H)` is `Collage.lean`;
* g) `C × E` over `E` is fibered and cofibered, with a canonical splitting;
  `Γ(C × E / E) ≅ Hom(E, C)` and `lim(C × E / E)` is the full subcategory of functors
  inverting all arrows.
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

/-! ### General lemmas -/

section Lemmas

variable {C : Type u₂} [Category.{v₂} C]

theorem isCartesian_map_of_isCartesian' {E : Type u} [Category.{v} E] (q : C ⥤ E) {R S : E}
    (f : R ⟶ S) {a b : C} (φ : a ⟶ b) (h : IsCartesian q f φ) : IsCartesian q (q.map φ) φ := by
  subst_hom_lift q f φ
  exact h

theorem isCocartesian_map_of_isCocartesian {E : Type u} [Category.{v} E] (q : C ⥤ E)
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) (h : IsCocartesian q f φ) :
    IsCocartesian q (q.map φ) φ := by
  subst_hom_lift q f φ
  exact h

theorem isCocartesian_of_isCocartesian_map {E : Type u} [Category.{v} E] (q : C ⥤ E)
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsHomLift q f φ]
    (h : IsCocartesian q (q.map φ) φ) : IsCocartesian q f φ := by
  subst_hom_lift q f φ
  exact h

/-- A vertical cocartesian arrow is an isomorphism. -/
theorem isIso_of_vertical_isCocartesian {E : Type u} [Category.{v} E] (q : C ⥤ E) {S : E}
    {a b : C} (φ : a ⟶ b) [h : IsCocartesian q (𝟙 S) φ] : IsIso φ := by
  have := (isCocartesian_iff_op (𝟙 S) φ).mp h
  have : IsIso φ.op := isIso_of_vertical_isCartesian q.op (S := Opposite.op S) φ.op
  exact isIso_of_op φ

end Lemmas

/-! ### a) The category of arrows -/

section Arrows

open Limits

variable {E : Type u₁} [Category.{v₁} E]

theorem arrow_isHomLift {u v : Arrow E} (φ : u ⟶ v) : IsHomLift Arrow.rightFunc φ.right φ :=
  IsHomLift.map Arrow.rightFunc φ

theorem arrow_right_eq {u v : Arrow E} (φ : u ⟶ v) (f : u.right ⟶ v.right)
    [h : IsHomLift Arrow.rightFunc f φ] : φ.right = f :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ Arrow.rightFunc u v f φ h).symm

/-- VI.11 a): a square `sq : u ⟶ v` of `Arrow E` is cartesian for the target functor iff it
is a pullback square. -/
theorem arrow_isCartesian_iff {u v : Arrow E} (sq : u ⟶ v) :
    IsCartesian Arrow.rightFunc sq.right sq ↔ IsPullback sq.left u.hom v.hom sq.right := by
  have := arrow_isHomLift sq
  constructor
  · intro _
    let ψ : PullbackCone v.hom sq.right → (Σ' (a : Arrow E), a ⟶ v) := fun s ↦
      ⟨Arrow.mk s.snd, Arrow.homMk (f := Arrow.mk s.snd) s.fst sq.right s.condition⟩
    have hψ : ∀ s, IsHomLift Arrow.rightFunc sq.right (ψ s).2 := fun s ↦
      arrow_isHomLift (ψ s).2
    let χ := fun s ↦ @IsCartesian.map _ _ _ _ Arrow.rightFunc _ _ _ _ sq.right sq _ _ (ψ s).2
      (hψ s)
    have hχfac : ∀ s, χ s ≫ sq = (ψ s).2 := fun s ↦
      @IsCartesian.fac _ _ _ _ Arrow.rightFunc _ _ _ _ sq.right sq _ _ (ψ s).2 (hψ s)
    have hχr : ∀ s, (χ s).right = 𝟙 _ := fun s ↦ by
      have : IsHomLift Arrow.rightFunc (𝟙 u.right) (χ s) :=
        @IsCartesian.map_isHomLift _ _ _ _ Arrow.rightFunc _ _ _ _ sq.right sq _ _ (ψ s).2
          (hψ s)
      exact arrow_right_eq (χ s) (𝟙 u.right)
    refine IsPullback.of_isLimit' ⟨Arrow.w sq⟩ (PullbackCone.IsLimit.mk (Arrow.w sq)
      (fun s ↦ (χ s).left) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
    · exact congrArg Arrow.Hom.left (hχfac s)
    · have := Arrow.w (χ s)
      rw [hχr s, Category.comp_id] at this
      exact this
    · let χ' : Arrow.mk s.snd ⟶ u := Arrow.homMk m (𝟙 _) (by simpa using h₂)
      have : IsHomLift Arrow.rightFunc (𝟙 u.right) χ' := arrow_isHomLift χ'
      have := @IsCartesian.map_uniq _ _ _ _ Arrow.rightFunc _ _ _ _ sq.right sq _ _ (ψ s).2
        (hψ s) χ' _
        (Arrow.hom_ext _ _ h₁ (Category.id_comp _))
      exact congrArg Arrow.Hom.left this
  · intro hP
    refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
    obtain ⟨al, ar, ah⟩ := a'
    have har : ar = u.right := IsHomLift.domain_eq Arrow.rightFunc sq.right φ'
    subst har
    revert φ' hφ'
    change ∀ (φ' : Arrow.mk ah ⟶ v), IsHomLift Arrow.rightFunc sq.right φ' →
      ∃! χ : Arrow.mk ah ⟶ u, IsHomLift Arrow.rightFunc (𝟙 u.right) χ ∧ χ ≫ sq = φ'
    intro φ' hφ'
    have hφr : φ'.right = sq.right := arrow_right_eq φ' sq.right
    have hw : φ'.left ≫ v.hom = ah ≫ sq.right := by
      have := Arrow.w φ'
      rw [hφr] at this
      exact this
    let χ : Arrow.mk ah ⟶ u := Arrow.homMk (hP.lift φ'.left ah hw) (𝟙 _) (by simp)
    have : IsHomLift Arrow.rightFunc (𝟙 u.right) χ := arrow_isHomLift χ
    refine ⟨χ, ⟨this, Arrow.hom_ext _ _ (by simp [χ]) (by simp [χ, hφr])⟩, ?_⟩
    rintro χ' ⟨hχ', hfac⟩
    have hχ'r : χ'.right = 𝟙 _ := arrow_right_eq χ' (𝟙 u.right)
    refine Arrow.hom_ext _ _ (hP.hom_ext ?_ ?_) (by simp [χ, hχ'r])
    · simpa [χ] using congrArg Arrow.Hom.left hfac
    · have := Arrow.w χ'
      rw [hχ'r] at this
      simpa [χ] using this

/-- VI.11 a): the target functor `Arrow E ⥤ E` is prefibered iff `E` has fibered products. -/
theorem arrow_isPreFibered_iff : IsPreFibered (Arrow.rightFunc : Arrow E ⥤ E) ↔ HasPullbacks E := by
  constructor
  · intro _
    have : ∀ {X Y Z : E} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := by
      intro X Y Z f g
      obtain ⟨⟨bl, br, bh⟩, φ, hφ⟩ :=
        IsPreFibered.exists_isCartesian' (p := Arrow.rightFunc) (a := Arrow.mk f) g
      have : IsHomLift Arrow.rightFunc g φ := hφ.toIsHomLift
      have hbr : br = Y := IsHomLift.domain_eq Arrow.rightFunc g φ
      subst hbr
      have hφr : φ.right = g := arrow_right_eq φ g
      have := (arrow_isCartesian_iff φ).mp (isCartesian_map_of_isCartesian' _ g φ hφ)
      rw [hφr] at this
      exact this.hasPullback
    exact hasPullbacks_of_hasLimit_cospan E
  · intro _
    refine ⟨fun {v R} f ↦ ⟨Arrow.mk (pullback.snd v.hom f),
      Arrow.homMk (pullback.fst v.hom f) f pullback.condition, ?_⟩⟩
    exact (arrow_isCartesian_iff (Arrow.homMk (f := Arrow.mk (pullback.snd v.hom f)) (g := v)
      (pullback.fst v.hom f) f pullback.condition)).mpr (IsPullback.of_hasPullback v.hom f)

/-- VI.11 a): if `E` has fibered products, the target functor `Arrow E ⥤ E` is fibered. -/
instance arrow_isFibered [HasPullbacks E] : IsFibered (Arrow.rightFunc : Arrow E ⥤ E) := by
  have := arrow_isPreFibered_iff.mpr (inferInstance : HasPullbacks E)
  refine (isFibered_iff_comp _).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
  have h₁ := (arrow_isCartesian_iff φ).mp (isCartesian_map_of_isCartesian' _ f φ hφ)
  have h₂ := (arrow_isCartesian_iff ψ).mp (isCartesian_map_of_isCartesian' _ g ψ hψ)
  exact isCartesian_of_isCartesian_map _ (f ≫ g) (φ ≫ ψ)
    ((arrow_isCartesian_iff (φ ≫ ψ)).mpr (h₁.paste_horiz h₂))

/-- VI.11 a): the square `(𝟙, f) : u ⟶ u ≫ f` is cocartesian: `f_*` is composition with `f`
(the co-splitting of `Arrow E`). -/
theorem arrow_isCocartesian_homMk {X T S : E} (u : X ⟶ T) (f : T ⟶ S) :
    IsCocartesian Arrow.rightFunc f (Arrow.homMk' (f := u) (g := u ≫ f) (𝟙 X) f) := by
  have : IsHomLift Arrow.rightFunc f (Arrow.homMk' (f := u) (g := u ≫ f) (𝟙 X) f) :=
    arrow_isHomLift (Arrow.homMk' (f := u) (g := u ≫ f) (𝟙 X) f)
  refine ⟨fun {b'} ψ hψ ↦ ?_⟩
  obtain ⟨bl, br, bh⟩ := b'
  have hbr : br = S := IsHomLift.codomain_eq Arrow.rightFunc f ψ
  subst hbr
  revert ψ hψ
  change ∀ (ψ : Arrow.mk u ⟶ Arrow.mk bh), IsHomLift Arrow.rightFunc f ψ →
    ∃! χ : Arrow.mk (u ≫ f) ⟶ Arrow.mk bh, IsHomLift Arrow.rightFunc (𝟙 br) χ ∧
      Arrow.homMk' (f := u) (g := u ≫ f) (𝟙 X) f ≫ χ = ψ
  intro ψ hψ
  have hψr : ψ.right = f := arrow_right_eq ψ f
  let χ : Arrow.mk (u ≫ f) ⟶ Arrow.mk bh :=
    Arrow.homMk ψ.left (𝟙 _) (by simp [hψr])
  have : IsHomLift Arrow.rightFunc (𝟙 br) χ := arrow_isHomLift χ
  refine ⟨χ, ⟨this, Arrow.hom_ext _ _ (by simp [χ]) (by simp [χ, hψr])⟩, ?_⟩
  rintro χ' ⟨hχ', hfac⟩
  have hχ'r : χ'.right = 𝟙 _ := arrow_right_eq χ' (𝟙 br)
  refine Arrow.hom_ext _ _ ?_ (by simp [χ, hχ'r])
  simpa [χ] using congrArg Arrow.Hom.left hfac

/-- VI.11 a): the target functor `Arrow E ⥤ E` is coprefibered. -/
instance arrow_isPreCofibered : IsPreCofibered (Arrow.rightFunc : Arrow E ⥤ E) :=
  ⟨fun {u S} f ↦ ⟨Arrow.mk (u.hom ≫ f), Arrow.homMk (𝟙 u.left) f (by simp),
    arrow_isCocartesian_homMk u.hom f⟩⟩

/-- VI.11 a): as SGA deduces from VI.10.1, if `E` has fibered products then `Arrow E` is
bifibered over `E`. -/
instance arrow_isCofibered [HasPullbacks E] : IsCofibered (Arrow.rightFunc : Arrow E ⥤ E) := by
  have := arrow_isPreFibered_iff.mpr (inferInstance : HasPullbacks E)
  exact (isFibered_iff_isCofibered _).mp inferInstance

/-- VI.11 a): an object `X ⟶ S` of `E/S` as an object of the fiber of the target functor. -/
def overToArrowFiber (S : E) : Over S ⥤ Fiber (Arrow.rightFunc : Arrow E ⥤ E) S where
  obj X := ⟨Arrow.mk X.hom, rfl⟩
  map {X Y} g := ⟨Arrow.homMk g.left (𝟙 S) (by simp),
    arrow_isHomLift (Arrow.homMk (f := Arrow.mk X.hom) (g := Arrow.mk Y.hom) g.left (𝟙 S)
      (by simp))⟩
  map_id X := Subtype.ext (Arrow.hom_ext _ _ rfl rfl)
  map_comp f g := Subtype.ext (Arrow.hom_ext _ _ rfl (Category.id_comp (𝟙 S)).symm)

instance (S : E) : (overToArrowFiber S).Faithful where
  map_injective {X Y} {g g'} h := by
    ext
    exact congrArg (fun k ↦ Arrow.Hom.left k.val) h

instance (S : E) : (overToArrowFiber S).Full where
  map_surjective {X Y} u := by
    have hr : u.val.right = 𝟙 S := arrow_right_eq u.val (𝟙 S) (h := u.property)
    have hw : u.val.left ≫ Y.hom = X.hom := by
      have := Arrow.w u.val
      rw [hr] at this
      exact this.trans (Category.comp_id _)
    refine ⟨Over.homMk u.val.left hw, ?_⟩
    exact Subtype.ext (Arrow.hom_ext _ _ rfl hr.symm)

instance (S : E) : (overToArrowFiber S).IsIso where
  bijective_obj := by
    constructor
    · intro X Y h
      have h₁ := congrArg (fun k : Fiber (Arrow.rightFunc : Arrow E ⥤ E) S ↦ k.val) h
      change Arrow.mk X.hom = Arrow.mk Y.hom at h₁
      obtain ⟨X, ⟨⟨⟩⟩, x⟩ := X
      obtain ⟨Y, ⟨⟨⟩⟩, y⟩ := Y
      cases h₁
      rfl
    · rintro ⟨⟨A, B, h⟩, hB⟩
      change B = S at hB
      subst hB
      exact ⟨Over.mk h, rfl⟩

/-- VI.11 a): the fiber of the target functor `Arrow E ⥤ E` at `S` is canonically isomorphic
to `E/S`. -/
noncomputable def arrowFiberIso (S : E) :
    IsoCat (Over S) (Fiber (Arrow.rightFunc : Arrow E ⥤ E) S) :=
  (overToArrowFiber S).asIsomorphism

end Arrows

/-! ### c) Groupoid bases -/

section Groupoid

variable {D : Type u₂} [Category.{v₂} D] [IsGroupoid D]

/-- VI.11 c): over a groupoid every section is cartesian (its values are isomorphisms). -/
theorem isCartesianFunctor_of_isGroupoid {E : Type u} [Category.{v} E]
    {X : BasedCategory.{v₁, u₁} E} (s : BasedFunctor (BasedCategory.ofFunctor (𝟭 E)) X)
    [IsGroupoid E] : IsCartesianFunctor s where
  map_isCartesian {R S a b} f φ _ := by
    have : IsIso φ := IsGroupoid.all_isIso (C := E) φ
    have : IsIso (s.map φ) := Functor.map_isIso s.toFunctor φ
    infer_instance

/-- VI.11 c): for `λ : D ⥤ E` with `D` a groupoid, every `E`-functor `D ⥤ 𝒳` over `λ` sends
all arrows to cartesian arrows; so the cartesian sections of `𝒳 ×_E D` are all sections,
i.e. (for `D = SingleObj G`) the objects with operators of `𝒳` over the object with
operators `λ`. -/
theorem transformsToCartesian_of_isGroupoid {E : Type u} [Category.{v} E]
    (X : BasedCategory.{v₁, u₁} E) (L : D ⥤ E)
    (H : BasedFunctor (restrictBase (BasedCategory.ofFunctor (𝟭 D)) L) X) :
    TransformsToCartesian X L H := by
  intro a b φ
  have : IsHomLift X.p (L.map φ) (H.map φ) := (H.isHomLift_iff (L.map φ) φ).mpr
    (IsHomLift.map (𝟭 D ⋙ L) φ)
  have : IsIso (C := (restrictBase (BasedCategory.ofFunctor (𝟭 D)) L).obj) φ :=
    IsGroupoid.all_isIso (C := D) φ
  have : IsIso (H.map φ) := Functor.map_isIso H.toFunctor φ
  infer_instance

end Groupoid

/-! ### g) The product `C × E` over `E` -/

section Product

variable (C : Type u₂) [Category.{v₂} C] (E : Type u₁) [Category.{v₁} E]

variable {C E}

theorem prod_isHomLift_snd {R S : E} (f : R ⟶ S) {a b : C × E} (φ : a ⟶ b)
    [IsHomLift (CategoryTheory.Prod.snd C E) f φ] :
    φ.2 = eqToHom (IsHomLift.domain_eq (CategoryTheory.Prod.snd C E) f φ) ≫ f ≫
      eqToHom (IsHomLift.codomain_eq (CategoryTheory.Prod.snd C E) f φ).symm :=
  IsHomLift.fac' (CategoryTheory.Prod.snd C E) f φ

/-- VI.11 g): an arrow of `C × E` over `f` is cartesian iff its component in `C` is an
isomorphism. -/
theorem prod_isCartesian_iff {R S : E} (f : R ⟶ S) {a b : C × E} (φ : a ⟶ b)
    [IsHomLift (CategoryTheory.Prod.snd C E) f φ] :
    IsCartesian (CategoryTheory.Prod.snd C E) f φ ↔ IsIso φ.1 := by
  have ha := IsHomLift.domain_eq (CategoryTheory.Prod.snd C E) f φ
  have hφ := prod_isHomLift_snd f φ
  constructor
  · intro _
    let ψ : (b.1, a.2) ⟶ b := (𝟙 b.1, φ.2)
    have : IsHomLift (CategoryTheory.Prod.snd C E) f ψ := IsHomLift.of_fac' _ f ψ ha
      (IsHomLift.codomain_eq (CategoryTheory.Prod.snd C E) f φ) hφ
    let χ := IsCartesian.map (CategoryTheory.Prod.snd C E) f φ ψ
    have hχ : χ ≫ φ = ψ := IsCartesian.fac _ f φ ψ
    have h₁ : χ.1 ≫ φ.1 = 𝟙 b.1 := congrArg Prod.fst hχ
    let ω : a ⟶ a := (φ.1 ≫ χ.1, 𝟙 a.2)
    have : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 R) ω :=
      IsHomLift.of_fac' _ _ ω ha ha (by simp [ω])
    have : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 R) (𝟙 a) := IsHomLift.id ha
    have : ω = 𝟙 a := IsCartesian.ext (CategoryTheory.Prod.snd C E) f φ ω (𝟙 a) (by
      ext
      · simp [ω, h₁]
      · simp [ω])
    exact ⟨χ.1, congrArg Prod.fst this, h₁⟩
  · intro _
    refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
    have ha' := IsHomLift.domain_eq (CategoryTheory.Prod.snd C E) f φ'
    have hφ' := prod_isHomLift_snd f φ'
    let χ : a' ⟶ a := (φ'.1 ≫ inv φ.1, eqToHom (ha'.trans ha.symm))
    have hχ : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 R) χ :=
      IsHomLift.of_fac' _ _ χ ha' ha (by simp [χ])
    refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
    · ext
      · simp [χ]
      · simp [χ, hφ, hφ']
    · rintro χ' ⟨hχ', hfac⟩
      have hχ'2 := prod_isHomLift_snd (𝟙 R) χ'
      ext
      · simp [χ, ← congrArg Prod.fst hfac]
      · simp [χ, hχ'2]

/-- VI.11 g): an arrow of `C × E` over `f` whose component in `C` is an isomorphism is
cocartesian. -/
theorem prod_isCocartesian_of_isIso {R S : E} (f : R ⟶ S) {a b : C × E} (φ : a ⟶ b)
    [IsHomLift (CategoryTheory.Prod.snd C E) f φ] [IsIso φ.1] :
    IsCocartesian (CategoryTheory.Prod.snd C E) f φ := by
  have hb := IsHomLift.codomain_eq (CategoryTheory.Prod.snd C E) f φ
  have hφ := prod_isHomLift_snd f φ
  refine ⟨fun {b'} φ' hφ' ↦ ?_⟩
  have hb' := IsHomLift.codomain_eq (CategoryTheory.Prod.snd C E) f φ'
  have hφ' := prod_isHomLift_snd f φ'
  let χ : b ⟶ b' := (inv φ.1 ≫ φ'.1, eqToHom (hb.trans hb'.symm))
  have hχ : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 S) χ :=
    IsHomLift.of_fac' _ _ χ hb hb' (by simp [χ])
  refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
  · ext
    · simp [χ]
    · simp [χ, hφ, hφ']
  · rintro χ' ⟨hχ', hfac⟩
    have hχ'2 := prod_isHomLift_snd (𝟙 S) χ'
    ext
    · simp [χ, ← congrArg Prod.fst hfac]
    · simp [χ, hχ'2]

/-- VI.11 g): the transport `(𝟙, f) : (c, R) ⟶ (c, S)`. -/
abbrev prodTransport {R S : E} (f : R ⟶ S) (c : C) : ((c, R) : C × E) ⟶ (c, S) := (𝟙 c, f)

instance {R S : E} (f : R ⟶ S) (c : C) :
    IsHomLift (CategoryTheory.Prod.snd C E) f (prodTransport f c) :=
  IsHomLift.map (CategoryTheory.Prod.snd C E) (prodTransport f c)

instance {R S : E} (f : R ⟶ S) (c : C) :
    IsCartesian (CategoryTheory.Prod.snd C E) f (prodTransport f c) :=
  (prod_isCartesian_iff f _).mpr (inferInstanceAs (IsIso (𝟙 c)))

/-- VI.11 g): `C × E` is fibered over `E`. -/
instance prod_isFibered : IsFibered (CategoryTheory.Prod.snd C E) := by
  have : IsPreFibered (CategoryTheory.Prod.snd C E) :=
    ⟨fun {a R} f ↦ ⟨(a.1, R), prodTransport f a.1, inferInstance⟩⟩
  refine (isFibered_iff_comp _).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
  have := (prod_isCartesian_iff f φ).mp hφ
  have := (prod_isCartesian_iff g ψ).mp hψ
  exact (prod_isCartesian_iff (f ≫ g) (φ ≫ ψ)).mpr (inferInstanceAs (IsIso (φ.1 ≫ ψ.1)))

/-- VI.11 g): `C × E` is cofibered over `E` (hence bifibered). -/
instance prod_isCofibered : IsCofibered (CategoryTheory.Prod.snd C E) := by
  have : IsPreCofibered (CategoryTheory.Prod.snd C E) := ⟨fun {a S} f ↦ ⟨(a.1, S), (𝟙 a.1, f), by
    have : IsHomLift (CategoryTheory.Prod.snd C E) f ((𝟙 a.1, f) : a ⟶ (a.1, S)) :=
      IsHomLift.map (CategoryTheory.Prod.snd C E) ((𝟙 a.1, f) : a ⟶ (a.1, S))
    have : IsIso ((𝟙 a.1, f) : a ⟶ (a.1, S)).1 := inferInstanceAs (IsIso (𝟙 a.1))
    exact prod_isCocartesian_of_isIso f _⟩⟩
  exact (isFibered_iff_isCofibered _).mp inferInstance

/-- VI.11 g): the canonical cleavage of `C × E`, with transports `(𝟙, f)`. -/
noncomputable def prodCleavage : Cleavage (CategoryTheory.Prod.snd C E) :=
  Cleavage.ofLifts (fun {R S} _ ξ ↦ ⟨(ξ.val.1, R), rfl⟩)
    (fun f ξ ↦ show ((ξ.val.1, _) : C × E) ⟶ ξ.val from
      (𝟙 ξ.val.1, f ≫ eqToHom ξ.property.symm))
    (fun {R S} f ξ ↦ by
      have : IsHomLift (CategoryTheory.Prod.snd C E) f
          (show ((ξ.val.1, R) : C × E) ⟶ ξ.val from (𝟙 ξ.val.1, f ≫ eqToHom ξ.property.symm)) :=
        IsHomLift.of_fac' _ f _ rfl ξ.property (by simp)
      exact (prod_isCartesian_iff f _).mpr (inferInstanceAs (IsIso (𝟙 ξ.val.1))))

/-- VI.11 g): the canonical cleavage of `C × E` is a splitting (it corresponds to the
constant functor `Eᵒᵖ ⥤ Cat` with value `C`). -/
theorem prodCleavage_isSplitting : (prodCleavage (C := C) (E := E)).IsSplitting := by
  refine ⟨fun S ξ ↦ ?_, fun {U T S} f g ξ ↦ ⟨rfl, ?_⟩⟩
  · obtain ⟨⟨c, S'⟩, rfl⟩ := ξ
    refine ⟨rfl, ?_⟩
    apply Prod.ext
    · rfl
    · change 𝟙 S' ≫ eqToHom rfl = eqToHom rfl
      simp
  · obtain ⟨⟨c, S'⟩, rfl⟩ := ξ
    apply Prod.ext
    · change 𝟙 c ≫ 𝟙 c = 𝟙 c ≫ 𝟙 c
      rfl
    · change (g ≫ eqToHom rfl) ≫ f ≫ eqToHom rfl = 𝟙 U ≫ (g ≫ f) ≫ eqToHom rfl
      simp

variable (C E) in
/-- VI.11 g): `C × E` as a category over `E` through `pr₂`. -/
abbrev ProdOver : BasedCategory.{max v₁ v₂, max u₁ u₂} E where
  obj := C × E
  p := CategoryTheory.Prod.snd C E

/-- VI.11 g): `s ↦ pr₁ ∘ s`, from sections of `C × E` over `E` to functors `E ⥤ C`. -/
@[simps]
def prodSections : BasedFunctor (BasedCategory.ofFunctor (𝟭 E)) (ProdOver C E) ⥤ (E ⥤ C) where
  obj s := s.toFunctor ⋙ CategoryTheory.Prod.fst C E
  map α := Functor.whiskerRight α.toNatTrans (CategoryTheory.Prod.fst C E)

theorem prodSection_snd_obj (s : BasedFunctor (BasedCategory.ofFunctor (𝟭 E)) (ProdOver C E))
    (e : E) : (s.obj e).2 = e :=
  s.w_obj e

theorem prodSection_snd_map (s : BasedFunctor (BasedCategory.ofFunctor (𝟭 E)) (ProdOver C E))
    {e e' : E} (g : e ⟶ e') :
    (s.map g).2 = eqToHom (prodSection_snd_obj s e) ≫ g ≫
      eqToHom (prodSection_snd_obj s e').symm :=
  Functor.congr_hom s.w g

private theorem eqToHom_conj_aux {a b a' b' c c' : E} (g : c ⟶ c') (ha : a = c) (hb : b = c)
    (ha' : a' = c') (hb' : b' = c') :
    (eqToHom ha ≫ g ≫ eqToHom ha'.symm) ≫ eqToHom (ha'.trans hb'.symm) =
      eqToHom (ha.trans hb.symm) ≫ eqToHom hb ≫ g ≫ eqToHom hb'.symm := by
  subst ha hb ha' hb'
  simp

private theorem eqToHom_id_aux {a b c : E} (h₁ : a = c) (h₂ : b = c) :
    eqToHom (h₁.trans h₂.symm) = eqToHom h₁ ≫ 𝟙 c ≫ eqToHom h₂.symm := by
  subst h₁ h₂
  simp

instance : (prodSections (C := C) (E := E)).Faithful where
  map_injective {s s'} {α β} h := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext e
    apply Prod.ext
    · exact congrArg (fun γ ↦ γ.app e) h
    · have hα : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 e) (α.app e) := α.isHomLift' e
      have hβ : IsHomLift (CategoryTheory.Prod.snd C E) (𝟙 e) (β.app e) := β.isHomLift' e
      exact (prod_isHomLift_snd (C := C) (E := E) (𝟙 e) (α.app e)).trans
        (prod_isHomLift_snd (C := C) (E := E) (𝟙 e) (β.app e)).symm

instance : (prodSections (C := C) (E := E)).Full where
  map_surjective {s s'} β := by
    have hs : ∀ e : E, (s.obj e).2 = (s'.obj e).2 := fun e ↦
      (prodSection_snd_obj s e).trans (prodSection_snd_obj s' e).symm
    refine ⟨⟨
      { app := fun e ↦ (β.app e, eqToHom (hs e))
        naturality := fun e e' g ↦ ?_ }, fun e ↦ ?_⟩, ?_⟩
    · apply Prod.ext
      · exact β.naturality g
      · change (s.map g).2 ≫ eqToHom (hs e') = eqToHom (hs e) ≫ (s'.map g).2
        rw [prodSection_snd_map s g, prodSection_snd_map s' g]
        exact eqToHom_conj_aux g (prodSection_snd_obj s e) (prodSection_snd_obj s' e)
          (prodSection_snd_obj s e') (prodSection_snd_obj s' e')
    · exact IsHomLift.of_fac' (CategoryTheory.Prod.snd C E) (𝟙 e) _ (prodSection_snd_obj s e)
        (prodSection_snd_obj s' e) (by
          exact eqToHom_id_aux (prodSection_snd_obj s e) (prodSection_snd_obj s' e))
    · rfl

instance : (prodSections (C := C) (E := E)).IsIso where
  bijective_obj := by
    constructor
    · intro s s' h
      apply basedFunctor_ext
      have h₂ : s.toFunctor ⋙ CategoryTheory.Prod.snd C E =
          s'.toFunctor ⋙ CategoryTheory.Prod.snd C E := s.w.trans s'.w.symm
      change (s.toFunctor ⋙ CategoryTheory.Prod.fst C E).prod'
          (s.toFunctor ⋙ CategoryTheory.Prod.snd C E) =
        (s'.toFunctor ⋙ CategoryTheory.Prod.fst C E).prod'
          (s'.toFunctor ⋙ CategoryTheory.Prod.snd C E)
      rw [show s.toFunctor ⋙ CategoryTheory.Prod.fst C E =
        s'.toFunctor ⋙ CategoryTheory.Prod.fst C E from h, h₂]
    · intro G
      exact ⟨{ toFunctor := G.prod' (𝟭 E), w := rfl }, rfl⟩

/-- VI.11 g): `Γ(C × E / E) ≅ Hom(E, C)`, an isomorphism of categories. -/
noncomputable def prodSectionsIso :=
  (prodSections (C := C) (E := E)).asIsomorphism

variable (C E) in
/-- VI.11 g): functors `E ⥤ C` sending every arrow to an isomorphism. -/
def InvertsAllArrows : ObjectProperty (E ⥤ C) :=
  fun G ↦ ∀ {x y : E} (f : x ⟶ y), IsIso (G.map f)

theorem isCartesianFunctor_iff_invertsAllArrows
    (s : BasedFunctor (BasedCategory.ofFunctor (𝟭 E)) (ProdOver C E)) :
    IsCartesianFunctor s ↔ InvertsAllArrows C E (prodSections.obj s) := by
  constructor
  · intro hs x y f
    have : IsCartesian (BasedCategory.ofFunctor (𝟭 E)).p f f := isCartesian_id_functor f
    have := hs.map_isCartesian f f
    exact (prod_isCartesian_iff f (s.map f)).mp this
  · intro h
    refine ⟨fun {R S a b} f φ hφ ↦ ?_⟩
    have : IsHomLift (CategoryTheory.Prod.snd C E) f (s.map φ) :=
      (s.isHomLift_iff f φ).mpr hφ.toIsHomLift
    exact (prod_isCartesian_iff f (s.map φ)).mpr (h φ)

/-- VI.11 g): `lim(C × E / E)` is isomorphic to the full subcategory of `Hom(E, C)` formed by
the functors sending every arrow to an isomorphism. -/
noncomputable def prodCartesianSectionsIso :
    IsoCat (cartesianLimit (ProdOver C E)) (InvertsAllArrows C E).FullSubcategory :=
  haveI := ObjectProperty.isIso_lift_of_isIso (prodSections (C := C) (E := E))
    (cartesianFunctorProperty (X := BasedCategory.ofFunctor (𝟭 E)) (Y := ProdOver C E))
    (InvertsAllArrows C E) isCartesianFunctor_iff_invertsAllArrows
  ((InvertsAllArrows C E).lift ((cartesianFunctorProperty (X := BasedCategory.ofFunctor (𝟭 E))
      (Y := ProdOver C E)).ι ⋙ prodSections)
    (fun s ↦ (isCartesianFunctor_iff_invertsAllArrows s.obj).mp s.property)).asIsomorphism

end Product

/-! ### f) The walking arrow -/

section WalkingArrow

variable {C : Type u₂} [Category.{v₂} C] (p : C ⥤ Fin 2)

/-- VI.11 f): the arrow `f : T ⟶ S` of the base, with `T = 0` and `S = 1`. -/
def walkingArrow : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

omit [Category.{v₂} C] in
private theorem fin2_cases {R S T : Fin 2} (f : R ⟶ S) (g : S ⟶ T) : R = S ∨ S = T := by
  have h₁ := Fin.le_iff_val_le_val.mp (leOfHom f)
  have h₂ := Fin.le_iff_val_le_val.mp (leOfHom g)
  have := T.isLt
  rcases Nat.lt_or_ge S.val 1 with h | h
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr (Fin.ext (by omega))

/-- VI.11 f): over the walking arrow, a prefibered category is fibered. -/
theorem fin2_isFibered_iff : IsFibered p ↔ IsPreFibered p := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ (isFibered_iff_comp p).mpr ?_⟩
  intro R S T f g a b c φ ψ hφ hψ
  rcases fin2_cases f g with h | h
  · subst h
    obtain rfl : f = 𝟙 R := Subsingleton.elim _ _
    have : IsIso φ := isIso_of_vertical_isCartesian p (S := R) φ
    have : IsHomLift p (𝟙 R) (asIso φ).hom := hφ.toIsHomLift
    rw [Category.id_comp]
    exact IsCartesian.of_iso_comp p g ψ (asIso φ)
  · subst h
    obtain rfl : g = 𝟙 S := Subsingleton.elim _ _
    have : IsIso ψ := isIso_of_vertical_isCartesian p (S := S) ψ
    have : IsHomLift p (𝟙 S) (asIso ψ).hom := hψ.toIsHomLift
    rw [Category.comp_id]
    exact IsCartesian.of_comp_iso p f φ (asIso ψ)

/-- VI.11 f): over the walking arrow, a coprefibered category is cofibered. -/
theorem fin2_isCofibered_iff : IsCofibered p ↔ IsPreCofibered p := by
  refine ⟨fun h ↦ h.toIsPreCofibered, fun _ ↦ (isCofibered_iff_comp p).mpr ?_⟩
  intro R S T f g a b c φ ψ hφ hψ
  rcases fin2_cases f g with h | h
  · subst h
    obtain rfl : f = 𝟙 R := Subsingleton.elim _ _
    have : IsIso φ := isIso_of_vertical_isCocartesian p (S := R) φ
    rw [Category.id_comp]
    have hψ' := (isCocartesian_iff_op g ψ).mp hψ
    have : IsHomLift p.op (𝟙 (Opposite.op R)) (asIso φ.op).hom :=
      (isHomLift_op_iff (𝟙 R) φ).mpr hφ.toIsHomLift
    exact (isCocartesian_iff_op g (φ ≫ ψ)).mpr
      (IsCartesian.of_comp_iso p.op g.op ψ.op (asIso φ.op))
  · subst h
    obtain rfl : g = 𝟙 S := Subsingleton.elim _ _
    have : IsIso ψ := isIso_of_vertical_isCocartesian p (S := S) ψ
    rw [Category.comp_id]
    have hφ' := (isCocartesian_iff_op f φ).mp hφ
    have : IsHomLift p.op (𝟙 (Opposite.op S)) (asIso ψ.op).hom :=
      (isHomLift_op_iff (𝟙 S) ψ).mpr hψ.toIsHomLift
    exact (isCocartesian_iff_op f (φ ≫ ψ)).mpr
      (IsCartesian.of_iso_comp p.op f.op φ.op (asIso ψ.op))

/-- In the walking arrow, an arrow of `𝒳` lies over any base arrow between the right
objects. -/
theorem fin2_isHomLift {R S : Fin 2} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) (ha : p.obj a = R)
    (hb : p.obj b = S) : IsHomLift p f φ :=
  IsHomLift.of_fac p f φ ha hb (Subsingleton.elim _ _)

/-- VI.11 f): a category over the walking arrow `f : T ⟶ S` is fibered (or prefibered) iff the
bifunctor `H(η, ξ) = Hom_f(η, ξ)` is representable in `η` for every `ξ ∈ 𝒳_S`. -/
theorem fin2_isFibered_iff_representable :
    IsFibered p ↔ ∀ ξ : Fiber p 1, (homOverFunctor p walkingArrow ξ).IsRepresentable := by
  rw [fin2_isFibered_iff]
  constructor
  · intro _ ξ
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian p ξ.property walkingArrow
    exact (exists_isCartesian_iff_isRepresentable p walkingArrow ξ).mp
      ⟨⟨b, IsHomLift.domain_eq p walkingArrow φ⟩, φ, hφ⟩
  · intro h
    refine ⟨fun {a R} f ↦ ?_⟩
    rcases fin2_cases f (𝟙 (p.obj a)) with hR | -
    · subst hR
      obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      exact ⟨a, 𝟙 a, inferInstance⟩
    · by_cases hR : R = p.obj a
      · subst hR
        obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
        exact ⟨a, 𝟙 a, inferInstance⟩
      · have h₀ : R = 0 ∧ p.obj a = 1 := by
          have h₁ := Fin.le_iff_val_le_val.mp (leOfHom f)
          have := (p.obj a).isLt
          refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;>
            · have := fun h ↦ hR (Fin.ext h)
              omega
        obtain ⟨η, φ, hφ⟩ := (exists_isCartesian_iff_isRepresentable p walkingArrow
          ⟨a, h₀.2⟩).mpr (h ⟨a, h₀.2⟩)
        have : IsHomLift p f φ := fin2_isHomLift p f φ (η.property.trans h₀.1.symm) rfl
        exact ⟨η.val, φ, isCartesian_of_isCartesian_map p f φ
          (isCartesian_map_of_isCartesian' p walkingArrow φ hφ)⟩

/-- VI.11 f): a category over the walking arrow `f : T ⟶ S` is cofibered (or coprefibered) iff
`H(η, ξ) = Hom_f(η, ξ)` is corepresentable in `ξ` for every `η ∈ 𝒳_T`. -/
theorem fin2_isCofibered_iff_corepresentable :
    IsCofibered p ↔ ∀ η : Fiber p 0, (homOverCofunctor p walkingArrow η).IsCorepresentable := by
  rw [fin2_isCofibered_iff]
  constructor
  · intro _ η
    obtain ⟨b, φ, hφ⟩ := IsPreCofibered.exists_isCocartesian p η.property walkingArrow
    exact (exists_isCocartesian_iff_isCorepresentable p walkingArrow η).mp
      ⟨⟨b, IsHomLift.codomain_eq p walkingArrow φ⟩, φ, hφ⟩
  · intro h
    refine ⟨fun {a S} f ↦ ?_⟩
    by_cases hS : S = p.obj a
    · subst hS
      obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
      exact ⟨a, 𝟙 a, inferInstance⟩
    · have h₀ : p.obj a = 0 ∧ S = 1 := by
        have h₁ := Fin.le_iff_val_le_val.mp (leOfHom f)
        have := S.isLt
        refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;>
          · have := fun h ↦ hS (Fin.ext h)
            omega
      obtain ⟨ξ, φ, hφ⟩ := (exists_isCocartesian_iff_isCorepresentable p walkingArrow
        ⟨a, h₀.1⟩).mpr (h ⟨a, h₀.1⟩)
      have : IsHomLift p f φ := fin2_isHomLift p f φ rfl (ξ.property.trans h₀.2.symm)
      exact ⟨ξ.val, φ, isCocartesian_of_isCocartesian_map p f φ
        (isCocartesian_map_of_isCocartesian p walkingArrow φ hφ)⟩

end WalkingArrow

end SGA.SGA1.ExposeVI
