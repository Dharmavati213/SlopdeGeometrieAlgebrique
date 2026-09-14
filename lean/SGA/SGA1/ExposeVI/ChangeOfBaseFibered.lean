/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BaseChange
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.EqToHom

/-!
# SGA 1, Exposé VI, VI.6.6–6.9: change of base for (pre)fibered categories

Encoding: identify `IsHomLift (BaseChange.snd) f α` with `IsHomLift (𝟭 D) f α.right`.
Mediating arrows use `cobHomMk` or an explicit `eqToHom` in the base `D` only —
never `cases`/`subst` on `z.val.2 = R` after `subst_hom_lift`.

* VI.6.6: cartesian for `snd` over `f` iff the left component is cartesian for
  `p` over `L.map f`.
* VI.6.7: `changeOfBaseMap` preserves cartesian functors.
* VI.6.8: cartesian-lift functors embed as cartesian sections (one direction).
* VI.6.9: change of base preserves `(pre)fibered`.
-/

universe v v₁ v₃ u u₁ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {C : Type u₁} [Category.{v₁} C] {D : Type u₃} [Category.{v₃} D]

abbrev changeOfBaseProj (p : C ⥤ E) (L : D ⥤ E) : BaseChange p L ⥤ D :=
  BaseChange.snd p L

namespace changeOfBaseCartesian

variable {p : C ⥤ E} {L : D ⥤ E}

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

theorem isHomLift_snd_iff {R S : D} (f : R ⟶ S) {x y : BaseChange p L} (α : x ⟶ y) :
    IsHomLift (changeOfBaseProj p L) f α ↔ IsHomLift (𝟭 D) f α.right := by
  constructor
  · intro h
    exact IsHomLift.of_fac' (𝟭 D) f α.right
      (IsHomLift.domain_eq (changeOfBaseProj p L) f α)
      (IsHomLift.codomain_eq (changeOfBaseProj p L) f α)
      (IsHomLift.fac' (changeOfBaseProj p L) f α)
  · intro h
    exact IsHomLift.of_fac' (changeOfBaseProj p L) f α
      (IsHomLift.domain_eq (𝟭 D) f α.right)
      (IsHomLift.codomain_eq (𝟭 D) f α.right)
      (IsHomLift.fac' (𝟭 D) f α.right)

theorem isHomLift_image {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [IsHomLift (changeOfBaseProj p L) f α] :
    IsHomLift p (L.map f) α.left := by
  subst_hom_lift (changeOfBaseProj p L) f α
  exact α.over

def cobHomMk {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    (h₁ : IsHomLift p (L.map f) α₁) (h₂ : IsHomLift (𝟭 D) f α₂) : x ⟶ y where
  left := α₁
  right := α₂
  over := by
    refine IsHomLift.of_fac' p (L.map α₂) α₁ x.property y.property ?_
    have hleft := IsHomLift.fac' p (L.map f) α₁
    have hright := IsHomLift.fac' (𝟭 D) f α₂
    have hd₂ := IsHomLift.domain_eq (𝟭 D) f α₂
    have hc₂ := IsHomLift.codomain_eq (𝟭 D) f α₂
    cases hd₂
    cases hc₂
    have : α₂ = f := by simpa using hright
    simpa [this] using hleft

theorem isHomLift_cobHomMk {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    (h₁ : IsHomLift p (L.map f) α₁) (h₂ : IsHomLift (𝟭 D) f α₂) :
    IsHomLift (changeOfBaseProj p L) f (cobHomMk f α₁ α₂ h₁ h₂) :=
  (isHomLift_snd_iff f _).mpr h₂

theorem isCartesian_image {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hα : IsCartesian (changeOfBaseProj p L) f α] :
    IsCartesian p (L.map f) α.left := by
  haveI : IsHomLift (changeOfBaseProj p L) f α := hα.toIsHomLift
  haveI : IsHomLift p (L.map f) α.left := isHomLift_image f α
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp inferInstance
  refine ⟨?_⟩
  intro a' φ' hφ'
  have hx : x.val.2 = R := IsHomLift.domain_eq (𝟭 D) f α.right
  have hR₁ : p.obj a' = L.obj R := IsHomLift.domain_eq p (L.map f) φ'
  let z : BaseChange p L := ⟨(a', x.val.2), hR₁.trans (congrArg L.obj hx.symm)⟩
  have hψLift := isHomLift_cobHomMk (x := z) (y := y) f φ' α.right hφ' hα₂
  let ψ : z ⟶ y := cobHomMk f φ' α.right hφ' hα₂
  haveI : IsHomLift (changeOfBaseProj p L) f ψ := hψLift
  let χFull := IsCartesian.map (changeOfBaseProj p L) f α ψ
  refine ⟨χFull.left, ⟨?_, ?_⟩, ?_⟩
  · have hχ₁ : IsHomLift p (L.map (𝟙 R)) χFull.left := isHomLift_image (𝟙 R) χFull
    rwa [L.map_id] at hχ₁
  · exact congrArg BaseChange.Hom.left (IsCartesian.fac (changeOfBaseProj p L) f α ψ)
  · intro χ ⟨hχ, hfac⟩
    have hχ' : IsHomLift p (L.map (𝟙 R)) χ := by
      rwa [L.map_id]
    have hχLift := isHomLift_cobHomMk (x := z) (y := x) (𝟙 R) χ (𝟙 x.val.2) hχ' (IsHomLift.id hx)
    let χLift : z ⟶ x := cobHomMk (𝟙 R) χ (𝟙 x.val.2) hχ' (IsHomLift.id hx)
    haveI : IsHomLift (changeOfBaseProj p L) (𝟙 R) χLift := hχLift
    have hfacLift : χLift ≫ α = ψ := by
      apply BaseChange.Hom.ext
      · exact hfac
      · change (𝟙 x.val.2) ≫ α.right = α.right
        rw [Category.id_comp]
    exact congrArg BaseChange.Hom.left
      (IsCartesian.map_uniq (changeOfBaseProj p L) f α ψ χLift hfacLift)

theorem vertical_eqToHom_fac {R S : D} (f : R ⟶ S) {x y z : BaseChange p L}
    (α : x ⟶ y) (ψ : z ⟶ y)
    (hα₂ : IsHomLift (𝟭 D) f α.right) (hψ₂ : IsHomLift (𝟭 D) f ψ.right)
    (hx : x.val.2 = R) (hz : z.val.2 = R)
    (χ₂ : z.val.2 ⟶ x.val.2) (hχ₂ : χ₂ = eqToHom (hz.trans hx.symm)) :
    χ₂ ≫ α.right = ψ.right := by
  have hy : y.val.2 = S := IsHomLift.codomain_eq (𝟭 D) f α.right
  have ha : α.right = eqToHom hx ≫ f ≫ eqToHom hy.symm := by
    simpa using IsHomLift.fac' (𝟭 D) f α.right
  have hp : ψ.right = eqToHom hz ≫ f ≫ eqToHom
      (IsHomLift.codomain_eq (𝟭 D) f ψ.right).symm := by
    simpa using IsHomLift.fac' (𝟭 D) f ψ.right
  have hcod : IsHomLift.codomain_eq (𝟭 D) f ψ.right = hy := rfl
  subst hχ₂
  calc
    eqToHom (hz.trans hx.symm) ≫ α.right
        = eqToHom (hz.trans hx.symm) ≫ (eqToHom hx ≫ f ≫ eqToHom hy.symm) := by
          rw [ha]
    _ = eqToHom hz ≫ f ≫ eqToHom hy.symm := by simp only [eqToHom_trans_assoc]
    _ = ψ.right := by rw [hp, hcod]

theorem isHomLift_eqToHom_left {R S : D} (_f : R ⟶ S) {x y z : BaseChange p L}
    (_α : x ⟶ y) (_ψ : z ⟶ y)
    (hx : x.val.2 = R) (hz : z.val.2 = R)
    (χ₁ : z.val.1 ⟶ x.val.1) (hχ₁ : IsHomLift p (𝟙 (L.obj R)) χ₁)
    (χ₂ : z.val.2 ⟶ x.val.2) (hχ₂ : χ₂ = eqToHom (hz.trans hx.symm)) :
    IsHomLift p (L.map χ₂) χ₁ := by
  subst hχ₂
  refine IsHomLift.of_fac' p (L.map (eqToHom (hz.trans hx.symm))) χ₁
    ((IsHomLift.domain_eq p (𝟙 (L.obj R)) χ₁).trans (congrArg L.obj hz.symm))
    ((IsHomLift.codomain_eq p (𝟙 (L.obj R)) χ₁).trans (congrArg L.obj hx.symm)) ?_
  have hfac := IsHomLift.fac' p (𝟙 (L.obj R)) χ₁
  rw [hfac, eqToHom_map L (hz.trans hx.symm)]
  simp [eqToHom_trans, eqToHom_trans_assoc, Category.id_comp]

theorem isCartesian_of_image {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hαLift : IsHomLift (changeOfBaseProj p L) f α]
    (h : IsCartesian p (L.map f) α.left) :
    IsCartesian (changeOfBaseProj p L) f α := by
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp hαLift
  have hx : x.val.2 = R := IsHomLift.domain_eq (𝟭 D) f α.right
  haveI := hαLift
  haveI : IsHomLift p (L.map f) α.left := isHomLift_image f α
  haveI := h
  refine ⟨?_⟩
  intro z ψ hψ
  have hψ₁ : IsHomLift p (L.map f) ψ.left := isHomLift_image f ψ
  have hψ₂ : IsHomLift (𝟭 D) f ψ.right := (isHomLift_snd_iff f ψ).mp hψ
  haveI := hψ₁
  let χ₁ := IsCartesian.map p (L.map f) α.left ψ.left
  have hχ₁ : IsHomLift p (𝟙 (L.obj R)) χ₁ := inferInstance
  have hz : z.val.2 = R := IsHomLift.domain_eq (𝟭 D) f ψ.right
  let χ₂ : z.val.2 ⟶ x.val.2 := eqToHom (hz.trans hx.symm)
  have hχ₁_over : IsHomLift p (L.map χ₂) χ₁ :=
    isHomLift_eqToHom_left f α ψ hx hz χ₁ hχ₁ χ₂ rfl
  let χ : z ⟶ x := ⟨χ₁, χ₂, hχ₁_over⟩
  haveI : IsHomLift (changeOfBaseProj p L) (𝟙 R) χ :=
    (isHomLift_snd_iff (𝟙 R) χ).mpr
      (IsHomLift.eqToHom_domain_lift_id (hz.trans hx.symm) hz)
  refine ⟨χ, ⟨inferInstance, ?_⟩, ?_⟩
  · apply BaseChange.Hom.ext
    · exact IsCartesian.fac p (L.map f) α.left ψ.left
    · exact vertical_eqToHom_fac f α ψ hα₂ hψ₂ hx hz χ₂ rfl
  · intro χ' ⟨hχ', hfac'⟩
    have hχ'₁ : IsHomLift p (𝟙 (L.obj R)) χ'.left := by
      have := isHomLift_image (𝟙 R) χ'
      rwa [L.map_id] at this
    haveI := hχ'₁
    have hl : χ'.left ≫ α.left = ψ.left := congrArg BaseChange.Hom.left hfac'
    apply BaseChange.Hom.ext
    · exact IsCartesian.map_uniq p (L.map f) α.left ψ.left χ'.left hl
    · have hχ'₂ : IsHomLift (𝟭 D) (𝟙 R) χ'.right :=
        (isHomLift_snd_iff (𝟙 R) χ').mp hχ'
      have hfacχ := IsHomLift.fac' (𝟭 D) (𝟙 R) χ'.right
      have hd := IsHomLift.domain_eq (𝟭 D) (𝟙 R) χ'.right
      have hc := IsHomLift.codomain_eq (𝟭 D) (𝟙 R) χ'.right
      calc
        χ'.right = eqToHom hd ≫ 𝟙 R ≫ eqToHom hc.symm := hfacχ
        _ = eqToHom (hd.trans hc.symm) := by simp
        _ = eqToHom (hz.trans hx.symm) := rfl

theorem isCartesian_iff {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [IsHomLift (changeOfBaseProj p L) f α] :
    IsCartesian (changeOfBaseProj p L) f α ↔ IsCartesian p (L.map f) α.left :=
  ⟨fun _ => isCartesian_image f α, fun h => isCartesian_of_image f α h⟩

instance instIsPreFibered [IsPreFibered p] :
    IsPreFibered (changeOfBaseProj p L) where
  exists_isCartesian' {x R} f := by
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian p x.property (L.map f)
    have hφLift : IsHomLift p (L.map f) φ := hφ.toIsHomLift
    have hb : p.obj b = L.obj R :=
      @IsHomLift.domain_eq _ _ _ _ p _ _ _ _ (L.map f) φ hφLift
    let y : BaseChange p L := ⟨(b, R), hb⟩
    have h₂ : IsHomLift (𝟭 D) f f := IsHomLift.map (𝟭 D) f
    have hψLift := isHomLift_cobHomMk (x := y) (y := x) f φ f hφLift h₂
    let ψ := cobHomMk (x := y) (y := x) f φ f hφLift h₂
    haveI : IsHomLift (changeOfBaseProj p L) f ψ := hψLift
    exact ⟨y, ψ, isCartesian_of_image (x := y) (y := x) f ψ hφ⟩

instance instIsFibered [IsFibered p] :
    IsFibered (changeOfBaseProj p L) where
  comp {R S T} f g {x y z} α β hα hβ := by
    haveI := hα; haveI := hβ
    have hα₁ := isCartesian_image f α
    have hβ₁ := isCartesian_image g β
    haveI := hα₁; haveI := hβ₁
    have hcomp : IsCartesian p (L.map (f ≫ g)) (α.left ≫ β.left) := by
      rw [L.map_comp]
      exact IsFibered.comp (p := p) (L.map f) (L.map g) α.left β.left
    haveI : IsHomLift (changeOfBaseProj p L) (f ≫ g) (α ≫ β) := inferInstance
    exact isCartesian_of_image (f ≫ g) (α ≫ β) hcomp

end changeOfBaseCartesian

/-! ### VI.6.7 -/

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₁, u₁} E}

set_option linter.style.haveILetI false in
theorem isCartesianFunctor_changeOfBaseMap (F : BasedFunctor X Y) [IsCartesianFunctor F]
    (L : D ⥤ E) : IsCartesianFunctor (changeOfBaseMap F L) where
  map_isCartesian {R S a b} f φ hφ := by
    haveI : IsCartesian (changeOfBaseProj X.p L) f φ := hφ
    have hL : IsCartesian X.p (L.map f) φ.left :=
      changeOfBaseCartesian.isCartesian_image (p := X.p) (L := L) f φ
    haveI := hL
    have hF : IsCartesian Y.p (L.map f) (F.map φ.left) :=
      IsCartesianFunctor.map_isCartesian (F := F) (L.map f) φ.left
    haveI : IsHomLift (BaseChange.snd Y.p L) f ((changeOfBaseMap F L).map φ) :=
      BasedFunctor.preserves_isHomLift (changeOfBaseMap F L) f φ
    exact changeOfBaseCartesian.isCartesian_of_image (p := Y.p) (L := L) f
      ((changeOfBaseMap F L).map φ) hF

def changeOfBaseCartesianFunctors (L : D ⥤ E) :
    CartesianFunctors X Y ⥤
      CartesianFunctors (changeOfBase X L) (changeOfBase Y L) where
  obj F := by
    haveI : IsCartesianFunctor F.obj := F.property
    exact ⟨changeOfBaseMap F.obj L, isCartesianFunctor_changeOfBaseMap F.obj L⟩
  map {F G} α := InducedCategory.homMk (changeOfBaseNatTrans α.hom L)
  map_id _ := rfl
  map_comp α β := by
    apply InducedCategory.hom_ext
    exact (changeOfBaseHom (X := X) (Y := Y) L).map_comp α.hom β.hom

/-! ### VI.6.8 (cartesian-lift data → cartesian section) -/

structure CartesianLiftFunctor (p : C ⥤ E) (L : D ⥤ E) where
  toFunctor : D ⥤ C
  w : toFunctor ⋙ p = L
  map_isCartesian : ∀ {a b : D} (φ : a ⟶ b),
    IsCartesian p (L.map φ) (toFunctor.map φ)

def CartesianLiftFunctor.toSectionFunctor {p : C ⥤ E} {L : D ⥤ E}
    (F : CartesianLiftFunctor p L) :
    BasedFunctor (BasedCategory.ofFunctor (𝟭 D))
      (changeOfBase (BasedCategory.ofFunctor p) L) where
  toFunctor := BaseChange.lift F.toFunctor (𝟭 D) (by
    calc F.toFunctor ⋙ p = L := F.w
      _ = (𝟭 D) ⋙ L := (Functor.id_comp L).symm)
  w := BaseChange.lift_snd F.toFunctor (𝟭 D) _

set_option linter.style.haveILetI false in
theorem CartesianLiftFunctor.toSectionFunctor_isCartesian {p : C ⥤ E} {L : D ⥤ E}
    (F : CartesianLiftFunctor p L) :
    IsCartesianFunctor F.toSectionFunctor where
  map_isCartesian {R S a b} f φ hφ := by
    have h₂ : IsHomLift (𝟭 D) f φ := hφ.toIsHomLift
    haveI : IsHomLift (BaseChange.snd p L) f (F.toSectionFunctor.map φ) :=
      (changeOfBaseCartesian.isHomLift_snd_iff (p := p) (L := L) f _).mpr h₂
    refine changeOfBaseCartesian.isCartesian_of_image (p := p) (L := L) f
      (F.toSectionFunctor.map φ) ?_
    change IsCartesian p (L.map f) (F.toFunctor.map φ)
    subst_hom_lift (𝟭 D) f φ
    exact F.map_isCartesian φ

/-- VI.6.8: package a cartesian-lift functor as a cartesian section. -/
def CartesianLiftFunctor.toCartesianSection {p : C ⥤ E} {L : D ⥤ E}
    (F : CartesianLiftFunctor p L) :
    cartesianLimit (changeOfBase (BasedCategory.ofFunctor p) L) :=
  ⟨F.toSectionFunctor, F.toSectionFunctor_isCartesian⟩

end SGA.SGA1.ExposeVI
