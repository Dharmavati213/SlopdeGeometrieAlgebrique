/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# SGA 1, Exposé VI, §11: discrete bases

VI.11(e): over a discrete category every based category is fibered and every
based functor is cartesian; restriction to the fibers gives an isomorphism of categories
`Hom_E(𝒳, 𝒴) ≅ ∏_i Hom(𝒳_i, 𝒴_i)` (`DiscreteBase.basedFunctorIso`), and
`Γ(𝒳/E) = lim(𝒳/E) ≅ ∏_i 𝒳_i` (`DiscreteBase.sectionsIso`; SGA's "`∏ E_i`" is a misprint for
`∏ 𝒳_i`).
-/

universe v u v₁ u₁

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {I : Type u} {C : Type u₁} [Category.{v₁} C] (p : C ⥤ Discrete I)

/-- VI.11(e): any category over a discrete base is fibered. -/
instance discrete_isFibered : IsFibered p :=
  IsFibered.of_exists_isStronglyCartesian fun a i f => by
    have : i = p.obj a := Discrete.ext (Discrete.eq_of_hom f)
    subst this
    obtain rfl : f = 𝟙 (p.obj a) := Subsingleton.elim _ _
    exact ⟨a, 𝟙 a, inferInstance⟩

/-- VI.11(e): every based functor over a discrete base is cartesian. -/
instance discrete_isCartesianFunctor {X Y : BasedCategory.{v₁, u₁} (Discrete I)}
    (F : BasedFunctor X Y) : IsCartesianFunctor F where
  map_isCartesian {R S a b} f φ hφ := by
    have hRS : R = S := Discrete.ext (Discrete.eq_of_hom f)
    subst hRS
    obtain rfl : f = 𝟙 R := Subsingleton.elim _ _
    have : IsCartesian X.p (𝟙 R) φ := hφ
    have : IsIso φ := isIso_of_vertical_isCartesian X.p (S := R) φ
    have : IsIso (F.map φ) := inferInstance
    infer_instance

end SGA.SGA1.ExposeVI

/-! ### VI.11 e): `Hom_E(𝒳, 𝒴) ≅ ∏ Hom(𝒳_i, 𝒴_i)` over a discrete base -/

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

namespace DiscreteBase

variable {I : Type u} {X Y : BasedCategory.{v₁, u₁} (Discrete I)}

/-- Over a discrete base, every arrow is vertical. -/
theorem isHomLift_id_of_eq {x y : X.obj} (φ : x ⟶ y) {i : I} (hx : X.p.obj x = ⟨i⟩) :
    IsHomLift X.p (𝟙 (⟨i⟩ : Discrete I)) φ :=
  IsHomLift.of_fac' X.p _ φ hx ((Discrete.ext (Discrete.eq_of_hom (X.p.map φ))).symm.trans hx)
    (Subsingleton.elim _ _)

variable (F : ∀ i : I, Fiber X.p ⟨i⟩ ⥤ Fiber Y.p ⟨i⟩)

/-- The value of the family on an object `x` of the fiber `i` (with `i` arbitrary). -/
def objAux {i : I} (x : X.obj) (hx : X.p.obj x = ⟨i⟩) : Y.obj :=
  Fiber.fiberInclusion.obj ((F i).obj (Fiber.mk hx))

theorem objAux_congr {i j : I} (h : i = j) (x : X.obj) (hx : X.p.obj x = ⟨i⟩)
    (hx' : X.p.obj x = ⟨j⟩) : objAux F x hx = objAux F x hx' := by
  subst h
  rfl

/-- The action of the family on an arrow `φ : x ⟶ y`, with `x` in the fiber `i` and `y` in the
fiber `j` (necessarily `i = j`). -/
def mapAux {i j : I} (h : i = j) {x y : X.obj} (hx : X.p.obj x = ⟨i⟩) (hy : X.p.obj y = ⟨j⟩)
    (φ : x ⟶ y) : objAux F x hx ⟶ objAux F y hy := by
  subst h
  have := isHomLift_id_of_eq φ hx
  exact Fiber.fiberInclusion.map ((F i).map (Fiber.homMk X.p ⟨i⟩ φ))

theorem mapAux_id {i : I} (x : X.obj) (hx : X.p.obj x = ⟨i⟩) :
    mapAux F rfl hx hx (𝟙 x) = 𝟙 _ := by
  change Fiber.fiberInclusion.map ((F i).map (𝟙 (Fiber.mk hx))) = _
  rw [Functor.map_id, Functor.map_id]
  rfl

theorem mapAux_comp {i j k : I} (h₁ : i = j) (h₂ : j = k) {x y z : X.obj}
    (hx : X.p.obj x = ⟨i⟩) (hy : X.p.obj y = ⟨j⟩) (hz : X.p.obj z = ⟨k⟩) (φ : x ⟶ y)
    (ψ : y ⟶ z) :
    mapAux F (h₁.trans h₂) hx hz (φ ≫ ψ) = mapAux F h₁ hx hy φ ≫ mapAux F h₂ hy hz ψ := by
  subst h₁ h₂
  have := isHomLift_id_of_eq φ hx
  have := isHomLift_id_of_eq ψ hy
  change Fiber.fiberInclusion.map ((F i).map (Fiber.homMk X.p ⟨i⟩ (φ ≫ ψ))) =
    Fiber.fiberInclusion.map ((F i).map (Fiber.homMk X.p ⟨i⟩ φ)) ≫
      Fiber.fiberInclusion.map ((F i).map (Fiber.homMk X.p ⟨i⟩ ψ))
  rw [← Fiber.homMk_comp, Functor.map_comp, Functor.map_comp]

theorem mapAux_eq {i : I} {x y : X.obj} (hx : X.p.obj x = ⟨i⟩) (hy : X.p.obj y = ⟨i⟩)
    (u : Fiber.mk hx ⟶ Fiber.mk hy) :
    mapAux F rfl hx hy (Fiber.fiberInclusion.map u) = Fiber.fiberInclusion.map ((F i).map u) :=
  rfl

/-- VI.11 e): the `E`-functor defined by a family of functors between the fibers. -/
def ofFamily : BasedFunctor X Y where
  obj x := objAux F x rfl
  map {x y} φ := mapAux F (Discrete.eq_of_hom (X.p.map φ)) rfl rfl φ
  map_id x := mapAux_id F x rfl
  map_comp {x y z} φ ψ := mapAux_comp F _ _ rfl rfl rfl φ ψ
  w := by
    refine CategoryTheory.Functor.ext (fun x ↦ ((F _).obj _).property) fun _ _ _ ↦
      Subsingleton.elim _ _

theorem mapAux_congr {i j i' j' : I} (h : i = j) (h' : i' = j') {x y : X.obj}
    (hx : X.p.obj x = ⟨i⟩) (hy : X.p.obj y = ⟨j⟩) (hx' : X.p.obj x = ⟨i'⟩)
    (hy' : X.p.obj y = ⟨j'⟩) (φ : x ⟶ y) :
    mapAux F h hx hy φ = eqToHom (objAux_congr F (congrArg Discrete.as (hx.symm.trans hx')) x
      hx hx') ≫ mapAux F h' hx' hy' φ ≫
        eqToHom (objAux_congr F (congrArg Discrete.as (hy.symm.trans hy')) y hy hy').symm := by
  obtain rfl : i = i' := congrArg Discrete.as (hx.symm.trans hx')
  obtain rfl : j = j' := congrArg Discrete.as (hy.symm.trans hy')
  simp

/-- VI.11 e): the fibers of `ofFamily F` are the given functors. -/
theorem fiberMap_ofFamily (i : I) : fiberMap (ofFamily F) ⟨i⟩ = F i := by
  refine CategoryTheory.Functor.ext (fun ξ ↦ ?_) (fun ξ η u ↦ ?_)
  · obtain ⟨x, hx⟩ := ξ
    exact Subtype.ext (objAux_congr F (congrArg Discrete.as hx) x rfl hx)
  · obtain ⟨x, hx⟩ := ξ
    obtain ⟨y, hy⟩ := η
    apply Fiber.hom_ext
    change mapAux F _ rfl rfl u.val = _
    rw [mapAux_congr F _ rfl rfl rfl hx hy, Functor.map_comp, Functor.map_comp, eqToHom_map,
      eqToHom_map]
    rfl

theorem eq_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {a b : C} (f : a ⟶ b)
    (h₁ : a = a) (h₂ : b = b) : f = eqToHom h₁ ≫ f ≫ eqToHom h₂ := by
  simp

theorem mapAux_fiberMap (G : BasedFunctor X Y) {i j : I} (h : i = j) {x y : X.obj}
    (hx : X.p.obj x = ⟨i⟩) (hy : X.p.obj y = ⟨j⟩) (φ : x ⟶ y) :
    mapAux (fun i ↦ fiberMap G ⟨i⟩) h hx hy φ = G.map φ := by
  subst h
  rfl

/-- VI.11 e): an `E`-functor is determined by its fibers. -/
theorem ofFamily_fiberMap (G : BasedFunctor X Y) : ofFamily (fun i ↦ fiberMap G ⟨i⟩) = G := by
  apply basedFunctor_ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun x y φ ↦ ?_
  change mapAux (fun i ↦ fiberMap G ⟨i⟩) _ rfl rfl φ = _
  exact (mapAux_fiberMap G _ rfl rfl φ).trans (eq_eqToHom_comp_comp_eqToHom _ _ _)

variable (X Y) in
/-- VI.11 e): restriction of `E`-functors to the fibers, `Hom_E(𝒳, 𝒴) ⥤ ∏ Hom(𝒳_i, 𝒴_i)`. -/
def restrictFamily : BasedFunctor X Y ⥤ ∀ i : I, (Fiber X.p ⟨i⟩ ⥤ Fiber Y.p ⟨i⟩) :=
  Functor.pi' fun i ↦ fiberHom (X := X) (Y := Y) (⟨i⟩ : Discrete I)

theorem natAux_congr {G H : BasedFunctor X Y} (γ : ∀ i : I, fiberMap G ⟨i⟩ ⟶ fiberMap H ⟨i⟩)
    {i j : I} (h : i = j) (y : X.obj) (hy : X.p.obj y = ⟨i⟩) (hy' : X.p.obj y = ⟨j⟩) :
    ((γ i).app (Fiber.mk hy)).val = ((γ j).app (Fiber.mk hy')).val := by
  subst h
  rfl

instance : (restrictFamily X Y (I := I)).Faithful where
  map_injective {G H} {α β} h := by
    apply BasedNatTrans.ext
    ext x
    have := congrArg (fun γ ↦ ((γ (X.p.obj x).as).app (Fiber.mk rfl)).val) h
    exact this

theorem natural_of_family {G H : BasedFunctor X Y}
    (γ : ∀ i : I, fiberMap G ⟨i⟩ ⟶ fiberMap H ⟨i⟩) {x y : X.obj} (φ : x ⟶ y) :
    G.map φ ≫ ((γ (X.p.obj y).as).app (Fiber.mk rfl)).val =
      ((γ (X.p.obj x).as).app (Fiber.mk rfl)).val ≫ H.map φ := by
  have hy : X.p.obj y = ⟨(X.p.obj x).as⟩ := (Discrete.ext (Discrete.eq_of_hom (X.p.map φ))).symm
  have := isHomLift_id_of_eq φ (rfl : X.p.obj x = ⟨(X.p.obj x).as⟩)
  have hn := congrArg Subtype.val ((γ (X.p.obj x).as).naturality
    (Fiber.homMk X.p ⟨(X.p.obj x).as⟩ φ))
  rw [natAux_congr γ (congrArg Discrete.as hy) y rfl hy]
  exact hn

instance : (restrictFamily X Y (I := I)).Full where
  map_surjective {G H} γ := by
    let α : G ⟶ H :=
      { app := fun x ↦ ((γ (X.p.obj x).as).app (Fiber.mk rfl)).val
        naturality := fun {_ _} φ ↦ natural_of_family γ φ
        isHomLift' := fun x ↦ ((γ _).app (Fiber.mk rfl)).property }
    refine ⟨α, ?_⟩
    funext i
    ext ⟨x, hx⟩
    exact natAux_congr γ (congrArg Discrete.as hx) x rfl hx

instance : (restrictFamily X Y (I := I)).IsIso where
  bijective_obj := by
    constructor
    · intro G H h
      rw [← ofFamily_fiberMap G, ← ofFamily_fiberMap H]
      exact congrArg ofFamily (h : (fun i ↦ fiberMap G ⟨i⟩) = fun i ↦ fiberMap H ⟨i⟩)
    · intro F
      exact ⟨ofFamily F, show (fun i ↦ fiberMap (ofFamily F) ⟨i⟩) = F from
        funext (fiberMap_ofFamily F)⟩

variable (X Y) in
/-- VI.11 e): over a discrete category, `Hom_E(𝒳, 𝒴) ≅ ∏_i Hom(𝒳_i, 𝒴_i)`, an isomorphism of
categories. -/
noncomputable def basedFunctorIso :
    IsoCat (BasedFunctor X Y) (∀ i : I, (Fiber X.p ⟨i⟩ ⥤ Fiber Y.p ⟨i⟩)) :=
  (restrictFamily X Y).asIsomorphism

/-! ### Sections over a discrete base -/

variable (X) in
/-- VI.11 e): a section of `𝒳` over the discrete category `I` is a family `(x_i)` with `x_i ∈ 𝒳_i`:
the functor `Γ(𝒳/E) ⥤ ∏_i 𝒳_i`. -/
def sectionsToFamily :
    BasedFunctor (BasedCategory.ofFunctor (𝟭 (Discrete I))) X ⥤ ∀ i : I, Fiber X.p ⟨i⟩ where
  obj s i := ⟨s.obj ⟨i⟩, s.w_obj ⟨i⟩⟩
  map α i := ⟨α.app ⟨i⟩, α.isHomLift' ⟨i⟩⟩

instance : (sectionsToFamily X).Faithful where
  map_injective {s t} {α β} h := by
    apply BasedNatTrans.ext
    ext ⟨i⟩
    exact congrArg (fun γ ↦ (γ i).val) h

instance : (sectionsToFamily X).Full where
  map_surjective {s t} β := by
    let α : s ⟶ t :=
      { toNatTrans := Discrete.natTrans fun i ↦ (β i.as).val
        isHomLift' := fun i ↦ (β i.as).property }
    exact ⟨α, rfl⟩

theorem basedFunctor_ext_discrete {s t : BasedFunctor (BasedCategory.ofFunctor (𝟭 (Discrete I))) X}
    (h : ∀ i : I, s.obj ⟨i⟩ = t.obj ⟨i⟩) : s = t := by
  apply basedFunctor_ext
  refine CategoryTheory.Functor.ext (fun i ↦ h i.as) fun i j φ ↦ ?_
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain rfl : i = j := Discrete.eq_of_hom φ
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim (α := (⟨i⟩ : Discrete I) ⟶ ⟨i⟩) _ _
  erw [s.map_id, t.map_id]
  simp

instance : (sectionsToFamily X).IsIso where
  bijective_obj := by
    constructor
    · intro s t h
      exact basedFunctor_ext_discrete fun i ↦ congrArg (fun ξ ↦ (ξ i).val) h
    · intro ξ
      refine ⟨{ toFunctor := Discrete.functor fun i ↦ (ξ i).val
                w := CategoryTheory.Functor.ext (fun i ↦ (ξ i.as).property)
                  fun _ _ _ ↦ Subsingleton.elim _ _ }, ?_⟩
      funext i
      rfl

variable (X) in
/-- VI.11 e): over a discrete category, `Γ(𝒳/E) = lim(𝒳/E) ≅ ∏_i 𝒳_i` (every section is cartesian,
`discrete_isCartesianFunctor`). -/
noncomputable def sectionsIso :
    IsoCat (BasedFunctor (BasedCategory.ofFunctor (𝟭 (Discrete I))) X) (∀ i : I, Fiber X.p ⟨i⟩) :=
  (sectionsToFamily X).asIsomorphism

end DiscreteBase

end SGA.SGA1.ExposeVI
