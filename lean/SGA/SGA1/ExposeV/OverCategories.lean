/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import SGA.SGA1.ExposeV.ExactFunctors

/-!
# SGA 1, Exposé V, V.6.13: the Galois category of objects over a connected object

Let `C` be a Galois category with fibre functor `F`, `S` a connected object and `a ∈ F(S)`.
SGA states (and leaves the proof to the reader) that the category `C/S` of objects over `S` is
a Galois category, with fibre functor `F'(X) = F(X) ×_{F(S)} {a}` (`overFiber`), that
`H : X ↦ X × S` is exact with `F ≅ F' ∘ H`, and that the induced homomorphism
`u : π_{F'} → π_F` is an isomorphism onto the stabilizer of `a`, an open subgroup of `π_F`.

The fibre functor is shown to commute with connected finite limits and with all the colimits
commuting with `F`, using that limits and colimits of finite sets are stable under restriction
to a fibre.
-/

universe u₁ u₂ w

namespace SGA.SGA1.ExposeV

open CategoryTheory Limits PreGaloisCategory Functor

variable {C : Type u₁} [Category.{u₂} C]

section Over

variable [PreGaloisCategory C] (S : C)

instance : PreGaloisCategory (Over S) where
  hasTerminal := IsTerminal.hasTerminal Over.mkIdTerminal
  hasPullbacks := inferInstance
  hasFiniteCoproducts := ⟨fun _ ↦
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Over.forget S)⟩
  hasQuotientsByFiniteGroups _ _ _ := inferInstance
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    obtain ⟨Z, u, ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand i.left
    let v : Over.mk (u ≫ Y.hom) ⟶ Y := Over.homMk u
    exact ⟨Over.mk (u ≫ Y.hom), v, ⟨isColimitOfReflects (Over.forget S)
      ((isColimitMapCoconeBinaryCofanEquiv (Over.forget S) i v).symm hc)⟩⟩

variable {S} (F : C ⥤ FintypeCat.{w}) (a : F.obj S)

/-- V.6.13: the fibre functor of `C/S` at `a ∈ F(S)`: `F'(X) = F(X) ×_{F(S)} {a}`. -/
@[simps]
def overFiber : Over S ⥤ FintypeCat.{w} where
  obj X := FintypeCat.of {x : F.obj X.left // F.map X.hom x = a}
  map {X Y} f := FintypeCat.homMk fun x ↦ ⟨F.map f.left x.1, by
    rw [← FintypeCat.comp_apply, ← F.map_comp, Over.w f, x.2]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre functor at `a` commutes with the connected limits commuting with `F`. -/
lemma preservesLimitsOfShape_overFiber (J : Type) [SmallCategory J] [FinCategory J]
    [CategoryTheory.IsConnected J]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J (overFiber F a) where
  preservesLimit {K} := ⟨fun {c} hc ↦ by
    have hc' := isLimitOfPreserves (Over.forget S ⋙ F ⋙ FintypeCat.incl) hc
    refine ⟨isLimitOfReflects FintypeCat.incl ?_⟩
    apply Nonempty.some
    rw [Types.isLimit_iff]
    intro s hs
    obtain ⟨x, hx, hxu⟩ := (Types.isLimit_iff _).1 ⟨hc'⟩ (fun j ↦ (s j).1)
      fun f ↦ congrArg Subtype.val (hs f)
    have hxa : F.map c.pt.hom x = a := by
      obtain ⟨j⟩ : Nonempty J := inferInstance
      have hw : (c.π.app j).left ≫ (K.obj j).hom = c.pt.hom := Over.w (c.π.app j)
      rw [← hw, F.map_comp, FintypeCat.comp_apply]
      exact (congrArg (fun y ↦ F.map (K.obj j).hom y) (hx j)).trans (s j).2
    exact ⟨⟨x, hxa⟩, fun j ↦ Subtype.ext (hx j),
      fun y hy ↦ Subtype.ext (hxu y.1 fun j ↦ congrArg Subtype.val (hy j))⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre functor at `a` commutes with the colimits commuting with `F` (colimits of finite
sets are stable under restriction to a fibre). -/
lemma preservesColimitsOfShape_overFiber (J : Type*) [Category J] [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J FintypeCat.incl.{w}] :
    PreservesColimitsOfShape J (overFiber F a) where
  preservesColimit {K} := ⟨fun {c} hc ↦ by
    let E := K ⋙ Over.forget S ⋙ F ⋙ FintypeCat.incl
    let D := K ⋙ overFiber F a ⋙ FintypeCat.incl
    have hc' := (Types.isColimit_iff_coconeTypesIsColimit _).1
      ⟨isColimitOfPreserves (Over.forget S ⋙ F ⋙ FintypeCat.incl) hc⟩
    refine ⟨isColimitOfReflects FintypeCat.incl ?_⟩
    apply Nonempty.some
    rw [Types.isColimit_iff_coconeTypesIsColimit]
    let P (p : Σ j, E.obj j) : Prop := F.map (K.obj p.1).hom p.2 = a
    have hrel {p q : Σ j, E.obj j} (h : E.ColimitTypeRel p q) : P p ↔ P q := by
      obtain ⟨f, hf⟩ := h
      change F.map (K.obj p.1).hom p.2 = a ↔ F.map (K.obj q.1).hom q.2 = a
      rw [hf, ← Over.w (K.map f), F.map_comp, FintypeCat.comp_apply]
      exact Iff.rfl
    have hP {p q : Σ j, E.obj j} (h : Relation.EqvGen E.ColimitTypeRel p q) : P p ↔ P q := by
      induction h with
      | rel _ _ h => exact hrel h
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hlift {p q : Σ j, E.obj j} (h : Relation.EqvGen E.ColimitTypeRel p q) (hp : P p)
        (hq : P q) : Relation.EqvGen D.ColimitTypeRel ⟨p.1, ⟨p.2, hp⟩⟩ ⟨q.1, ⟨q.2, hq⟩⟩ := by
      induction h with
      | rel p q h =>
        obtain ⟨f, hf⟩ := h
        exact .rel _ _ ⟨f, Subtype.ext hf⟩
      | refl => exact .refl _
      | symm p q _ ih => exact .symm _ _ (ih hq hp)
      | trans p q r h₁ _ ih₁ ih₂ =>
        have hq' := (hP h₁).1 hp
        exact .trans _ _ _ (ih₁ hp hq') (ih₂ hq' hq)
    refine ⟨⟨fun u v huv ↦ ?_, fun y ↦ ?_⟩⟩
    · obtain ⟨j, x, rfl⟩ := D.ιColimitType_jointly_surjective u
      obtain ⟨j', x', rfl⟩ := D.ιColimitType_jointly_surjective v
      have h1 : E.ιColimitType j x.1 = E.ιColimitType j' x'.1 :=
        hc'.bijective.1 (congrArg Subtype.val huv)
      rw [Functor.ιColimitType_eq_iff] at h1
      exact (Functor.ιColimitType_eq_iff _ _ _).2 (hlift h1 x.2 x'.2)
    · obtain ⟨j, x, hx⟩ := (Functor.CoconeTypes.descColimitType_surjective_iff _).1
        hc'.bijective.2 y.1
      have hxa : F.map (K.obj j).hom x = a := by
        have hw : (c.ι.app j).left ≫ c.pt.hom = (K.obj j).hom := Over.w (c.ι.app j)
        rw [← hw, F.map_comp, FintypeCat.comp_apply]
        exact (congrArg (fun z ↦ F.map c.pt.hom z) hx).trans y.2
      exact ⟨D.ιColimitType j ⟨x, hxa⟩, Subtype.ext hx⟩⟩

end Over

section OverGalois

variable [GaloisCategory C] {S : C} (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (a : F.obj S)

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre at `a` of the final object `S` of `C/S` is a point. -/
def isTerminalOverFiber : IsTerminal ((overFiber F a).obj (Over.mk (𝟙 S))) :=
  IsTerminal.ofUniqueHom (fun _ ↦ FintypeCat.homMk fun _ ↦ ⟨a, by simp⟩) fun Y m ↦ by
    ext y
    apply Subtype.ext
    have := (m y).2
    simp only [Over.mk_left, Over.mk_hom, F.map_id, FintypeCat.id_apply] at this
    exact this

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.13: for `S` connected, the fibre at `a` is a fibre functor on `C/S`. -/
instance [IsConnected S] : FiberFunctor (overFiber F a) where
  preservesTerminalObjects := by
    have := preservesTerminal_of_iso (overFiber F a)
      ((overFiber F a).mapIso (terminalIsoIsTerminal Over.mkIdTerminal) ≪≫
        (isTerminalOverFiber F a).uniqueUpToIso terminalIsTerminal)
    exact preservesLimitsOfShape_pempty_of_preservesTerminal _
  preservesPullbacks := preservesLimitsOfShape_overFiber F a WalkingCospan
  preservesFiniteCoproducts := ⟨fun n ↦ preservesColimitsOfShape_overFiber F a _⟩
  preservesEpis := ⟨fun {X Y} f _ ↦ by
    have : Epi f.left := (Over.forget S).map_epi f
    have hs := surjective_on_fiber_of_epi F f.left
    refine ConcreteCategory.epi_of_surjective _ fun y ↦ ?_
    obtain ⟨x, hx⟩ := hs y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [← Over.w f, F.map_comp, FintypeCat.comp_apply, hx, y.2]⟩
  preservesQuotientsByFiniteGroups G _ _ := preservesColimitsOfShape_overFiber F a _
  reflectsIsos := ⟨fun {X Y} f hf ↦ by
    have hb := (ConcreteCategory.isIso_iff_bijective ((overFiber F a).map f)).1 hf
    suffices IsIso ((Over.forget S).map f) from isIso_of_reflects_iso f (Over.forget S)
    suffices Function.Bijective (F.map f.left) by
      have : IsIso (F.map f.left) := (ConcreteCategory.isIso_iff_bijective _).2 this
      exact isIso_of_reflects_iso f.left F
    have hw (x : F.obj X.left) : F.map Y.hom (F.map f.left x) = F.map X.hom x := by
      rw [← FintypeCat.comp_apply, ← F.map_comp, Over.w f]
    refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) a (F.map X.hom x₁)
      have h₁ : F.map X.hom (σ⁻¹ • x₁) = a := by rw [← mulAction_naturality, ← hσ, inv_smul_smul]
      have h₂ : F.map X.hom (σ⁻¹ • x₂) = a := by
        rw [← mulAction_naturality, ← hw, ← h, hw, ← hσ, inv_smul_smul]
      have := hb.1 (a₁ := ⟨σ⁻¹ • x₁, h₁⟩) (a₂ := ⟨σ⁻¹ • x₂, h₂⟩)
        (Subtype.ext (by
          change F.map f.left (σ⁻¹ • x₁) = F.map f.left (σ⁻¹ • x₂)
          rw [← mulAction_naturality, h, mulAction_naturality]))
      simpa using congrArg Subtype.val this
    · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) a (F.map Y.hom y)
      have h₁ : F.map Y.hom (σ⁻¹ • y) = a := by rw [← mulAction_naturality, ← hσ, inv_smul_smul]
      obtain ⟨x, hx⟩ := hb.2 ⟨σ⁻¹ • y, h₁⟩
      refine ⟨σ • x.1, ?_⟩
      rw [← mulAction_naturality,
        show F.map f.left x.1 = σ⁻¹ • y from congrArg Subtype.val hx, smul_inv_smul]⟩

variable (S) in
/-- V.6.13: for `S` connected, the category `C/S` of objects over `S` is a Galois category. -/
instance [IsConnected S] : GaloisCategory (Over S) :=
  let F := CategoryTheory.GaloisCategory.getFiberFunctor C
  galoisCategory_of_fiberFunctor (overFiber F (nonempty_fiber_of_isConnected F S).some)

variable (S) in
/-- V.6.13: the functor `H : X ↦ X × S` from `C` to `C/S`. -/
@[simps]
noncomputable def prodOver : C ⥤ Over S where
  obj X := Over.mk (prod.snd : X ⨯ S ⟶ S)
  map f := Over.homMk (prod.map f (𝟙 S)) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.13: `F ≅ F' ∘ H`, where `F'` is the fibre functor of `C/S` at `a`. -/
noncomputable def prodOverCompOverFiberIso : prodOver S ⋙ overFiber F a ≅ F :=
  NatIso.ofComponents (fun X ↦ FintypeCat.equivEquivIso
    { toFun := fun z ↦ F.map prod.fst z.1
      invFun := fun x ↦ ⟨(fiberBinaryProductEquiv F X S).symm (x, a), by
        change F.map prod.snd _ = a
        simp⟩
      left_inv := fun z ↦ Subtype.ext (by
        apply ext_map_fst_snd F
        · simp
        · simp only [fiberBinaryProductEquiv_symm_snd_apply]
          exact z.2.symm)
      right_inv := fun x ↦ by simp }) fun {X Y} f ↦ by
    ext z
    change F.map prod.fst (F.map (prod.map f (𝟙 S)) z.1) = F.map f (F.map prod.fst z.1)
    rw [← FintypeCat.comp_apply, ← F.map_comp, prod.map_fst, F.map_comp, FintypeCat.comp_apply]

instance [IsConnected S] : FiberFunctor (prodOver S ⋙ overFiber F a) :=
  fiberFunctor_of_natIso (prodOverCompOverFiberIso F a).symm

include F a in
/-- V.6.13: the functor `X ↦ X × S` from `C` to `C/S` is exact. -/
theorem exact_prodOver [IsConnected S] :
    PreservesFiniteLimits (prodOver S) ∧ PreservesFiniteColimits (prodOver S) :=
  exact_of_fiberFunctor_comp _ (overFiber F a)

/-- V.6.13: the homomorphism `u : π_{F'} → π_F` induced by `H : X ↦ X × S`, where `π_{F'∘H}`
is identified with `π_F` by `F ≅ F' ∘ H`. -/
noncomputable def overFiberAutHom : Aut (overFiber F a) →* Aut F :=
  (prodOverCompOverFiberIso F a).conjAut.toMonoidHom.comp
    (autWhiskerLeft (prodOver S) (overFiber F a))

lemma overFiberAutHom_apply (σ : Aut (overFiber F a)) (X : C) (x : F.obj X) :
    (overFiberAutHom F a σ).hom.app X x = (prodOverCompOverFiberIso F a).hom.app X
      (σ.hom.app ((prodOver S).obj X) ((prodOverCompOverFiberIso F a).inv.app X x)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6.13: `u` is an isomorphism of `π_{F'}` onto the stabilizer of `a`, an open subgroup of
`π_F` (`stabilizer_isOpen`). -/
theorem injective_overFiberAutHom_and_range_eq :
    Function.Injective (overFiberAutHom F a) ∧
      (overFiberAutHom F a).range = MulAction.stabilizer (Aut F) a := by
  let e := prodOverCompOverFiberIso F a
  have he (X : C) (z : (overFiber F a).obj ((prodOver S).obj X)) :
      e.hom.app X z = F.map prod.fst z.1 := rfl
  have he' (X : C) (x : F.obj X) :
      (e.inv.app X x).1 = (fiberBinaryProductEquiv F X S).symm (x, a) := rfl
  refine ⟨fun σ₁ σ₂ h ↦ ?_, le_antisymm ?_ ?_⟩
  · -- `σ₁` and `σ₂` agree on the objects `X × S`, hence everywhere since every `Y` over `S`
    -- embeds into `Y × S` by its graph.
    have h1 (X : C) (z : (overFiber F a).obj ((prodOver S).obj X)) :
        σ₁.hom.app _ z = σ₂.hom.app _ z := by
      apply ((ConcreteCategory.isIso_iff_bijective (e.hom.app X)).1 inferInstance).1
      have := congrArg (fun σ : Aut F ↦ σ.hom.app X (e.hom.app X z)) h
      simpa [overFiberAutHom_apply, e] using this
    apply Aut.ext
    ext Y z
    let γ : Y ⟶ (prodOver S).obj Y.left :=
      Over.homMk (prod.lift (𝟙 Y.left) Y.hom : Y.left ⟶ ((prodOver S).obj Y.left).left)
        (by change prod.lift (𝟙 Y.left) Y.hom ≫ prod.snd = Y.hom; simp)
    have hγ : Function.Injective ((overFiber F a).map γ) := fun z z' hz ↦ by
      apply Subtype.ext
      have := congrArg (fun w ↦ F.map prod.fst w.1) hz
      change F.map prod.fst (F.map (prod.lift (𝟙 Y.left) Y.hom) z.1) =
        F.map prod.fst (F.map (prod.lift (𝟙 Y.left) Y.hom) z'.1) at this
      simpa [← FintypeCat.comp_apply, ← F.map_comp] using this
    apply hγ
    rw [← FintypeCat.comp_apply, ← σ₁.hom.naturality, FintypeCat.comp_apply, h1,
      ← FintypeCat.comp_apply, σ₂.hom.naturality, FintypeCat.comp_apply]
  · rintro _ ⟨σ, rfl⟩
    change (overFiberAutHom F a σ).hom.app S a = a
    rw [overFiberAutHom_apply]
    let δ : Over.mk (𝟙 S) ⟶ (prodOver S).obj S :=
      Over.homMk (prod.lift (𝟙 S) (𝟙 S) : S ⟶ ((prodOver S).obj S).left)
        (by change prod.lift (𝟙 S) (𝟙 S) ≫ prod.snd = 𝟙 S; simp)
    let q : (overFiber F a).obj (Over.mk (𝟙 S)) := ⟨a, by simp⟩
    have hsub (u v : (overFiber F a).obj (Over.mk (𝟙 S))) : u = v := by
      have hu := u.2
      have hv := v.2
      simp only [Over.mk_left, Over.mk_hom, F.map_id, FintypeCat.id_apply] at hu hv
      exact Subtype.ext (hu.trans hv.symm)
    have hq : (overFiber F a).map δ q = e.inv.app S a := Subtype.ext (by
      rw [he']
      apply ext_map_fst_snd F
      · change F.map prod.fst (F.map (prod.lift (𝟙 S) (𝟙 S)) a) = _
        simp [← FintypeCat.comp_apply, ← F.map_comp]
      · change F.map prod.snd (F.map (prod.lift (𝟙 S) (𝟙 S)) a) = _
        simp [← FintypeCat.comp_apply, ← F.map_comp])
    have hfix : σ.hom.app _ ((overFiber F a).map δ q) = (overFiber F a).map δ q := by
      rw [FunctorToFintypeCat.naturality, hsub (σ.hom.app _ q) q]
    rw [← hq, hfix, hq]
    exact FintypeCat.inv_hom_id_apply (e.app S) a
  · intro τ (hτ : τ • a = a)
    have hY (Y : Over S) (y : (overFiber F a).obj Y) : F.map Y.hom (τ • y.1) = a := by
      rw [← mulAction_naturality, y.2, hτ]
    have hY' (Y : Over S) (y : (overFiber F a).obj Y) : F.map Y.hom (τ⁻¹ • y.1) = a := by
      rw [← mulAction_naturality, y.2]
      conv_lhs => rw [← hτ]
      exact inv_smul_smul τ a
    let σ : Aut (overFiber F a) := NatIso.ofComponents (fun Y ↦ FintypeCat.equivEquivIso
      { toFun := fun y ↦ ⟨τ • y.1, hY Y y⟩
        invFun := fun y ↦ ⟨τ⁻¹ • y.1, hY' Y y⟩
        left_inv := fun y ↦ Subtype.ext (inv_smul_smul τ y.1)
        right_inv := fun y ↦ Subtype.ext (smul_inv_smul τ y.1) }) fun {Y Y'} f ↦ by
      ext y
      exact Subtype.ext (mulAction_naturality F τ f.left y.1)
    refine ⟨σ, Aut.ext (NatTrans.ext (funext fun X ↦ ?_))⟩
    ext x
    rw [overFiberAutHom_apply]
    change F.map prod.fst (τ • (e.inv.app X x).1) = τ • x
    calc F.map prod.fst (τ • (e.inv.app X x).1)
        = τ • F.map (prod.fst : X ⨯ S ⟶ X) (e.inv.app X x).1 :=
          (mulAction_naturality F τ prod.fst _).symm
      _ = τ • x := by rw [he', fiberBinaryProductEquiv_symm_fst_apply]

end OverGalois

end SGA.SGA1.ExposeV
