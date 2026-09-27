/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.VariousExamples

/-!
# SGA 1, Exposé VI, VI.10 and VI.11 g): co-splittings

Following VI.10, a *co-cleavage* (resp. *co-splitting*) of `p : 𝒳 ⥤ E` is a cleavage (resp.
splitting) of `pᵒᵖ : 𝒳ᵒᵖ ⥤ Eᵒᵖ`: a choice of direct images `f_*` with cocartesian transports
`η ⟶ f_* η`. VI.11 g): `𝒞 × E` over `E` has, besides its canonical splitting
(`prodCleavage_isSplitting`), a canonical co-splitting, with transports `(𝟙, f) : (c, T) ⟶ (c, S)`;
it corresponds to the constant functor `E ⥤ Cat` with value `𝒞`. VI.11 a): the target functor
`Arrow E ⥤ E` has the co-splitting `f_* u = u ≫ f` (`arrowCoCleavage_isSplitting`).
-/

universe v u v₁ u₁

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

variable {C : Type u₁} [Category.{v₁} C] {E : Type u} [Category.{v} E]

/-- VI.11 g): the canonical co-cleavage of `𝒞 × E` over `E` (a cleavage of the opposite
projection), with transports `(𝟙, f)`. -/
noncomputable def prodCoCleavage : Cleavage (CategoryTheory.Prod.snd C E).op :=
  Cleavage.ofLifts (fun {R _} _ ξ ↦ ⟨op (ξ.val.unop.1, R.unop), rfl⟩)
    (fun {R _} f ξ ↦ (show ξ.val.unop ⟶ (ξ.val.unop.1, R.unop) from
      (𝟙 _, eqToHom (congrArg unop ξ.property) ≫ f.unop)).op)
    (fun {R S} f ξ ↦ by
      have : IsHomLift (CategoryTheory.Prod.snd C E) f.unop (show ξ.val.unop ⟶
          (ξ.val.unop.1, R.unop) from (𝟙 _, eqToHom (congrArg unop ξ.property) ≫ f.unop)) :=
        IsHomLift.of_fac' _ _ _ (congrArg unop ξ.property) rfl (by simp)
      have : IsIso (show ξ.val.unop ⟶ (ξ.val.unop.1, R.unop) from
          (𝟙 _, eqToHom (congrArg unop ξ.property) ≫ f.unop)).1 :=
        inferInstanceAs (IsIso (𝟙 _))
      exact (isCocartesian_iff_op f.unop _).mp (prod_isCocartesian_of_isIso f.unop _))

/-- VI.11 g): the canonical co-cleavage of `𝒞 × E` is a co-splitting. -/
theorem prodCoCleavage_isSplitting : (prodCoCleavage (C := C) (E := E)).IsSplitting := by
  refine ⟨fun S ξ ↦ ?_, fun {U T S} f g ξ ↦ ⟨rfl, ?_⟩⟩
  · obtain ⟨⟨⟨c, S'⟩⟩, h⟩ := ξ
    change op S' = S at h
    subst h
    refine ⟨rfl, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Prod.ext
    · rfl
    · change eqToHom rfl ≫ 𝟙 S' = 𝟙 S'
      simp
  · obtain ⟨⟨⟨c, S'⟩⟩, h⟩ := ξ
    change op S' = S at h
    subst h
    apply Quiver.Hom.unop_inj
    apply Prod.ext
    · change 𝟙 c ≫ 𝟙 c = 𝟙 c ≫ 𝟙 c
      rfl
    · change (eqToHom rfl ≫ f.unop) ≫ (eqToHom rfl ≫ g.unop) =
        (eqToHom rfl ≫ (g ≫ f).unop) ≫ (eqToHom rfl : (op (c, U.unop) : (C × E)ᵒᵖ) ⟶ _).unop.2
      simp

/-- VI.11 g): `𝒞 × E` is cofibered over `E`, as witnessed by its co-splitting (a cleavage of the
opposite projection makes it coprefibered). -/
theorem prod_isPreCofibered_of_coCleavage : IsPreCofibered (CategoryTheory.Prod.snd C E) :=
  (isPreCofibered_iff_op _).mpr prodCoCleavage.toIsPreFibered

/-! ### VI.11 a): the co-splitting of the category of arrows -/

section Arrows

variable (E)

theorem eq_comp_eqToHom_self {D : Type*} [Category D] {a b c : D} (x : a ⟶ b) (y : b ⟶ c)
    (h : c = c) : x ≫ y = x ≫ y ≫ eqToHom h := by
  simp

/-- VI.11 a): the transport `(𝟙, v) : u ⟶ u ≫ v` of the category of arrows, as a morphism from an
arbitrary arrow. -/
def arrowPushTransport (ξ : Arrow E) {S : E} (v : ξ.right ⟶ S) : ξ ⟶ Arrow.mk (ξ.hom ≫ v) :=
  Arrow.homMk (𝟙 ξ.left) v (by simp)

variable {E}

theorem arrowPushTransport_isCocartesian (ξ : Arrow E) {S : E} (v : ξ.right ⟶ S) :
    IsCocartesian (Arrow.rightFunc : Arrow E ⥤ E) v (arrowPushTransport E ξ v) :=
  arrow_isCocartesian_homMk ξ.hom v

/-- VI.11 a): the canonical co-cleavage of the target functor `Arrow E ⥤ E` (a cleavage of the
opposite functor): `f_* u = u ≫ f`, with transports `(𝟙, f)`. -/
noncomputable def arrowCoCleavage : Cleavage (Arrow.rightFunc : Arrow E ⥤ E).op :=
  Cleavage.ofLifts
    (fun {R _} f ξ ↦ ⟨op (Arrow.mk (ξ.val.unop.hom ≫ eqToHom (congrArg unop ξ.property) ≫ f.unop)),
      rfl⟩)
    (fun f ξ ↦ (arrowPushTransport E ξ.val.unop (eqToHom (congrArg unop ξ.property) ≫ f.unop)).op)
    (fun {R S} f ξ ↦ by
      have h := arrowPushTransport_isCocartesian ξ.val.unop
        (eqToHom (congrArg unop ξ.property) ≫ f.unop)
      have : IsHomLift (Arrow.rightFunc : Arrow E ⥤ E) f.unop
          (arrowPushTransport E ξ.val.unop (eqToHom (congrArg unop ξ.property) ≫ f.unop)) :=
        IsHomLift.of_fac' _ _ _ (congrArg unop ξ.property) rfl (by
          change eqToHom _ ≫ f.unop = _
          exact eq_comp_eqToHom_self _ _ _)
      have h' := isCocartesian_of_isCocartesian_map _ f.unop _
        (isCocartesian_map_of_isCocartesian _ _ _ h)
      exact (isCocartesian_iff_op f.unop _).mp h')

/-- VI.11 a): the canonical co-cleavage of `Arrow E` is a co-splitting: `(𝟙_S)_* = 𝟭` and
`(gf)_* = g_* f_*` (up to the associativity of composition in `E`). -/
theorem arrowCoCleavage_isSplitting : (arrowCoCleavage (E := E)).IsSplitting := by
  refine ⟨fun S ξ ↦ ?_, fun {U T S} f g ξ ↦ ?_⟩
  · obtain ⟨⟨⟨l, r, u⟩⟩, h⟩ := ξ
    change op r = S at h
    subst h
    have ho : Arrow.mk (u ≫ eqToHom rfl ≫ (𝟙 (op r)).unop) = ⟨l, r, u⟩ := by
      simp
      rfl
    refine ⟨congrArg op ho, ?_⟩
    apply Quiver.Hom.unop_inj
    refine Arrow.hom_ext _ _ ?_ ?_
    · erw [eqToHom_unop, Arrow.eqToHom_left]
      rfl
    · erw [eqToHom_unop, Arrow.eqToHom_right]
      change eqToHom rfl ≫ 𝟙 r = _
      simp only [eqToHom_refl, Category.comp_id]
      rfl
  · obtain ⟨⟨⟨l, r, u⟩⟩, h⟩ := ξ
    change op r = S at h
    subst h
    have ho : Arrow.mk ((u ≫ eqToHom rfl ≫ f.unop) ≫ eqToHom rfl ≫ g.unop) =
        Arrow.mk (u ≫ eqToHom rfl ≫ (g ≫ f).unop) := by
      simp
    refine ⟨congrArg op ho, ?_⟩
    apply Quiver.Hom.unop_inj
    rw [unop_comp, unop_comp]
    refine Arrow.hom_ext _ _ ?_ ?_
    · erw [Arrow.comp_left, Arrow.comp_left, eqToHom_unop, Arrow.eqToHom_left]
      change 𝟙 l ≫ 𝟙 l = 𝟙 l ≫ eqToHom rfl
      simp
    · erw [Arrow.comp_right, Arrow.comp_right, eqToHom_unop, Arrow.eqToHom_right]
      change (eqToHom rfl ≫ f.unop) ≫ (eqToHom rfl ≫ g.unop) =
        (eqToHom rfl ≫ (g ≫ f).unop) ≫ eqToHom rfl
      simp

end Arrows

end SGA.SGA1.ExposeVI
