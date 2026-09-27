/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# Limits of towers of categories

A *tower* of categories is a sequence of functors `⋯ ⥤ C 2 ⥤ C 1 ⥤ C 0`. Its (pseudo-)limit
`TowerLimit F` has as objects the compatible systems `(Xₙ, Fₙ(Xₙ₊₁) ≅ Xₙ)` and as morphisms the
compatible families of morphisms. This is how objects over a formal scheme `𝔛 = lim→ Xₙ` are
described by compatible objects over the `Xₙ` (EGA I, §10.6; SGA 1 I.8.4, where the coverings of
a formal scheme are described through the sheaves of algebras `ℬₙ` on the `Xₙ`).

If every functor in the tower is an equivalence, the projection `TowerLimit F ⥤ C 0` is an
equivalence (`TowerLimit.isEquivalence_π_zero`): this is the formal part of SGA 1 I.8.4, the
geometric input being I.8.3 (each `Fₙ` is an equivalence).
-/

universe v u

namespace CategoryTheory

variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)] (F : ∀ n, C (n + 1) ⥤ C n)

/-- An object of the limit of the tower `⋯ ⥤ C 2 ⥤ C 1 ⥤ C 0`: objects `Xₙ` of the `C n` with
isomorphisms `Fₙ(Xₙ₊₁) ≅ Xₙ`. -/
structure TowerLimit where
  /-- The component in `C n`. -/
  obj (n : ℕ) : C n
  /-- The compatibility isomorphisms. -/
  iso (n : ℕ) : (F n).obj (obj (n + 1)) ≅ obj n

namespace TowerLimit

variable {F}

/-- Morphisms of compatible systems. -/
@[ext]
structure Hom (X Y : TowerLimit F) where
  /-- The component in `C n`. -/
  app (n : ℕ) : X.obj n ⟶ Y.obj n
  comm (n : ℕ) : (F n).map (app (n + 1)) ≫ (Y.iso n).hom = (X.iso n).hom ≫ app n

attribute [reassoc] Hom.comm

instance : Category (TowerLimit F) where
  Hom := Hom
  id X := ⟨fun _ ↦ 𝟙 _, fun n ↦ by simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, fun n ↦ by
    rw [Functor.map_comp, Category.assoc, g.comm, f.comm_assoc]⟩

@[ext]
lemma hom_ext {X Y : TowerLimit F} {f g : X ⟶ Y} (h : ∀ n, f.app n = g.app n) : f = g :=
  Hom.ext (funext h)

@[simp]
lemma id_app (X : TowerLimit F) (n : ℕ) : Hom.app (𝟙 X) n = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_app {X Y Z : TowerLimit F} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Hom.app (f ≫ g) n = f.app n ≫ g.app n := rfl

variable (F) in
/-- The projection to the `n`-th category of the tower. -/
@[simps]
def π (n : ℕ) : TowerLimit F ⥤ C n where
  obj X := X.obj n
  map f := f.app n

lemma map_app_succ {X Y : TowerLimit F} (f : X ⟶ Y) (n : ℕ) :
    (F n).map (f.app (n + 1)) = (X.iso n).hom ≫ f.app n ≫ (Y.iso n).inv := by
  rw [← f.comm_assoc, Iso.hom_inv_id, Category.comp_id]

variable [∀ n, (F n).IsEquivalence]

/-- A compatible system is determined by its first term when the tower consists of
equivalences: the system `n ↦ F₀⁻¹ ⋯ Fₙ₋₁⁻¹ X₀`. -/
noncomputable def ofZero (X₀ : C 0) : TowerLimit F where
  obj n := Nat.rec (motive := fun n ↦ C n) X₀ (fun n Xn ↦ (F n).objPreimage Xn) n
  iso n := (F n).objObjPreimageIso _

/-- Lift of a morphism at level `0` to a morphism of compatible systems. -/
noncomputable def liftApp {X Y : TowerLimit F} (φ : X.obj 0 ⟶ Y.obj 0) :
    ∀ n, X.obj n ⟶ Y.obj n
  | 0 => φ
  | n + 1 => (F n).preimage ((X.iso n).hom ≫ liftApp φ n ≫ (Y.iso n).inv)

/-- The projection of the limit of a tower of equivalences to its first category is an
equivalence (SGA 1 I.8.4, formal part). -/
instance isEquivalence_π_zero : (π F 0).IsEquivalence where
  faithful := ⟨fun {X Y} f g h ↦ by
    ext n
    induction n with
    | zero => exact h
    | succ n ih =>
      apply (F n).map_injective
      rw [map_app_succ, map_app_succ, ih]⟩
  full := ⟨fun {X Y} φ ↦ ⟨⟨liftApp φ, fun n ↦ by
    simp only [liftApp, Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩,
    rfl⟩⟩
  essSurj := ⟨fun X₀ ↦ ⟨ofZero X₀, ⟨Iso.refl _⟩⟩⟩

end TowerLimit

end CategoryTheory
