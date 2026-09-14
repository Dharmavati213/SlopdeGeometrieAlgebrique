/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# SGA 2, Exposé II, Lemma 9: comparison by dimension shifting

The two exactness conditions at a connecting morphism suffice to propagate
a degree-zero comparison isomorphism to every degree, provided both families
vanish in positive degrees on injective objects. This is the general
homological argument in II.9(b) ⇒ (a); applications must supply their actual
connecting maps and prove compatibility of the comparison with them.
-/

noncomputable section

universe u v u' v'

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII

variable (C : Type u) [Category.{v} C] [Abelian C]
  (D : Type u') [Category.{v'} D] [Abelian D]

/-- The portion of a cohomological sequence used in dimension shifting.
No universality or comparison isomorphism is part of this data. -/
structure ConnectingSequence where
  /-- The functor in each nonnegative degree. -/
  obj : ℕ → C ⥤ D
  /-- The boundary of a short exact sequence. -/
  δ (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    (obj n).obj S.X₃ ⟶ (obj (n + 1)).obj S.X₁
  /-- The preceding map followed by the boundary is zero. -/
  map_δ (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    (obj n).map S.g ≫ δ S hS n = 0
  /-- The boundary followed by the next map is zero. -/
  δ_map (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    δ S hS n ≫ (obj (n + 1)).map S.f = 0
  /-- Exactness immediately before the boundary. -/
  exact_left (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((obj n).map S.g) (δ S hS n) (map_δ S hS n)).Exact
  /-- Exactness immediately after the boundary. -/
  exact_right (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (δ S hS n) ((obj (n + 1)).map S.f) (δ_map S hS n)).Exact

namespace ConnectingSequence

variable {C D}

/-- A degreewise natural comparison that commutes with the boundaries. -/
structure Hom (F G : ConnectingSequence C D) where
  /-- The natural transformation in each degree. -/
  app : ∀ n, F.obj n ⟶ G.obj n
  /-- Compatibility with the connecting morphisms. -/
  comm (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    F.δ S hS n ≫ (app (n + 1)).app S.X₁ =
      (app n).app S.X₃ ≫ G.δ S hS n

/-- Positive-degree vanishing on injectives. -/
def VanishesOnInjectives (F : ConnectingSequence C D) : Prop :=
  ∀ (I : C) [Injective I] (n : ℕ), IsZero ((F.obj (n + 1)).obj I)

set_option backward.isDefEq.respectTransparency false in
/-- II.9's dimension-shifting argument: a comparison between cohomological
sequences vanishing on injectives is an isomorphism in every degree as soon
as it is an isomorphism in degree zero. -/
theorem Hom.isIso_of_degree_zero [EnoughInjectives C]
    {F G : ConnectingSequence C D} (φ : Hom F G)
    (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    (hzero : ∀ X, IsIso ((φ.app 0).app X)) (n : ℕ) (X : C) :
    IsIso ((φ.app n).app X) := by
  induction n generalizing X with
  | zero => exact hzero X
  | succ n ih =>
    let S := ShortComplex.cokernelSequence (Injective.ι X)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := by change Mono (Injective.ι X); infer_instance
        epi_g := by change Epi (cokernel.π (Injective.ι X)); infer_instance }
    have hδF : Epi (F.δ S hS n) := by
      have hz : (F.obj (n + 1)).map S.f = 0 :=
        (hF (Injective.under X) n).eq_of_tgt _ _
      exact (ShortComplex.exact_iff_epi _ hz).mp (F.exact_right S hS n)
    have hδG : Epi (G.δ S hS n) := by
      have hz : (G.obj (n + 1)).map S.f = 0 :=
        (hG (Injective.under X) n).eq_of_tgt _ _
      exact (ShortComplex.exact_iff_epi _ hz).mp (G.exact_right S hS n)
    let ψ : ComposableArrows.mk₂ ((F.obj n).map S.g) (F.δ S hS n) ⟶
        ComposableArrows.mk₂ ((G.obj n).map S.g) (G.δ S hS n) :=
      ComposableArrows.homMk₂ ((φ.app n).app S.X₂) ((φ.app n).app S.X₃)
        ((φ.app (n + 1)).app S.X₁) ((φ.app n).naturality S.g) (φ.comm S hS n)
    have := ih S.X₂
    have := ih S.X₃
    exact Abelian.isIso_of_epi_of_isIso ψ
      (F.exact_left S hS n).exact_toComposableArrows
      (G.exact_left S hS n).exact_toComposableArrows
      hδF hδG (show Epi ((φ.app n).app S.X₂) from inferInstance)
        (show IsIso ((φ.app n).app S.X₃) from inferInstance)

end ConnectingSequence

end SGA.SGA2.ExposeII
